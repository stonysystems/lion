// Lion-based async I/O layer for IronFleet IronRSL (Multi-Paxos).
//
// This is a Rust `cdylib` loaded into the C# (Dafny-generated) IronRSL process via
// P/Invoke, replacing the C# IoScheduler. The C# Paxos core is unchanged: its main
// loop calls `lion_io_receive` / `lion_io_send` synchronously across the FFI
// boundary.
//
// Architecture: a single background OS thread owns a Lion current-thread runtime;
// all network I/O — the accept loop, per-connection reader/writer tasks, and peer
// dialing — runs as lightweight async tasks on that runtime (lion::net + lion::spawn
// + lion::time, reading/writing via tokio's AsyncRead/Write ext traits, which Lion's
// TcpStream halves implement). The C# thread and the Lion runtime thread exchange
// packets over thread-safe flume channels: inbound packets are pushed by reader
// tasks and drained by `lion_io_receive`; outbound messages are pushed by
// `lion_io_send` and drained by writer tasks. Per-connection threads (the old
// design) are thus collapsed into one runtime thread driving many async tasks.
//
// Wire protocol: [8-byte BE length][message bytes].
// Handshake: the initiator sends [8-byte BE key_length][public_key_bytes]; the
// acceptor reads it and derives the peer's key hash (SHA-256).

use std::collections::{HashMap, HashSet};
use std::net::SocketAddr;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::time::Duration;

use lion::net::{TcpListener, TcpStream};
use sha2::{Digest, Sha256};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

const IDLE_SPINS: u32 = 64;
const IDLE_BLOCK_MS: u64 = 50;

struct Packet {
    sender_key_hash: Vec<u8>,
    message: Vec<u8>,
}

enum Command {
    Dial {
        key_hash: Vec<u8>,
        addr: SocketAddr,
        msg: Vec<u8>,
    },
    Shutdown,
}

// Shared between the C# thread (receive/send) and the Lion runtime thread (I/O tasks).
struct IoState {
    inbound_tx: flume::Sender<Packet>,
    inbound_rx: flume::Receiver<Packet>,
    outbound_writers: Mutex<HashMap<Vec<u8>, flume::Sender<Vec<u8>>>>,
    dialing: Mutex<HashSet<Vec<u8>>>,
    my_public_key: Vec<u8>,
    my_public_key_hash: Vec<u8>,
    known_peers: HashMap<Vec<u8>, SocketAddr>,
    listener_addr: SocketAddr,
    idle_count: AtomicU32,
}

pub struct LionIo {
    state: Arc<IoState>,
    cmd_tx: flume::Sender<Command>,
    runtime_thread: Option<JoinHandle<()>>,
}

fn sha256_hash(data: &[u8]) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().to_vec()
}

// ── async wire helpers (generic over the AsyncRead/Write halves) ───────────────

async fn read_be_u64<R: AsyncReadExt + Unpin>(r: &mut R) -> std::io::Result<u64> {
    let mut buf = [0u8; 8];
    r.read_exact(&mut buf).await?;
    Ok(u64::from_be_bytes(buf))
}

async fn read_message<R: AsyncReadExt + Unpin>(r: &mut R) -> std::io::Result<Vec<u8>> {
    let len = read_be_u64(r).await? as usize;
    let mut buf = vec![0u8; len];
    r.read_exact(&mut buf).await?;
    Ok(buf)
}

async fn write_message<W: AsyncWriteExt + Unpin>(w: &mut W, data: &[u8]) -> std::io::Result<()> {
    w.write_all(&(data.len() as u64).to_be_bytes()).await?;
    w.write_all(data).await
}

// ── Lion runtime: supervisor + I/O tasks ──────────────────────────────────────

// Drives all network I/O. Returns (ending block_on, stopping the runtime thread)
// only when a Shutdown command arrives.
async fn supervisor(state: Arc<IoState>, cmd_rx: flume::Receiver<Command>) {
    {
        let s = state.clone();
        lion::spawn(async move { listener_task(s).await });
    }
    // Dial every known peer (except self), retrying until connected.
    let peers: Vec<(Vec<u8>, SocketAddr)> = state
        .known_peers
        .iter()
        .filter(|(kh, _)| *kh != &state.my_public_key_hash)
        .map(|(kh, addr)| (kh.clone(), *addr))
        .collect();
    for (kh, addr) in peers {
        let s = state.clone();
        lion::spawn(async move { connect_task(s, kh, addr, None).await });
    }
    // On-demand dials (for connections not known at startup) + shutdown.
    while let Ok(cmd) = cmd_rx.recv_async().await {
        match cmd {
            Command::Dial { key_hash, addr, msg } => {
                let s = state.clone();
                lion::spawn(async move { connect_task(s, key_hash, addr, Some(msg)).await });
            }
            Command::Shutdown => break,
        }
    }
}

async fn listener_task(state: Arc<IoState>) {
    let listener = match TcpListener::bind(state.listener_addr).await {
        Ok(l) => l,
        Err(_) => return,
    };
    loop {
        match listener.accept().await {
            Ok((stream, _)) => {
                let s = state.clone();
                lion::spawn(async move { accept_conn(s, stream).await });
            }
            Err(_) => break,
        }
    }
}

async fn accept_conn(state: Arc<IoState>, mut stream: TcpStream) {
    let _ = stream.set_nodelay(true);
    // Handshake: read the initiator's public key, derive its hash.
    let key = match read_message(&mut stream).await {
        Ok(k) => k,
        Err(_) => return,
    };
    let remote_hash = sha256_hash(&key);
    spawn_conn(state, stream, remote_hash, None);
}

async fn connect_task(state: Arc<IoState>, key_hash: Vec<u8>, addr: SocketAddr, first: Option<Vec<u8>>) {
    loop {
        match TcpStream::connect(addr).await {
            Ok(mut stream) => {
                let _ = stream.set_nodelay(true);
                // Handshake: announce our public key.
                if write_message(&mut stream, &state.my_public_key).await.is_err() {
                    lion::time::sleep(Duration::from_millis(100)).await;
                    continue;
                }
                spawn_conn(state.clone(), stream, key_hash.clone(), first);
                state.dialing.lock().unwrap().remove(&key_hash);
                return;
            }
            Err(_) => lion::time::sleep(Duration::from_millis(100)).await,
        }
    }
}

// Split a connected stream and spawn its reader + writer tasks. Must be called from
// within the Lion runtime (it uses lion::spawn).
fn spawn_conn(state: Arc<IoState>, stream: TcpStream, hash: Vec<u8>, first: Option<Vec<u8>>) {
    let (mut read_half, mut write_half) = stream.into_split();

    // Reader: stream inbound messages into the shared inbound channel.
    let inbound_tx = state.inbound_tx.clone();
    let reader_hash = hash.clone();
    lion::spawn(async move {
        loop {
            match read_message(&mut read_half).await {
                Ok(msg) => {
                    let _ = inbound_tx.send(Packet {
                        sender_key_hash: reader_hash.clone(),
                        message: msg,
                    });
                }
                Err(_) => break,
            }
        }
    });

    // Writer: drain the per-connection outbound channel onto the socket.
    let (wtx, wrx) = flume::unbounded::<Vec<u8>>();
    if let Some(m) = first {
        let _ = wtx.send(m);
    }
    state.outbound_writers.lock().unwrap().insert(hash, wtx);
    lion::spawn(async move {
        while let Ok(msg) = wrx.recv_async().await {
            if write_message(&mut write_half, &msg).await.is_err() {
                break;
            }
        }
    });
}

// ── C#-thread-side operations (called synchronously over FFI) ──────────────────

impl LionIo {
    fn new_and_start(
        bind_addr: SocketAddr,
        my_public_key: Vec<u8>,
        known_peers: HashMap<Vec<u8>, SocketAddr>,
    ) -> LionIo {
        let (inbound_tx, inbound_rx) = flume::unbounded();
        let my_public_key_hash = sha256_hash(&my_public_key);
        let state = Arc::new(IoState {
            inbound_tx,
            inbound_rx,
            outbound_writers: Mutex::new(HashMap::new()),
            dialing: Mutex::new(HashSet::new()),
            my_public_key,
            my_public_key_hash,
            known_peers,
            listener_addr: bind_addr,
            idle_count: AtomicU32::new(0),
        });
        let (cmd_tx, cmd_rx) = flume::unbounded();
        let st = state.clone();
        let runtime_thread = std::thread::spawn(move || {
            let rt = lion::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .expect("failed to build Lion runtime");
            rt.block_on(supervisor(st, cmd_rx));
        });
        LionIo { state, cmd_tx, runtime_thread: Some(runtime_thread) }
    }

    // Called from the C# Paxos loop. Mirrors the idle-aware policy: a non-blocking
    // probe, then a short spin, then (after IDLE_SPINS empty polls) a bounded block
    // that frees the CPU when idle.
    fn receive(&self, time_limit_ms: i32) -> Result<Packet, bool> {
        let st = &self.state;
        if time_limit_ms == 0 {
            if let Ok(pkt) = st.inbound_rx.try_recv() {
                st.idle_count.store(0, Ordering::Relaxed);
                return Ok(pkt);
            }
            let idle = st.idle_count.fetch_add(1, Ordering::Relaxed);
            if idle < IDLE_SPINS {
                std::thread::yield_now();
                Err(true)
            } else {
                match st.inbound_rx.recv_timeout(Duration::from_millis(IDLE_BLOCK_MS)) {
                    Ok(pkt) => {
                        st.idle_count.store(0, Ordering::Relaxed);
                        Ok(pkt)
                    }
                    Err(_) => Err(true),
                }
            }
        } else {
            st.inbound_rx
                .recv_timeout(Duration::from_millis(time_limit_ms as u64))
                .map_err(|_| true)
        }
    }

    fn send(&self, remote_key_hash: &[u8], message: &[u8]) -> bool {
        let st = &self.state;
        // Self-send shortcut.
        if remote_key_hash == st.my_public_key_hash.as_slice() {
            let _ = st.inbound_tx.send(Packet {
                sender_key_hash: st.my_public_key_hash.clone(),
                message: message.to_vec(),
            });
            return true;
        }
        {
            let writers = st.outbound_writers.lock().unwrap();
            if let Some(tx) = writers.get(remote_key_hash) {
                return tx.send(message.to_vec()).is_ok();
            }
        }
        // No writer yet: ask the runtime to dial this known peer. The first send
        // carries its message in the Dial command; sends arriving while the dial is
        // in flight are dropped (Paxos retransmits).
        if let Some(addr) = st.known_peers.get(remote_key_hash) {
            let mut dialing = st.dialing.lock().unwrap();
            if dialing.insert(remote_key_hash.to_vec()) {
                let _ = self.cmd_tx.send(Command::Dial {
                    key_hash: remote_key_hash.to_vec(),
                    addr: *addr,
                    msg: message.to_vec(),
                });
            }
            true
        } else {
            false
        }
    }
}

// ============================================================
// FFI
// ============================================================

#[repr(C)]
pub struct FfiIdentity {
    pub public_key: *const u8,
    pub public_key_len: u32,
    pub host: *const u8,
    pub host_len: u32,
    pub port: u16,
}

#[no_mangle]
pub extern "C" fn lion_io_create(
    bind_host: *const u8,
    bind_host_len: u32,
    bind_port: u16,
    my_public_key: *const u8,
    my_public_key_len: u32,
    known: *const FfiIdentity,
    known_count: u32,
) -> *mut LionIo {
    let bind_host_str = unsafe {
        std::str::from_utf8(std::slice::from_raw_parts(bind_host, bind_host_len as usize)).unwrap()
    };
    let bind_addr: SocketAddr = format!("{}:{}", bind_host_str, bind_port).parse().unwrap();

    let my_pk =
        unsafe { std::slice::from_raw_parts(my_public_key, my_public_key_len as usize).to_vec() };

    let mut known_peers = HashMap::new();
    for i in 0..known_count as usize {
        let id = unsafe { &*known.add(i) };
        let pk = unsafe { std::slice::from_raw_parts(id.public_key, id.public_key_len as usize) };
        let host = unsafe {
            std::str::from_utf8(std::slice::from_raw_parts(id.host, id.host_len as usize)).unwrap()
        };
        let addr: SocketAddr = format!("{}:{}", host, id.port).parse().unwrap();
        known_peers.insert(sha256_hash(pk), addr);
    }

    let io = LionIo::new_and_start(bind_addr, my_pk, known_peers);
    Box::into_raw(Box::new(io))
}

#[no_mangle]
pub extern "C" fn lion_io_destroy(handle: *mut LionIo) {
    if !handle.is_null() {
        let mut io = unsafe { Box::from_raw(handle) };
        let _ = io.cmd_tx.send(Command::Shutdown);
        if let Some(t) = io.runtime_thread.take() {
            let _ = t.join();
        }
    }
}

#[no_mangle]
pub extern "C" fn lion_io_my_key_hash(
    handle: *const LionIo,
    out_hash: *mut *const u8,
    out_hash_len: *mut u32,
) {
    let io = unsafe { &*handle };
    unsafe {
        *out_hash = io.state.my_public_key_hash.as_ptr();
        *out_hash_len = io.state.my_public_key_hash.len() as u32;
    }
}

#[no_mangle]
pub extern "C" fn lion_io_receive(
    handle: *const LionIo,
    time_limit_ms: i32,
    out_ok: *mut u8,
    out_timed_out: *mut u8,
    out_remote: *mut *mut u8,
    out_remote_len: *mut u32,
    out_msg: *mut *mut u8,
    out_msg_len: *mut u32,
) {
    let io = unsafe { &*handle };
    match io.receive(time_limit_ms) {
        Ok(pkt) => {
            let remote = pkt.sender_key_hash.into_boxed_slice();
            let msg = pkt.message.into_boxed_slice();
            unsafe {
                *out_ok = 1;
                *out_timed_out = 0;
                *out_remote_len = remote.len() as u32;
                *out_remote = Box::into_raw(remote) as *mut u8;
                *out_msg_len = msg.len() as u32;
                *out_msg = Box::into_raw(msg) as *mut u8;
            }
        }
        Err(_) => unsafe {
            *out_ok = 1;
            *out_timed_out = 1;
            *out_remote = std::ptr::null_mut();
            *out_remote_len = 0;
            *out_msg = std::ptr::null_mut();
            *out_msg_len = 0;
        },
    }
}

#[no_mangle]
pub extern "C" fn lion_io_send(
    handle: *const LionIo,
    remote_key_hash: *const u8,
    remote_key_hash_len: u32,
    message: *const u8,
    message_len: u32,
) -> u8 {
    let io = unsafe { &*handle };
    let rkh = unsafe { std::slice::from_raw_parts(remote_key_hash, remote_key_hash_len as usize) };
    let msg = unsafe { std::slice::from_raw_parts(message, message_len as usize) };
    if io.send(rkh, msg) {
        1
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn lion_io_free_buffer(ptr: *mut u8, len: u32) {
    if !ptr.is_null() {
        unsafe {
            let _ = Box::from_raw(std::slice::from_raw_parts_mut(ptr, len as usize));
        }
    }
}
