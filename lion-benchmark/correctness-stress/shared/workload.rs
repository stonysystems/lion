// Async-runtime liveness stress test — the single shared kernel.
//
// This one source is compiled unchanged against every runtime under test. Each
// per-runtime crate renames its runtime dependency to `rt` in Cargo.toml
// (`rt = { package = "tokio", version = "=1.21.0" }`, or `package = "lion"`) and
// its `main.rs` is nothing but `#[path = ".../workload.rs"] mod workload; fn
// main() { workload::run() }`. The ONLY difference between runtimes is the
// peripheral configuration — which runtime `rt` resolves to. This is possible
// because Lion mirrors Tokio's public API (`rt::spawn`, `rt::time::*`,
// `rt::task::{yield_now, LocalSet, block_in_place}`, `rt::net::*`, `rt::io::*`,
// `rt::runtime::Builder`).
//
// The test models a small server pushed hard for a fixed duration, with a steady
// mix of the workloads a real async service handles concurrently: deadline-guarded
// requests, cooperative compute, scatter/gather fan-out, a periodic heartbeat, and
// network I/O. Each runs as a loop until a shared deadline, so every workload
// stays active for the whole run.
//
// The same workload is run in the two standard runtime configurations a server is
// deployed in, selected by argv[1]:
//   "current"  current-thread runtime; startup uses a LocalSet to initialize
//              not-Send tasks (the idiomatic single-thread setup pattern).
//   "multi"    multi-thread runtime; a worker offloads a blocking job with
//              block_in_place, bridging back to async to process it in chunks
//              (the idiomatic multi-thread blocking pattern; block_in_place is
//              not valid on a current-thread runtime).
// Each config exercises the spawn/wake and blocking-offload paths the way code
// written for that config actually does.
//
// Success criterion: a runtime that keeps every task scheduled drives the whole
// mix to the deadline and the process exits in a few seconds. If any task is left
// unfinished, the process never exits, which the harness records as a hang (see
// run.sh). The heatmap (plot.py) is taken from the "current" run.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use rt::task::LocalSet;
use rt::io::{AsyncReadExt, AsyncWriteExt};

// How long the run lasts.
const RUN_SECS: u64 = 3;

static EVENT_ID: AtomicU64 = AtomicU64::new(0);

struct Logger {
  start: Instant,
}

impl Logger {
  fn new() -> Self {
    Self { start: Instant::now() }
  }
  fn log(&self, phase: &str, event: &str, task_id: u64) {
    let ts = self.start.elapsed().as_micros();
    println!("{ts}\t{phase}\t{event}\t{task_id}");
  }
}

fn next_id() -> u64 {
  EVENT_ID.fetch_add(1, Ordering::Relaxed)
}

// Deadline-guarded requests.
//
// A connection that keeps serving requests until the run ends. Each request runs
// a short async operation under a timeout, the way a service bounds the latency of
// a downstream call; the operation finishes well within the deadline, so each
// request registers a timeout and then completes normally.
async fn task_request_loop(logger: Arc<Logger>, deadline: Instant) {
  let id = next_id();
  logger.log("lifecycle", "spawn", id);
  let mut n = 0u64;
  while Instant::now() < deadline {
    // Backstop timeout deliberately BELOW the harness window (5 s < 15 s): the
    // whole workload's worst honest critical path stays bounded by
    // RUN_SECS + 5 s, so a harness timeout can only mean a permanent stall.
    let _ = rt::time::timeout(Duration::from_secs(5), async {
      rt::time::sleep(Duration::from_millis(1)).await;
    })
    .await;
    n += 1;
    if n % 50 == 0 {
      logger.log("timer", "op", id);
    }
  }
  logger.log("lifecycle", "done", id);
}

// Cooperative compute.
//
// Background compute that runs until the run ends, yielding between work units so
// it does not monopolise the scheduler and pausing briefly between rounds — the
// recommended way to keep long-running work fair to other tasks on a cooperative
// runtime.
async fn task_compute_loop(logger: Arc<Logger>, deadline: Instant) {
  let id = next_id();
  logger.log("lifecycle", "spawn", id);
  let mut acc: u64 = 0;
  let mut i: u64 = 0;
  while Instant::now() < deadline {
    acc = acc.wrapping_add(i);
    i += 1;
    rt::task::yield_now().await;
    rt::time::sleep(Duration::from_millis(3)).await;
    if i % 30 == 0 {
      logger.log("coop", "yield", id);
    }
  }
  std::hint::black_box(acc);
  logger.log("lifecycle", "done", id);
}

// Scatter / gather fan-out.
//
// A coordinator that keeps issuing scatter/gather rounds until the run ends: each
// round spawns a wave of sub-workers, every one does a little async work, and the
// results are gathered before the next round.
async fn task_fanout_loop(logger: Arc<Logger>, deadline: Instant) {
  let id = next_id();
  logger.log("lifecycle", "spawn", id);
  while Instant::now() < deadline {
    let mut gs = Vec::new();
    for _ in 0..10 {
      let l = logger.clone();
      gs.push(rt::spawn(async move {
        rt::task::yield_now().await;
        rt::time::sleep(Duration::from_millis(5)).await;
        let _ = &l;
      }));
    }
    for g in gs {
      g.await.unwrap();
    }
    // a wave of child tasks spawned and joined this round
    logger.log("lifecycle", "wave", id);
  }
  logger.log("lifecycle", "done", id);
}

// Periodic heartbeat.
//
// A health-check loop that ticks on a fixed interval for the whole run, like the
// keepalive / liveness probe every server carries. It runs concurrently with
// everything else.
async fn task_heartbeat_loop(logger: Arc<Logger>, deadline: Instant) {
  let id = next_id();
  logger.log("heartbeat", "spawn", id);
  while Instant::now() < deadline {
    rt::time::sleep(Duration::from_millis(50)).await;
    logger.log("heartbeat", "tick", next_id());
  }
  logger.log("heartbeat", "done", id);
}

// Network echo.
//
// A real TCP echo server with waves of clients that connect, send, and await the
// reply, paced so client traffic arrives across the whole run as it would for a
// live server.
async fn echo_loop(logger: Arc<Logger>, deadline: Instant, clients: usize) {
  let id = next_id();
  logger.log("network", "open", id);
  let listener = rt::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
  let addr = listener.local_addr().unwrap();

  let server = rt::spawn(async move {
    loop {
      let (mut stream, _) = match listener.accept().await {
        Ok(s) => s,
        Err(_) => break,
      };
      rt::spawn(async move {
        let mut buf = [0u8; 64];
        loop {
          match stream.read(&mut buf).await {
            Ok(0) => break,
            Ok(n) => {
              if stream.write_all(&buf[..n]).await.is_err() {
                break;
              }
            }
            Err(_) => break,
          }
        }
      });
    }
  });

  while Instant::now() < deadline {
    let mut hs = Vec::new();
    for _ in 0..clients {
      let lg = logger.clone();
      hs.push(rt::spawn(async move {
        let cid = next_id();
        lg.log("network", "connect", cid);
        let mut stream = rt::net::TcpStream::connect(addr).await.unwrap();
        let msg = b"ping";
        stream.write_all(msg).await.unwrap();
        let mut buf = [0u8; 4];
        stream.read_exact(&mut buf).await.unwrap();
        assert_eq!(&buf, msg);
        lg.log("network", "reply", cid);
      }));
    }
    for h in hs {
      h.await.unwrap();
    }
    rt::time::sleep(Duration::from_millis(60)).await;
  }
  server.abort();
  logger.log("network", "close", id);
}

// Offloaded blocking job (multi-thread configuration only).
//
// On a multi-threaded runtime, a worker periodically offloads a blocking job with
// block_in_place (the idiomatic way to run a blocking section without starving the
// worker pool). The job is a sync routine that bridges back into async — via the
// runtime handle — to process its input in many small chunks, yielding between
// chunks so the bridged work stays cooperative. Jobs are paced, as a server would
// issue them between other work.
async fn offload_loop(logger: Arc<Logger>, deadline: Instant) {
  let id = next_id();
  logger.log("offload", "spawn", id);
  while Instant::now() < deadline {
    let jid = next_id();
    logger.log("offload", "job", jid);
    rt::task::block_in_place(|| {
      rt::runtime::Handle::current().block_on(async {
        let mut acc: u64 = 0;
        for chunk in 0..256u64 {
          acc = acc.wrapping_add(chunk);
          rt::task::yield_now().await;
        }
        std::hint::black_box(acc);
      })
    });
    logger.log("offload", "ack", jid);
    rt::time::sleep(Duration::from_millis(150)).await;
  }
  logger.log("offload", "done", id);
}

// Startup initialization (current-thread configuration only).
//
// Before serving, the server initializes a batch of tasks on a LocalSet — the
// idiomatic place for setup work that need not be Send (config loading, cache
// warming, local handles) — entering the LocalSet for the startup scope and
// waiting for every init task before it begins serving.
fn startup_init(logger: &Arc<Logger>) {
  let runtime = rt::runtime::Builder::new_current_thread()
    .enable_all()
    .build()
    .unwrap();
  let local = LocalSet::new();
  let _guard = local.enter();
  let lg = logger.clone();
  local.block_on(&runtime, async move {
    let mut handles = Vec::new();
    for _ in 0..50 {
      let l = lg.clone();
      handles.push(rt::task::spawn_local(async move {
        rt::time::sleep(Duration::ZERO).await;
        let _ = &l;
      }));
    }
    for h in handles {
      h.await.unwrap();
    }
  });
}

// The steady concurrent mix, spawned into whichever runtime is block_on'ing it.
// `with_offload` adds the multi-thread blocking-offload worker.
async fn general_workload(logger: Arc<Logger>, deadline: Instant, with_offload: bool) {
  let mut handles = Vec::new();
  for _ in 0..200 {
    let l = logger.clone();
    handles.push(rt::spawn(async move { task_request_loop(l, deadline).await }));
  }
  for _ in 0..50 {
    let l = logger.clone();
    handles.push(rt::spawn(async move { task_compute_loop(l, deadline).await }));
  }
  for _ in 0..10 {
    let l = logger.clone();
    handles.push(rt::spawn(async move { task_fanout_loop(l, deadline).await }));
  }
  let l = logger.clone();
  handles.push(rt::spawn(async move { task_heartbeat_loop(l, deadline).await }));
  let l = logger.clone();
  handles.push(rt::spawn(async move { echo_loop(l, deadline, 15).await }));
  if with_offload {
    let l = logger.clone();
    handles.push(rt::spawn(async move { offload_loop(l, deadline).await }));
  }
  for h in handles {
    h.await.unwrap();
  }
}

pub fn run() {
  let logger = Arc::new(Logger::new());
  println!("ts_us\tphase\tevent\ttask_id");
  let config = std::env::args().nth(1).unwrap_or_else(|| "current".to_string());
  let deadline = Instant::now() + Duration::from_secs(RUN_SECS);

  match config.as_str() {
    // Multi-thread deployment: the steady mix plus a block_in_place offload worker.
    "multi" => {
      let runtime = rt::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .build()
        .unwrap();
      runtime.block_on(general_workload(logger.clone(), deadline, true));
    }
    // Current-thread deployment: LocalSet startup, then the steady mix.
    _ => {
      startup_init(&logger);
      let runtime = rt::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();
      runtime.block_on(general_workload(logger.clone(), deadline, false));
    }
  }

  let total = logger.start.elapsed();
  eprintln!("ALL PHASES COMPLETE in {:.2}s", total.as_secs_f64());
}
