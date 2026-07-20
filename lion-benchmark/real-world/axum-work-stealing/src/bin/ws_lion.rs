//! Lion arm: N single-threaded per-core executors (thread-per-core, no stealing).
//!
//! Each core runs its own accept loop on its own `SO_REUSEPORT` listener, so a
//! connection's socket is registered and driven on the SAME core that accepted it
//! (a connection accepted on one core's reactor cannot be driven by another's).
//! Within a connection the hyper executor uses `lion::spawn`, keeping its work on
//! that core. So a heavy request pins its core and blocks the connections queued
//! behind it there — and no other core can steal them.

use axum_work_stealing::router;
use clap::Parser;
use hyper_util::rt::TokioIo;
use std::net::SocketAddr;
use tower::Service;

#[derive(Parser)]
#[command(name = "ws-lion")]
struct Args {
    #[arg(long, default_value = "0.0.0.0")]
    host: String,
    #[arg(long, default_value_t = 8080)]
    port: u16,
    /// Number of Lion per-core executor instances (= cores).
    #[arg(long, default_value_t = 8)]
    cores: usize,
}

/// A hyper executor that keeps a connection's sub-tasks on the *current* core.
#[derive(Clone)]
struct LocalExec;

impl<F> hyper::rt::Executor<F> for LocalExec
where
    F: std::future::Future + Send + 'static,
    F::Output: Send + 'static,
{
    fn execute(&self, fut: F) {
        lion::spawn(fut);
    }
}

async fn serve_one_core(addr: SocketAddr) {
    // Per-core SO_REUSEPORT listener: created ON this core, so its fd lives on
    // this core's reactor.
    let sock = if addr.is_ipv4() {
        lion::net::TcpSocket::new_v4()
    } else {
        lion::net::TcpSocket::new_v6()
    }
    .expect("create socket");
    sock.set_reuseport(true).expect("set SO_REUSEPORT");
    sock.bind(addr).expect("bind");
    let listener = sock.listen(1024).expect("listen");

    loop {
        let (stream, _) = match listener.accept().await {
            Ok(s) => s,
            Err(e) => {
                eprintln!("accept error: {e}");
                continue;
            }
        };
        let svc = router();
        // Serve this connection ON THIS core (lion::spawn = current executor).
        lion::spawn(async move {
            let io = TokioIo::new(stream);
            let hyper_service = hyper::service::service_fn(move |req| {
                let mut svc = svc.clone();
                async move { svc.call(req).await }
            });
            if let Err(err) = hyper_util::server::conn::auto::Builder::new(LocalExec)
                .serve_connection(io, hyper_service)
                .await
            {
                eprintln!("connection error: {err}");
            }
        });
    }
}

fn main() {
    let args = Args::parse();

    let rt = lion::runtime::MultiRuntime::new(args.cores).unwrap();
    let handle = rt.handle().clone();
    let addr: SocketAddr = format!("{}:{}", args.host, args.port).parse().unwrap();
    eprintln!("ws-lion: {} per-core executors on {}", args.cores, addr);

    rt.block_on(async move {
        // One accept loop per core. `handle.spawn` round-robins, so `cores`
        // spawns land one on each core.
        let mut tasks = Vec::with_capacity(args.cores);
        for _ in 0..args.cores {
            tasks.push(handle.spawn(serve_one_core(addr)));
        }
        for t in tasks {
            let _ = t.await;
        }
    });
}
