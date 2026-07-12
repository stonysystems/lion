use clap::Parser;
use hdrhistogram::Histogram;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

#[derive(Parser)]
#[command(name = "micro-tcp-echo")]
struct Cli {
    #[arg(short, long, default_value = "tokio")]
    runtime: String,

    #[arg(short, long, default_value_t = 1)]
    threads: usize,

    #[arg(short, long, default_value_t = 100)]
    load: usize,

    #[arg(short, long, default_value_t = 10)]
    duration: u64,

    #[arg(short, long, default_value_t = 12345)]
    port: u16,

    #[arg(long)]
    csv: bool,
}

const MSG_SIZE: usize = 64;

fn print_results(
    runtime: &str, threads: usize, load: usize, duration: u64,
    total: u64, hist: &Histogram<u64>, csv: bool,
) {
    let rps = total as f64 / duration as f64;
    let p50 = hist.value_at_quantile(0.5) as f64 / 1000.0;
    let p99 = hist.value_at_quantile(0.99) as f64 / 1000.0;
    let p999 = hist.value_at_quantile(0.999) as f64 / 1000.0;
    let max = hist.max() as f64 / 1000.0;

    if csv {
        println!("tcp-echo,{},{},{},{},{:.0},{:.3},{:.3},{:.3},{:.3}",
            runtime, threads, load, duration, rps, p50, p99, p999, max);
    } else {
        println!("Runtime:       {}", runtime);
        println!("Threads:       {}", threads);
        println!("Load:          {}", load);
        println!("Duration:      {}s", duration);
        println!("Total trips:   {}", total);
        println!("Roundtrip/s:   {:.0}", rps);
        println!("Latency (ms):  p50={:.3}  p99={:.3}  p99.9={:.3}  max={:.3}",
            p50, p99, p999, max);
    }
}

// ── Tokio ──

fn run_tokio(threads: usize, load: usize, duration: u64, port: u16, csv: bool) {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    let rt = if threads <= 1 {
        tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap()
    } else {
        tokio::runtime::Builder::new_multi_thread()
            .worker_threads(threads)
            .enable_all()
            .build()
            .unwrap()
    };

    rt.block_on(async {
        let listener = tokio::net::TcpListener::bind(format!("127.0.0.1:{}", port))
            .await
            .unwrap();

        let total_roundtrips = Arc::new(AtomicU64::new(0));
        let hist = Arc::new(std::sync::Mutex::new(Histogram::<u64>::new(3).unwrap()));

        let server_total = total_roundtrips.clone();
        let server = tokio::spawn(async move {
            loop {
                let (mut stream, _) = match listener.accept().await {
                    Ok(s) => s,
                    Err(_) => break,
                };
                let counter = server_total.clone();
                tokio::spawn(async move {
                    let mut buf = [0u8; MSG_SIZE];
                    loop {
                        match stream.read_exact(&mut buf).await {
                            Ok(_) => {}
                            Err(_) => break,
                        }
                        if stream.write_all(&buf).await.is_err() {
                            break;
                        }
                        counter.fetch_add(1, Ordering::Relaxed);
                    }
                });
            }
        });

        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

        let mut client_handles = Vec::new();
        for _ in 0..load {
            let hist = hist.clone();
            client_handles.push(tokio::spawn(async move {
                let mut stream = tokio::net::TcpStream::connect(format!("127.0.0.1:{}", port))
                    .await
                    .unwrap();
                stream.set_nodelay(true).unwrap();

                let msg = [0xABu8; MSG_SIZE];
                let mut buf = [0u8; MSG_SIZE];
                let deadline = tokio::time::Instant::now()
                    + tokio::time::Duration::from_secs(duration);

                let mut local_hist = Histogram::<u64>::new(3).unwrap();

                while tokio::time::Instant::now() < deadline {
                    let start = Instant::now();
                    if stream.write_all(&msg).await.is_err() {
                        break;
                    }
                    if stream.read_exact(&mut buf).await.is_err() {
                        break;
                    }
                    let elapsed_us = start.elapsed().as_micros() as u64;
                    let _ = local_hist.record(elapsed_us);
                }

                hist.lock().unwrap().add(&local_hist).unwrap();
            }));
        }

        for h in client_handles {
            let _ = h.await;
        }

        server.abort();

        let total = total_roundtrips.load(Ordering::Relaxed);
        let locked = hist.lock().unwrap();
        print_results("tokio", threads, load, duration, total, &locked, csv);
    });
}

// ── Lion ──

fn run_tokio_part(threads: usize, load: usize, duration: u64, port: u16, csv: bool) {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    let total_roundtrips = Arc::new(AtomicU64::new(0));
    let hist = Arc::new(std::sync::Mutex::new(Histogram::<u64>::new(3).unwrap()));

    let mut thread_handles = Vec::new();
    for tid in 0..threads {
        let load_per_thread = load / threads + if tid < load % threads { 1 } else { 0 };
        let total = total_roundtrips.clone();
        let hist = hist.clone();

        thread_handles.push(std::thread::spawn(move || {
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .unwrap();
            rt.block_on(async {
                let socket = tokio::net::TcpSocket::new_v4().unwrap();
                socket.set_reuseaddr(true).unwrap();
                socket.set_reuseport(true).unwrap();
                socket.bind(format!("127.0.0.1:{}", port).parse().unwrap()).unwrap();
                let listener = socket.listen(1024).unwrap();

                let server_total = total.clone();
                tokio::spawn(async move {
                    loop {
                        let (mut stream, _) = match listener.accept().await {
                            Ok(s) => s,
                            Err(_) => break,
                        };
                        let counter = server_total.clone();
                        tokio::spawn(async move {
                            let mut buf = [0u8; MSG_SIZE];
                            loop {
                                match stream.read_exact(&mut buf).await {
                                    Ok(_) => {}
                                    Err(_) => break,
                                }
                                if stream.write_all(&buf).await.is_err() {
                                    break;
                                }
                                counter.fetch_add(1, Ordering::Relaxed);
                            }
                        });
                    }
                });

                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

                let mut client_handles = Vec::new();
                for _ in 0..load_per_thread {
                    let hist = hist.clone();
                    client_handles.push(tokio::spawn(async move {
                        let mut stream = tokio::net::TcpStream::connect(
                            format!("127.0.0.1:{}", port),
                        )
                        .await
                        .unwrap();
                        stream.set_nodelay(true).unwrap();

                        let msg = [0xABu8; MSG_SIZE];
                        let mut buf = [0u8; MSG_SIZE];
                        let deadline = tokio::time::Instant::now()
                            + tokio::time::Duration::from_secs(duration);
                        let mut local_hist = Histogram::<u64>::new(3).unwrap();

                        while tokio::time::Instant::now() < deadline {
                            let start = Instant::now();
                            if stream.write_all(&msg).await.is_err() {
                                break;
                            }
                            if stream.read_exact(&mut buf).await.is_err() {
                                break;
                            }
                            let elapsed_us = start.elapsed().as_micros() as u64;
                            let _ = local_hist.record(elapsed_us);
                        }

                        hist.lock().unwrap().add(&local_hist).unwrap();
                    }));
                }

                for h in client_handles {
                    let _ = h.await;
                }
            });
        }));
    }

    for h in thread_handles {
        h.join().unwrap();
    }

    let total = total_roundtrips.load(Ordering::Relaxed);
    let locked = hist.lock().unwrap();
    print_results("tokio-part", threads, load, duration, total, &locked, csv);
}

fn run_lion(threads: usize, load: usize, duration: u64, port: u16, csv: bool) {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    let total_roundtrips = Arc::new(AtomicU64::new(0));
    let hist = Arc::new(std::sync::Mutex::new(Histogram::<u64>::new(3).unwrap()));

    let mut thread_handles = Vec::new();
    for tid in 0..threads {
        let load_per_thread = load / threads + if tid < load % threads { 1 } else { 0 };
        let total = total_roundtrips.clone();
        let hist = hist.clone();

        thread_handles.push(std::thread::spawn(move || {
            let rt = lion::Runtime::new().unwrap();
            rt.block_on(async {
                let socket = lion::net::TcpSocket::new_v4().unwrap();
                socket.set_reuseaddr(true).unwrap();
                socket.set_reuseport(true).unwrap();
                socket.bind(format!("127.0.0.1:{}", port).parse().unwrap()).unwrap();
                let listener = socket.listen(1024).unwrap();

                let server_total = total.clone();
                lion::spawn(async move {
                    loop {
                        let (mut stream, _) = match listener.accept().await {
                            Ok(s) => s,
                            Err(_) => break,
                        };
                        let counter = server_total.clone();
                        lion::spawn(async move {
                            let mut buf = [0u8; MSG_SIZE];
                            loop {
                                match stream.read_exact(&mut buf).await {
                                    Ok(_) => {}
                                    Err(_) => break,
                                }
                                if stream.write_all(&buf).await.is_err() {
                                    break;
                                }
                                counter.fetch_add(1, Ordering::Relaxed);
                            }
                        });
                    }
                });

                lion::time::sleep(lion::time::Duration::from_millis(100)).await;

                let mut client_handles = Vec::new();
                for _ in 0..load_per_thread {
                    let hist = hist.clone();
                    client_handles.push(lion::spawn(async move {
                        let mut stream = lion::net::TcpStream::connect(
                            format!("127.0.0.1:{}", port),
                        )
                        .await
                        .unwrap();
                        stream.set_nodelay(true).unwrap();

                        let msg = [0xABu8; MSG_SIZE];
                        let mut buf = [0u8; MSG_SIZE];
                        let deadline = Instant::now() + Duration::from_secs(duration);
                        let mut local_hist = Histogram::<u64>::new(3).unwrap();

                        while Instant::now() < deadline {
                            let start = Instant::now();
                            if stream.write_all(&msg).await.is_err() {
                                break;
                            }
                            if stream.read_exact(&mut buf).await.is_err() {
                                break;
                            }
                            let elapsed_us = start.elapsed().as_micros() as u64;
                            let _ = local_hist.record(elapsed_us);
                        }

                        hist.lock().unwrap().add(&local_hist).unwrap();
                    }));
                }

                for h in client_handles {
                    let _ = h.await;
                }
            });
        }));
    }

    for h in thread_handles {
        h.join().unwrap();
    }

    let total = total_roundtrips.load(Ordering::Relaxed);
    let locked = hist.lock().unwrap();
    print_results("lion", threads, load, duration, total, &locked, csv);
}

// ── Monoio ──

fn run_monoio(load: usize, duration: u64, port: u16, csv: bool) {
    use monoio::io::{AsyncReadRentExt, AsyncWriteRentExt, Splitable};

    let mut rt = monoio::RuntimeBuilder::<monoio::FusionDriver>::new()
        .enable_timer()
        .build()
        .unwrap();

    rt.block_on(async {
        let listener = monoio::net::TcpListener::bind(format!("127.0.0.1:{}", port)).unwrap();

        let total_roundtrips = Arc::new(AtomicU64::new(0));
        let hist = Arc::new(std::sync::Mutex::new(Histogram::<u64>::new(3).unwrap()));

        let server_total = total_roundtrips.clone();
        let _server = monoio::spawn(async move {
            loop {
                let (stream, _) = match listener.accept().await {
                    Ok(s) => s,
                    Err(_) => break,
                };
                let counter = server_total.clone();
                monoio::spawn(async move {
                    let (mut reader, mut writer) = stream.into_split();
                    loop {
                        let buf = vec![0u8; MSG_SIZE];
                        let (res, buf) = reader.read_exact(buf).await;
                        if res.is_err() {
                            break;
                        }
                        let (res, _) = writer.write_all(buf).await;
                        if res.is_err() {
                            break;
                        }
                        counter.fetch_add(1, Ordering::Relaxed);
                    }
                });
            }
        });

        monoio::time::sleep(monoio::time::Duration::from_millis(100)).await;

        let mut client_handles = Vec::new();
        for _ in 0..load {
            let hist = hist.clone();
            client_handles.push(monoio::spawn(async move {
                let stream = monoio::net::TcpStream::connect(format!("127.0.0.1:{}", port))
                    .await
                    .unwrap();
                stream.set_nodelay(true).unwrap();
                let (mut reader, mut writer) = stream.into_split();

                let deadline = Instant::now() + Duration::from_secs(duration);
                let mut local_hist = Histogram::<u64>::new(3).unwrap();

                while Instant::now() < deadline {
                    let start = Instant::now();
                    let msg = vec![0xABu8; MSG_SIZE];
                    let (res, _) = writer.write_all(msg).await;
                    if res.is_err() {
                        break;
                    }
                    let buf = vec![0u8; MSG_SIZE];
                    let (res, _) = reader.read_exact(buf).await;
                    if res.is_err() {
                        break;
                    }
                    let elapsed_us = start.elapsed().as_micros() as u64;
                    let _ = local_hist.record(elapsed_us);
                }

                hist.lock().unwrap().add(&local_hist).unwrap();
            }));
        }

        for h in client_handles {
            h.await;
        }

        let total = total_roundtrips.load(Ordering::Relaxed);
        let locked = hist.lock().unwrap();
        print_results("monoio", 1, load, duration, total, &locked, csv);
    });
}

fn main() {
    let cli = Cli::parse();

    if !cli.csv {
        println!("=== Micro TCP Echo Benchmark ===");
        println!("  {} connections, {} threads, {}s, runtime: {}\n",
            cli.load, cli.threads, cli.duration, cli.runtime);
    }

    match cli.runtime.as_str() {
        "tokio" => run_tokio(cli.threads, cli.load, cli.duration, cli.port, cli.csv),
        "tokio-part" => run_tokio_part(cli.threads, cli.load, cli.duration, cli.port, cli.csv),
        "lion" => run_lion(cli.threads, cli.load, cli.duration, cli.port, cli.csv),
        "monoio" => run_monoio(cli.load, cli.duration, cli.port, cli.csv),
        _ => eprintln!("Unknown runtime: {}. Use tokio, tokio-part, lion, or monoio.", cli.runtime),
    }
}
