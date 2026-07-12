use clap::Parser;
use hdrhistogram::Histogram;
use std::sync::atomic::{AtomicU64, AtomicUsize, AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

#[derive(Parser)]
#[command(name = "micro-timer")]
struct Cli {
    #[arg(short, long, default_value = "tokio")]
    runtime: String,

    #[arg(short, long, default_value_t = 1)]
    threads: usize,

    #[arg(short, long, default_value_t = 1000)]
    load: usize,

    #[arg(short, long, default_value_t = 10)]
    duration: u64,

    #[arg(long)]
    csv: bool,
}

const LATENCY_SAMPLERS: usize = 10;

fn print_results(
    runtime: &str, threads: usize, load: usize, duration: u64,
    total: u64, hist: &Histogram<u64>, csv: bool,
) {
    let ops = total as f64 / duration as f64;
    let p50 = hist.value_at_quantile(0.5) as f64 / 1000.0;
    let p99 = hist.value_at_quantile(0.99) as f64 / 1000.0;
    let p999 = hist.value_at_quantile(0.999) as f64 / 1000.0;
    let max = hist.max() as f64 / 1000.0;

    if csv {
        println!("timer,{},{},{},{},{:.0},{:.3},{:.3},{:.3},{:.3}",
            runtime, threads, load, duration, ops, p50, p99, p999, max);
    } else {
        println!("Runtime:       {}", runtime);
        println!("Threads:       {}", threads);
        println!("Load:          {}", load);
        println!("Duration:      {}s", duration);
        println!("Total ops:     {}", total);
        println!("Cancel/s:      {:.0}", ops);
        println!("Latency (ms):  p50={:.3}  p99={:.3}  p99.9={:.3}  max={:.3}",
            p50, p99, p999, max);
    }
}

// ── Tokio ──

async fn tokio_counter(duration_secs: u64) -> u64 {
    let mut count: u64 = 0;
    let deadline = tokio::time::Instant::now() + tokio::time::Duration::from_secs(duration_secs);
    while tokio::time::Instant::now() < deadline {
        tokio::select! {
            _ = tokio::time::sleep(tokio::time::Duration::from_secs(1)) => {}
            _ = tokio::time::sleep(tokio::time::Duration::from_millis(1)) => {}
        }
        count += 1;
    }
    count
}

async fn tokio_sampler(duration_secs: u64) -> (u64, Histogram<u64>) {
    let mut hist = Histogram::<u64>::new(3).unwrap();
    let mut count: u64 = 0;
    let deadline = tokio::time::Instant::now() + tokio::time::Duration::from_secs(duration_secs);
    while tokio::time::Instant::now() < deadline {
        let start = Instant::now();
        tokio::select! {
            _ = tokio::time::sleep(tokio::time::Duration::from_secs(1)) => {}
            _ = tokio::time::sleep(tokio::time::Duration::from_millis(1)) => {}
        }
        let elapsed_us = start.elapsed().as_micros() as u64;
        let _ = hist.record(elapsed_us);
        count += 1;
    }
    (count, hist)
}

fn run_tokio(threads: usize, load: usize, duration: u64, csv: bool) {
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
        let samplers = load.min(LATENCY_SAMPLERS);
        let counters = load - samplers;

        let mut sampler_handles = Vec::new();
        for _ in 0..samplers {
            sampler_handles.push(tokio::spawn(tokio_sampler(duration)));
        }
        let mut counter_handles = Vec::new();
        for _ in 0..counters {
            counter_handles.push(tokio::spawn(tokio_counter(duration)));
        }

        let mut total: u64 = 0;
        let mut merged = Histogram::<u64>::new(3).unwrap();
        for h in sampler_handles {
            let (count, hist) = h.await.unwrap();
            total += count;
            merged.add(&hist).unwrap();
        }
        for h in counter_handles {
            total += h.await.unwrap();
        }

        print_results("tokio", threads, load, duration, total, &merged, csv);
    });
}

// ── Tokio Partition ──

#[derive(Clone)]
struct TokioPartitionHandle {
    handles: Arc<Vec<tokio::runtime::Handle>>,
    next: Arc<AtomicUsize>,
}

impl TokioPartitionHandle {
    fn spawn<T: Send + 'static>(
        &self,
        future: impl std::future::Future<Output = T> + Send + 'static,
    ) -> tokio::task::JoinHandle<T> {
        let idx = self.next.fetch_add(1, Ordering::Relaxed) % self.handles.len();
        self.handles[idx].spawn(future)
    }
}

struct TokioPartitionRuntime {
    handle: TokioPartitionHandle,
    shutdown: Arc<AtomicBool>,
    workers: Vec<std::thread::JoinHandle<()>>,
    main_rt: tokio::runtime::Runtime,
}

impl TokioPartitionRuntime {
    fn new(threads: usize) -> Self {
        let threads = threads.max(1);
        let shutdown = Arc::new(AtomicBool::new(false));

        let main_rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();

        let mut all_handles = Vec::new();
        let mut workers = Vec::new();

        for _ in 0..threads {
            let (tx, rx) = std::sync::mpsc::channel();
            let shut = shutdown.clone();
            let worker = std::thread::spawn(move || {
                let rt = tokio::runtime::Builder::new_current_thread()
                    .enable_all()
                    .build()
                    .unwrap();
                tx.send(rt.handle().clone()).unwrap();
                rt.block_on(async move {
                    loop {
                        if shut.load(Ordering::Relaxed) { break; }
                        tokio::task::yield_now().await;
                    }
                });
            });
            all_handles.push(rx.recv().unwrap());
            workers.push(worker);
        }

        let handle = TokioPartitionHandle {
            handles: Arc::new(all_handles),
            next: Arc::new(AtomicUsize::new(0)),
        };

        TokioPartitionRuntime { handle, shutdown, workers, main_rt }
    }

    fn handle(&self) -> TokioPartitionHandle {
        self.handle.clone()
    }

    fn block_on<F: std::future::Future>(&self, future: F) -> F::Output {
        self.main_rt.block_on(future)
    }
}

impl Drop for TokioPartitionRuntime {
    fn drop(&mut self) {
        self.shutdown.store(true, Ordering::Relaxed);
        for w in self.workers.drain(..) {
            let _ = w.join();
        }
    }
}

fn run_tokio_part(threads: usize, load: usize, duration: u64, csv: bool) {
    let rt = TokioPartitionRuntime::new(threads);
    let handle = rt.handle();

    rt.block_on(async move {
        let samplers = load.min(LATENCY_SAMPLERS);
        let counters = load - samplers;

        let mut sampler_handles = Vec::new();
        for _ in 0..samplers {
            sampler_handles.push(handle.spawn(tokio_sampler(duration)));
        }
        let mut counter_handles = Vec::new();
        for _ in 0..counters {
            counter_handles.push(handle.spawn(tokio_counter(duration)));
        }

        let mut total: u64 = 0;
        let mut merged = Histogram::<u64>::new(3).unwrap();
        for h in sampler_handles {
            let (count, hist) = h.await.unwrap();
            total += count;
            merged.add(&hist).unwrap();
        }
        for h in counter_handles {
            total += h.await.unwrap();
        }

        print_results("tokio-part", threads, load, duration, total, &merged, csv);
    });
}

// ── Lion ──

async fn lion_counter(duration_secs: u64) -> u64 {
    let mut count: u64 = 0;
    let deadline = Instant::now() + Duration::from_secs(duration_secs);
    while Instant::now() < deadline {
        let long_sleep = std::pin::pin!(lion::time::sleep(lion::time::Duration::from_millis(1000)));
        let short_sleep = std::pin::pin!(lion::time::sleep(lion::time::Duration::from_millis(1)));
        futures::future::select(long_sleep, short_sleep).await;
        count += 1;
    }
    count
}

async fn lion_sampler(duration_secs: u64) -> (u64, Histogram<u64>) {
    let mut hist = Histogram::<u64>::new(3).unwrap();
    let mut count: u64 = 0;
    let deadline = Instant::now() + Duration::from_secs(duration_secs);
    while Instant::now() < deadline {
        let start = Instant::now();
        let long_sleep = std::pin::pin!(lion::time::sleep(lion::time::Duration::from_millis(1000)));
        let short_sleep = std::pin::pin!(lion::time::sleep(lion::time::Duration::from_millis(1)));
        futures::future::select(long_sleep, short_sleep).await;
        let elapsed_us = start.elapsed().as_micros() as u64;
        let _ = hist.record(elapsed_us);
        count += 1;
    }
    (count, hist)
}

fn run_lion(threads: usize, load: usize, duration: u64, csv: bool) {
    if threads <= 1 {
        let rt = lion::Runtime::new().unwrap();
        rt.block_on(async {
            let samplers = load.min(LATENCY_SAMPLERS);
            let counters = load - samplers;

            let mut sampler_handles = Vec::new();
            for _ in 0..samplers {
                sampler_handles.push(lion::spawn(lion_sampler(duration)));
            }
            let mut counter_handles = Vec::new();
            for _ in 0..counters {
                counter_handles.push(lion::spawn(lion_counter(duration)));
            }

            let mut total: u64 = 0;
            let mut merged = Histogram::<u64>::new(3).unwrap();
            for h in sampler_handles {
                let (count, hist) = h.await.unwrap();
                total += count;
                merged.add(&hist).unwrap();
            }
            for h in counter_handles {
                total += h.await.unwrap();
            }

            print_results("lion", threads, load, duration, total, &merged, csv);
        });
    } else {
        let rt = lion::multi::MultiRuntime::new(threads).unwrap();
        let handle = rt.handle().clone();

        rt.block_on(async {
            let samplers = load.min(LATENCY_SAMPLERS);
            let counters = load - samplers;

            let mut sampler_handles = Vec::new();
            for _ in 0..samplers {
                sampler_handles.push(handle.spawn(lion_sampler(duration)));
            }
            let mut counter_handles = Vec::new();
            for _ in 0..counters {
                counter_handles.push(handle.spawn(lion_counter(duration)));
            }

            let mut total: u64 = 0;
            let mut merged = Histogram::<u64>::new(3).unwrap();
            for h in sampler_handles {
                let (count, hist) = h.await.unwrap();
                total += count;
                merged.add(&hist).unwrap();
            }
            for h in counter_handles {
                total += h.await.unwrap();
            }

            print_results("lion", threads, load, duration, total, &merged, csv);
        });
    }
}

// ── Monoio ──

async fn monoio_counter(duration_secs: u64) -> u64 {
    let mut count: u64 = 0;
    let deadline = Instant::now() + Duration::from_secs(duration_secs);
    while Instant::now() < deadline {
        monoio::select! {
            _ = monoio::time::sleep(monoio::time::Duration::from_secs(1)) => {}
            _ = monoio::time::sleep(monoio::time::Duration::from_millis(1)) => {}
        }
        count += 1;
    }
    count
}

async fn monoio_sampler(duration_secs: u64) -> (u64, Histogram<u64>) {
    let mut hist = Histogram::<u64>::new(3).unwrap();
    let mut count: u64 = 0;
    let deadline = Instant::now() + Duration::from_secs(duration_secs);
    while Instant::now() < deadline {
        let start = Instant::now();
        monoio::select! {
            _ = monoio::time::sleep(monoio::time::Duration::from_secs(1)) => {}
            _ = monoio::time::sleep(monoio::time::Duration::from_millis(1)) => {}
        }
        let elapsed_us = start.elapsed().as_micros() as u64;
        let _ = hist.record(elapsed_us);
        count += 1;
    }
    (count, hist)
}

fn run_monoio(load: usize, duration: u64, csv: bool) {
    let mut rt = monoio::RuntimeBuilder::<monoio::FusionDriver>::new()
        .enable_timer()
        .build()
        .unwrap();

    rt.block_on(async {
        let samplers = load.min(LATENCY_SAMPLERS);
        let counters = load - samplers;

        let mut sampler_handles = Vec::new();
        for _ in 0..samplers {
            sampler_handles.push(monoio::spawn(monoio_sampler(duration)));
        }
        let mut counter_handles = Vec::new();
        for _ in 0..counters {
            counter_handles.push(monoio::spawn(monoio_counter(duration)));
        }

        let mut total: u64 = 0;
        let mut merged = Histogram::<u64>::new(3).unwrap();
        for h in sampler_handles {
            let (count, hist) = h.await;
            total += count;
            merged.add(&hist).unwrap();
        }
        for h in counter_handles {
            total += h.await;
        }

        print_results("monoio", 1, load, duration, total, &merged, csv);
    });
}

fn main() {
    let cli = Cli::parse();

    if !cli.csv {
        println!("=== Micro Timer Cancel Benchmark ===");
        println!("  {} tasks, {} threads, {}s, runtime: {}\n",
            cli.load, cli.threads, cli.duration, cli.runtime);
    }

    match cli.runtime.as_str() {
        "tokio" => run_tokio(cli.threads, cli.load, cli.duration, cli.csv),
        "tokio-part" => run_tokio_part(cli.threads, cli.load, cli.duration, cli.csv),
        "lion" => run_lion(cli.threads, cli.load, cli.duration, cli.csv),
        "monoio" => run_monoio(cli.load, cli.duration, cli.csv),
        _ => eprintln!("Unknown runtime: {}. Use tokio, tokio-part, lion, or monoio.", cli.runtime),
    }
}
