use clap::Parser;
use hdrhistogram::Histogram;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

#[derive(Parser)]
#[command(name = "micro-fs")]
struct Cli {
    #[arg(short, long, default_value = "tokio")]
    runtime: String,

    #[arg(short, long, default_value_t = 1)]
    threads: usize,

    #[arg(short, long, default_value_t = 100)]
    load: usize,

    #[arg(short, long, default_value_t = 10)]
    duration: u64,

    #[arg(long)]
    csv: bool,

    #[arg(long, default_value_t = 4096)]
    file_size: usize,
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
        println!("fs,{},{},{},{},{:.0},{:.3},{:.3},{:.3},{:.3}",
            runtime, threads, load, duration, ops, p50, p99, p999, max);
    } else {
        println!("Runtime:       {}", runtime);
        println!("Threads:       {}", threads);
        println!("Load:          {}", load);
        println!("Duration:      {}s", duration);
        println!("Total ops:     {}", total);
        println!("Ops/s:         {:.0}", ops);
        println!("Latency (ms):  p50={:.3}  p99={:.3}  p99.9={:.3}  max={:.3}",
            p50, p99, p999, max);
    }
}

// ── Tokio ──

async fn tokio_fs_counter(dir: String, task_id: usize, duration_secs: u64, file_size: usize) -> u64 {
    let data = vec![0xABu8; file_size];
    let mut count: u64 = 0;
    let deadline = tokio::time::Instant::now() + tokio::time::Duration::from_secs(duration_secs);
    while tokio::time::Instant::now() < deadline {
        let path = format!("{}/f_{}_{}.dat", dir, task_id, count);
        tokio::fs::write(&path, &data).await.unwrap();
        let _ = tokio::fs::read(&path).await.unwrap();
        let _ = tokio::fs::remove_file(&path).await;
        count += 1;
    }
    count
}

async fn tokio_fs_sampler(dir: String, task_id: usize, duration_secs: u64, file_size: usize) -> (u64, Histogram<u64>) {
    let data = vec![0xABu8; file_size];
    let mut hist = Histogram::<u64>::new(3).unwrap();
    let mut count: u64 = 0;
    let deadline = tokio::time::Instant::now() + tokio::time::Duration::from_secs(duration_secs);
    while tokio::time::Instant::now() < deadline {
        let start = Instant::now();
        let path = format!("{}/f_{}_{}.dat", dir, task_id, count);
        tokio::fs::write(&path, &data).await.unwrap();
        let _ = tokio::fs::read(&path).await.unwrap();
        let _ = tokio::fs::remove_file(&path).await;
        let elapsed_us = start.elapsed().as_micros() as u64;
        let _ = hist.record(elapsed_us);
        count += 1;
    }
    (count, hist)
}

fn run_tokio(threads: usize, load: usize, duration: u64, csv: bool, file_size: usize) {
    let tmpdir = tempfile::TempDir::new().unwrap();
    let dir = tmpdir.path().to_str().unwrap().to_string();

    let blocking_threads: Option<usize> = std::env::var("LION_BLOCKING_THREADS")
        .ok()
        .and_then(|s| s.parse().ok());

    let rt = if threads <= 1 {
        let mut b = tokio::runtime::Builder::new_current_thread();
        b.enable_all();
        if let Some(n) = blocking_threads { b.max_blocking_threads(n); }
        b.build().unwrap()
    } else {
        let mut b = tokio::runtime::Builder::new_multi_thread();
        b.worker_threads(threads).enable_all();
        if let Some(n) = blocking_threads { b.max_blocking_threads(n); }
        b.build().unwrap()
    };

    rt.block_on(async {
        let samplers = load.min(LATENCY_SAMPLERS);
        let counters = load - samplers;

        let mut sampler_handles = Vec::new();
        for i in 0..samplers {
            let d = dir.clone();
            sampler_handles.push(tokio::spawn(tokio_fs_sampler(d, i, duration, file_size)));
        }
        let mut counter_handles = Vec::new();
        for i in 0..counters {
            let d = dir.clone();
            counter_handles.push(tokio::spawn(tokio_fs_counter(d, samplers + i, duration, file_size)));
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

// ── Lion ──

async fn lion_fs_counter(dir: String, task_id: usize, duration_secs: u64, file_size: usize) -> u64 {
    let data = vec![0xABu8; file_size];
    let mut count: u64 = 0;
    let deadline = Instant::now() + Duration::from_secs(duration_secs);
    while Instant::now() < deadline {
        let path = format!("{}/f_{}_{}.dat", dir, task_id, count);
        lion::fs::write(&path, &data).await.unwrap();
        let _ = lion::fs::read(&path).await.unwrap();
        let _ = lion::fs::remove_file(&path).await;
        count += 1;
    }
    count
}

async fn lion_fs_sampler(dir: String, task_id: usize, duration_secs: u64, file_size: usize) -> (u64, Histogram<u64>) {
    let data = vec![0xABu8; file_size];
    let mut hist = Histogram::<u64>::new(3).unwrap();
    let mut count: u64 = 0;
    let deadline = Instant::now() + Duration::from_secs(duration_secs);
    while Instant::now() < deadline {
        let start = Instant::now();
        let path = format!("{}/f_{}_{}.dat", dir, task_id, count);
        lion::fs::write(&path, &data).await.unwrap();
        let _ = lion::fs::read(&path).await.unwrap();
        let _ = lion::fs::remove_file(&path).await;
        let elapsed_us = start.elapsed().as_micros() as u64;
        let _ = hist.record(elapsed_us);
        count += 1;
    }
    (count, hist)
}

fn run_lion(threads: usize, load: usize, duration: u64, csv: bool, file_size: usize) {
    let tmpdir = tempfile::TempDir::new().unwrap();
    let dir = tmpdir.path().to_str().unwrap().to_string();

    if threads <= 1 {
        let rt = lion::Runtime::new().unwrap();
        rt.block_on(async {
            let samplers = load.min(LATENCY_SAMPLERS);
            let counters = load - samplers;

            let mut sampler_handles = Vec::new();
            for i in 0..samplers {
                let d = dir.clone();
                sampler_handles.push(lion::spawn(lion_fs_sampler(d, i, duration, file_size)));
            }
            let mut counter_handles = Vec::new();
            for i in 0..counters {
                let d = dir.clone();
                counter_handles.push(lion::spawn(lion_fs_counter(d, samplers + i, duration, file_size)));
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
        let rt = lion::runtime::MultiRuntime::new(threads).unwrap();
        let handle = rt.handle().clone();
        rt.block_on(async move {
            let samplers = load.min(LATENCY_SAMPLERS);
            let counters = load - samplers;

            let mut sampler_handles = Vec::new();
            for i in 0..samplers {
                let d = dir.clone();
                sampler_handles.push(handle.spawn(lion_fs_sampler(d, i, duration, file_size)));
            }
            let mut counter_handles = Vec::new();
            for i in 0..counters {
                let d = dir.clone();
                counter_handles.push(handle.spawn(lion_fs_counter(d, samplers + i, duration, file_size)));
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

fn monoio_fs_shard(load: usize, duration: u64, dir: String, file_size: usize) -> (u64, Histogram<u64>) {
    let mut rt = monoio::RuntimeBuilder::<monoio::FusionDriver>::new()
        .enable_timer()
        .build()
        .unwrap();

    rt.block_on(async {
        let samplers = load.min(LATENCY_SAMPLERS);
        let counters = load - samplers;

        let total = Arc::new(AtomicU64::new(0));
        let hist = Arc::new(std::sync::Mutex::new(Histogram::<u64>::new(3).unwrap()));

        let mut handles = Vec::new();
        for i in 0..samplers {
            let d = dir.clone();
            let hist = hist.clone();
            let total = total.clone();
            handles.push(monoio::spawn(async move {
                let data = vec![0xABu8; file_size];
                let mut local_hist = Histogram::<u64>::new(3).unwrap();
                let mut count: u64 = 0;
                let deadline = Instant::now() + Duration::from_secs(duration);
                while Instant::now() < deadline {
                    let start = Instant::now();
                    let path = format!("{}/f_{}_{}.dat", d, i, count);
                    let file = monoio::fs::File::create(&path).await.unwrap();
                    let (res, _) = file.write_all_at(data.clone(), 0).await;
                    res.unwrap();
                    file.close().await.unwrap();
                    let file = monoio::fs::File::open(&path).await.unwrap();
                    let buf = vec![0u8; file_size];
                    let (res, _) = file.read_exact_at(buf, 0).await;
                    res.unwrap();
                    file.close().await.unwrap();
                    let _ = std::fs::remove_file(&path);
                    let elapsed_us = start.elapsed().as_micros() as u64;
                    let _ = local_hist.record(elapsed_us);
                    count += 1;
                }
                total.fetch_add(count, Ordering::Relaxed);
                hist.lock().unwrap().add(&local_hist).unwrap();
            }));
        }
        for i in 0..counters {
            let d = dir.clone();
            let total = total.clone();
            handles.push(monoio::spawn(async move {
                let data = vec![0xABu8; file_size];
                let mut count: u64 = 0;
                let deadline = Instant::now() + Duration::from_secs(duration);
                while Instant::now() < deadline {
                    let path = format!("{}/f_{}_{}.dat", d, samplers + i, count);
                    let file = monoio::fs::File::create(&path).await.unwrap();
                    let (res, _) = file.write_all_at(data.clone(), 0).await;
                    res.unwrap();
                    file.close().await.unwrap();
                    let file = monoio::fs::File::open(&path).await.unwrap();
                    let buf = vec![0u8; file_size];
                    let (res, _) = file.read_exact_at(buf, 0).await;
                    res.unwrap();
                    file.close().await.unwrap();
                    let _ = std::fs::remove_file(&path);
                    count += 1;
                }
                total.fetch_add(count, Ordering::Relaxed);
            }));
        }

        for h in handles {
            h.await;
        }

        let t = total.load(Ordering::Relaxed);
        let locked = hist.lock().unwrap();
        (t, locked.clone())
    })
}

fn run_monoio(threads: usize, load: usize, duration: u64, csv: bool, file_size: usize) {
    let tmpdir = tempfile::TempDir::new().unwrap();
    let dir = tmpdir.path().to_str().unwrap().to_string();

    if threads <= 1 {
        let (total, hist) = monoio_fs_shard(load, duration, dir, file_size);
        print_results("monoio", threads, load, duration, total, &hist, csv);
    } else {
        let per_thread = load / threads;
        let remainder = load % threads;
        let (tx, rx) = std::sync::mpsc::channel();

        let mut workers = Vec::new();
        for i in 0..threads {
            let shard_load = per_thread + if i < remainder { 1 } else { 0 };
            let shard_dir = format!("{}/t{}", dir, i);
            std::fs::create_dir_all(&shard_dir).unwrap();
            let tx = tx.clone();
            workers.push(std::thread::spawn(move || {
                let result = monoio_fs_shard(shard_load, duration, shard_dir, file_size);
                tx.send(result).unwrap();
            }));
        }
        drop(tx);

        let mut total: u64 = 0;
        let mut merged = Histogram::<u64>::new(3).unwrap();
        while let Ok((count, hist)) = rx.recv() {
            total += count;
            merged.add(&hist).unwrap();
        }

        for w in workers {
            w.join().unwrap();
        }

        print_results("monoio", threads, load, duration, total, &merged, csv);
    }
}

fn main() {
    let cli = Cli::parse();

    if !cli.csv {
        println!("=== Micro Filesystem Benchmark ===");
        println!("  {} tasks, {} threads, {}s, runtime: {}\n",
            cli.load, cli.threads, cli.duration, cli.runtime);
    }

    match cli.runtime.as_str() {
        "tokio" => run_tokio(cli.threads, cli.load, cli.duration, cli.csv, cli.file_size),
        "lion" => run_lion(cli.threads, cli.load, cli.duration, cli.csv, cli.file_size),
        "monoio" => run_monoio(cli.threads, cli.load, cli.duration, cli.csv, cli.file_size),
        _ => eprintln!("Unknown runtime: {}. Use tokio, lion, or monoio.", cli.runtime),
    }
}
