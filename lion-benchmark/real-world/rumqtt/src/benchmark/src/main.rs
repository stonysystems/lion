use anyhow::{Context, Result};
use clap::Parser;
use hdrhistogram::Histogram;
use rumqttc::{AsyncClient, Event, MqttOptions, Packet, QoS};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

#[derive(Parser, Debug)]
#[command(name = "mqtt-benchmark")]
#[command(about = "MQTT benchmark for rumqttd (tokio vs lion)")]
struct Args {
  #[arg(short = 'h', long, default_value = "127.0.0.1")]
  host: String,

  #[arg(short, long, default_value_t = 1883)]
  port: u16,

  #[arg(long, default_value_t = 30)]
  duration: u64,

  #[arg(short, long, default_value = "fanout,fanin,p2p,burst")]
  workloads: String,

  #[arg(long, default_value_t = 128)]
  payload_size: usize,

  #[arg(long)]
  csv: bool,

  #[arg(long, default_value = "rumqttd")]
  system: String,

  #[arg(long, default_value = "tokio")]
  runtime: String,
}

#[derive(Debug, Clone, Copy)]
enum Workload {
  Fanout,
  Fanin,
  P2p,
  Burst,
}

impl Workload {
  fn from_str(s: &str) -> Option<Self> {
    match s.trim().to_lowercase().as_str() {
      "fanout" => Some(Workload::Fanout),
      "fanin" => Some(Workload::Fanin),
      "p2p" => Some(Workload::P2p),
      "burst" => Some(Workload::Burst),
      _ => None,
    }
  }

  fn name(&self) -> &'static str {
    match self {
      Workload::Fanout => "W-Fanout",
      Workload::Fanin => "W-Fanin",
      Workload::P2p => "W-P2P",
      Workload::Burst => "W-Burst",
    }
  }

  fn description(&self) -> &'static str {
    match self {
      Workload::Fanout => "1 publisher, 50 subscribers on same topic",
      Workload::Fanin => "50 publishers, 10 subscribers on same topic",
      Workload::P2p => "50 pairs, each pub/sub on unique topic",
      Workload::Burst => "10 publishers sending 1000 msg bursts, 10 subscribers",
    }
  }
}

struct WorkloadResult {
  workload: Workload,
  published: usize,
  received: usize,
  duration: Duration,
  pub_throughput: f64,
  sub_throughput: f64,
  pub_latencies: Histogram<u64>,
}

impl WorkloadResult {
  fn print_summary(&self) {
    println!(
      "\n====== {} ({}) ======",
      self.workload.name(),
      self.workload.description()
    );
    println!(
      "  Duration: {:.2}s",
      self.duration.as_secs_f64()
    );
    println!("  Published: {} msgs ({:.2} msgs/sec)", self.published, self.pub_throughput);
    println!("  Received: {} msgs ({:.2} msgs/sec)", self.received, self.sub_throughput);
    println!(
      "  Publish latency: p50={:.2}ms p95={:.2}ms p99={:.2}ms p99.9={:.2}ms max={:.2}ms",
      self.pub_latencies.value_at_quantile(0.50) as f64 / 1000.0,
      self.pub_latencies.value_at_quantile(0.95) as f64 / 1000.0,
      self.pub_latencies.value_at_quantile(0.99) as f64 / 1000.0,
      self.pub_latencies.value_at_quantile(0.999) as f64 / 1000.0,
      self.pub_latencies.max() as f64 / 1000.0,
    );
  }

  fn print_csv(&self, system: &str, runtime: &str) {
    println!(
      "{},{},{},{:.2},{:.2},{:.2},{:.2},{:.2},{:.2},{:.2}",
      system,
      runtime,
      self.workload.name(),
      self.pub_throughput,
      self.sub_throughput,
      self.pub_latencies.value_at_quantile(0.50) as f64 / 1000.0,
      self.pub_latencies.value_at_quantile(0.95) as f64 / 1000.0,
      self.pub_latencies.value_at_quantile(0.99) as f64 / 1000.0,
      self.pub_latencies.value_at_quantile(0.999) as f64 / 1000.0,
      self.pub_latencies.max() as f64 / 1000.0,
    );
  }
}

fn make_client(host: &str, port: u16, id: &str) -> (AsyncClient, rumqttc::EventLoop) {
  let mut opts = MqttOptions::new(id, host, port);
  opts.set_keep_alive(Duration::from_secs(30));
  opts.set_inflight(100);
  AsyncClient::new(opts, 1000)
}

fn run_subscriber(
  host: String,
  port: u16,
  client_id: String,
  topic: String,
  duration_secs: u64,
) -> thread::JoinHandle<Result<usize>> {
  thread::spawn(move || {
    let rt = tokio::runtime::Builder::new_current_thread()
      .enable_all()
      .build()?;

    rt.block_on(async {
      let (client, mut eventloop) = make_client(&host, port, &client_id);
      client
        .subscribe(&topic, QoS::AtLeastOnce)
        .await
        .context("subscribe failed")?;

      let end_time = Instant::now() + Duration::from_secs(duration_secs);
      let mut received: usize = 0;

      while Instant::now() < end_time {
        match tokio::time::timeout(Duration::from_millis(100), eventloop.poll()).await {
          Ok(Ok(Event::Incoming(Packet::Publish(_)))) => {
            received += 1;
          }
          Ok(Ok(_)) => {}
          Ok(Err(_)) => {
            break;
          }
          Err(_) => {}
        }
      }

      let _ = client.disconnect().await;

      Ok(received)
    })
  })
}

fn run_publisher(
  host: String,
  port: u16,
  client_id: String,
  topic: String,
  payload_size: usize,
  duration_secs: u64,
  rate_per_sec: Option<u64>,
) -> thread::JoinHandle<Result<(Histogram<u64>, usize)>> {
  thread::spawn(move || {
    let rt = tokio::runtime::Builder::new_current_thread()
      .enable_all()
      .build()?;

    rt.block_on(async {
      let (client, mut eventloop) = make_client(&host, port, &client_id);

      tokio::spawn(async move {
        loop {
          if eventloop.poll().await.is_err() {
            break;
          }
        }
      });

      tokio::time::sleep(Duration::from_millis(500)).await;

      let payload = vec![b'x'; payload_size];
      let end_time = Instant::now() + Duration::from_secs(duration_secs);
      let mut local_hist =
        Histogram::<u64>::new(3).context("Failed to create histogram")?;
      let mut count: usize = 0;
      let interval = rate_per_sec.map(|r| Duration::from_micros(1_000_000 / r));

      while Instant::now() < end_time {
        let req_start = Instant::now();
        if client
          .publish(&topic, QoS::AtLeastOnce, false, payload.clone())
          .await
          .is_err()
        {
          break;
        }
        let latency = req_start.elapsed();
        local_hist
          .record(latency.as_micros() as u64)
          .context("Failed to record latency")?;
        count += 1;

        if let Some(iv) = interval {
          let elapsed = req_start.elapsed();
          if iv > elapsed {
            tokio::time::sleep(iv - elapsed).await;
          }
        }
      }

      let _ = client.disconnect().await;

      Ok((local_hist, count))
    })
  })
}

fn run_fanout(
  host: &str,
  port: u16,
  payload_size: usize,
  duration_secs: u64,
) -> Result<WorkloadResult> {
  let topic = "bench/fanout".to_string();
  let start = Instant::now();

  let mut sub_handles = Vec::new();
  for i in 0..50 {
    sub_handles.push(run_subscriber(
      host.to_string(),
      port,
      format!("sub-fanout-{}", i),
      topic.clone(),
      duration_secs,
    ));
  }

  thread::sleep(Duration::from_secs(1));

  let pub_handle = run_publisher(
    host.to_string(),
    port,
    "pub-fanout-0".to_string(),
    topic,
    payload_size,
    duration_secs - 1,
    Some(10_000),
  );

  let (pub_hist, pub_count) = pub_handle
    .join()
    .map_err(|_| anyhow::anyhow!("Publisher thread panicked"))??;

  let mut total_received: usize = 0;
  for h in sub_handles {
    total_received += h
      .join()
      .map_err(|_| anyhow::anyhow!("Subscriber thread panicked"))??;
  }

  let actual_duration = start.elapsed();
  Ok(WorkloadResult {
    workload: Workload::Fanout,
    published: pub_count,
    received: total_received,
    duration: actual_duration,
    pub_throughput: pub_count as f64 / actual_duration.as_secs_f64(),
    sub_throughput: total_received as f64 / actual_duration.as_secs_f64(),
    pub_latencies: pub_hist,
  })
}

fn run_fanin(
  host: &str,
  port: u16,
  payload_size: usize,
  duration_secs: u64,
) -> Result<WorkloadResult> {
  let topic = "bench/fanin".to_string();
  let num_subscribers = 10;
  let start = Instant::now();

  let mut sub_handles = Vec::new();
  for i in 0..num_subscribers {
    sub_handles.push(run_subscriber(
      host.to_string(),
      port,
      format!("sub-fanin-{}", i),
      topic.clone(),
      duration_secs,
    ));
  }

  thread::sleep(Duration::from_secs(1));

  let (tx, rx) = mpsc::channel::<(Histogram<u64>, usize)>();
  let mut pub_handles = Vec::new();

  for i in 0..50 {
    let tx = tx.clone();
    let h = host.to_string();
    let t = topic.clone();

    let handle = thread::spawn(move || -> Result<()> {
      let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;

      rt.block_on(async {
        let (client, mut eventloop) = make_client(&h, port, &format!("pub-fanin-{}", i));

        tokio::spawn(async move {
          loop {
            if eventloop.poll().await.is_err() {
              break;
            }
          }
        });

        tokio::time::sleep(Duration::from_millis(500)).await;

        let payload = vec![b'x'; payload_size];
        let end_time = Instant::now() + Duration::from_secs(duration_secs - 1);
        let mut local_hist =
          Histogram::<u64>::new(3).context("Failed to create histogram")?;
        let mut count: usize = 0;

        while Instant::now() < end_time {
          let req_start = Instant::now();
          if client
            .publish(&t, QoS::AtLeastOnce, false, payload.clone())
            .await
            .is_err()
          {
            break;
          }
          let latency = req_start.elapsed();
          local_hist
            .record(latency.as_micros() as u64)
            .context("Failed to record latency")?;
          count += 1;
        }

        let _ = client.disconnect().await;

        tx.send((local_hist, count))
          .map_err(|_| anyhow::anyhow!("Failed to send results"))?;
        Ok(())
      })
    });

    pub_handles.push(handle);
  }

  drop(tx);

  for h in pub_handles {
    h.join()
      .map_err(|_| anyhow::anyhow!("Publisher thread panicked"))??;
  }

  let mut total_received: usize = 0;
  for h in sub_handles {
    total_received += h
      .join()
      .map_err(|_| anyhow::anyhow!("Subscriber thread panicked"))??;
  }

  let actual_duration = start.elapsed();

  let mut total_published: usize = 0;
  let mut merged_hist =
    Histogram::<u64>::new(3).context("Failed to create merged histogram")?;

  for (hist, count) in rx.iter() {
    merged_hist
      .add(&hist)
      .context("Failed to merge histogram")?;
    total_published += count;
  }

  Ok(WorkloadResult {
    workload: Workload::Fanin,
    published: total_published,
    received: total_received,
    duration: actual_duration,
    pub_throughput: total_published as f64 / actual_duration.as_secs_f64(),
    sub_throughput: total_received as f64 / actual_duration.as_secs_f64(),
    pub_latencies: merged_hist,
  })
}

fn run_p2p(
  host: &str,
  port: u16,
  payload_size: usize,
  duration_secs: u64,
) -> Result<WorkloadResult> {
  let start = Instant::now();
  let pairs = 50;

  let mut sub_handles = Vec::new();
  for i in 0..pairs {
    let topic = format!("bench/p2p/{}", i);
    sub_handles.push(run_subscriber(
      host.to_string(),
      port,
      format!("sub-p2p-{}", i),
      topic,
      duration_secs,
    ));
  }

  thread::sleep(Duration::from_secs(1));

  let (tx, rx) = mpsc::channel::<(Histogram<u64>, usize)>();
  let mut pub_handles = Vec::new();

  for i in 0..pairs {
    let tx = tx.clone();
    let h = host.to_string();
    let topic = format!("bench/p2p/{}", i);

    let handle = thread::spawn(move || -> Result<()> {
      let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;

      rt.block_on(async {
        let (client, mut eventloop) = make_client(&h, port, &format!("pub-p2p-{}", i));

        tokio::spawn(async move {
          loop {
            if eventloop.poll().await.is_err() {
              break;
            }
          }
        });

        tokio::time::sleep(Duration::from_millis(500)).await;

        let payload = vec![b'x'; payload_size];
        let end_time = Instant::now() + Duration::from_secs(duration_secs - 1);
        let mut local_hist =
          Histogram::<u64>::new(3).context("Failed to create histogram")?;
        let mut count: usize = 0;

        while Instant::now() < end_time {
          let req_start = Instant::now();
          if client
            .publish(&topic, QoS::AtLeastOnce, false, payload.clone())
            .await
            .is_err()
          {
            break;
          }
          let latency = req_start.elapsed();
          local_hist
            .record(latency.as_micros() as u64)
            .context("Failed to record latency")?;
          count += 1;
        }

        let _ = client.disconnect().await;

        tx.send((local_hist, count))
          .map_err(|_| anyhow::anyhow!("Failed to send results"))?;
        Ok(())
      })
    });

    pub_handles.push(handle);
  }

  drop(tx);

  for h in pub_handles {
    h.join()
      .map_err(|_| anyhow::anyhow!("Publisher thread panicked"))??;
  }

  let mut total_received: usize = 0;
  for h in sub_handles {
    total_received += h
      .join()
      .map_err(|_| anyhow::anyhow!("Subscriber thread panicked"))??;
  }

  let actual_duration = start.elapsed();

  let mut total_published: usize = 0;
  let mut merged_hist =
    Histogram::<u64>::new(3).context("Failed to create merged histogram")?;

  for (hist, count) in rx.iter() {
    merged_hist
      .add(&hist)
      .context("Failed to merge histogram")?;
    total_published += count;
  }

  Ok(WorkloadResult {
    workload: Workload::P2p,
    published: total_published,
    received: total_received,
    duration: actual_duration,
    pub_throughput: total_published as f64 / actual_duration.as_secs_f64(),
    sub_throughput: total_received as f64 / actual_duration.as_secs_f64(),
    pub_latencies: merged_hist,
  })
}

fn run_burst(
  host: &str,
  port: u16,
  payload_size: usize,
  duration_secs: u64,
) -> Result<WorkloadResult> {
  let topic = "bench/burst".to_string();
  let start = Instant::now();
  let burst_size = 1000;
  let num_publishers = 10;
  let num_subscribers = 10;

  let mut sub_handles = Vec::new();
  for i in 0..num_subscribers {
    sub_handles.push(run_subscriber(
      host.to_string(),
      port,
      format!("sub-burst-{}", i),
      topic.clone(),
      duration_secs,
    ));
  }

  thread::sleep(Duration::from_secs(1));

  let (tx, rx) = mpsc::channel::<(Histogram<u64>, usize)>();
  let mut pub_handles = Vec::new();

  for i in 0..num_publishers {
    let tx = tx.clone();
    let h = host.to_string();
    let t = topic.clone();

    let handle = thread::spawn(move || -> Result<()> {
      let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;

      rt.block_on(async {
        let (client, mut eventloop) = make_client(&h, port, &format!("pub-burst-{}", i));

        tokio::spawn(async move {
          loop {
            if eventloop.poll().await.is_err() {
              break;
            }
          }
        });

        tokio::time::sleep(Duration::from_millis(500)).await;

        let payload = vec![b'x'; payload_size];
        let end_time = Instant::now() + Duration::from_secs(duration_secs - 1);
        let mut local_hist =
          Histogram::<u64>::new(3).context("Failed to create histogram")?;
        let mut count: usize = 0;

        while Instant::now() < end_time {
          for _ in 0..burst_size {
            let req_start = Instant::now();
            if client
              .publish(&t, QoS::AtLeastOnce, false, payload.clone())
              .await
              .is_err()
            {
              break;
            }
            let latency = req_start.elapsed();
            local_hist
              .record(latency.as_micros() as u64)
              .context("Failed to record latency")?;
            count += 1;
          }
          tokio::time::sleep(Duration::from_millis(100)).await;
        }

        let _ = client.disconnect().await;

        tx.send((local_hist, count))
          .map_err(|_| anyhow::anyhow!("Failed to send results"))?;
        Ok(())
      })
    });

    pub_handles.push(handle);
  }

  drop(tx);

  for h in pub_handles {
    h.join()
      .map_err(|_| anyhow::anyhow!("Publisher thread panicked"))??;
  }

  let mut total_received: usize = 0;
  for h in sub_handles {
    total_received += h
      .join()
      .map_err(|_| anyhow::anyhow!("Subscriber thread panicked"))??;
  }

  let actual_duration = start.elapsed();

  let mut total_published: usize = 0;
  let mut merged_hist =
    Histogram::<u64>::new(3).context("Failed to create merged histogram")?;

  for (hist, count) in rx.iter() {
    merged_hist
      .add(&hist)
      .context("Failed to merge histogram")?;
    total_published += count;
  }

  Ok(WorkloadResult {
    workload: Workload::Burst,
    published: total_published,
    received: total_received,
    duration: actual_duration,
    pub_throughput: total_published as f64 / actual_duration.as_secs_f64(),
    sub_throughput: total_received as f64 / actual_duration.as_secs_f64(),
    pub_latencies: merged_hist,
  })
}

fn main() -> Result<()> {
  let args = Args::parse();

  println!("MQTT Benchmark (rumqttd)");
  println!("  Broker: {}:{}", args.host, args.port);
  println!("  Payload: {} bytes", args.payload_size);
  println!("  Duration: {}s per workload", args.duration);
  println!();

  if args.csv {
    println!("system,runtime,workload,pub_throughput_mps,sub_throughput_mps,p50_ms,p95_ms,p99_ms,p999_ms,max_ms");
  }

  let workload_list: Vec<&str> = args.workloads.split(',').collect();

  for wl_name in workload_list {
    let wl = match Workload::from_str(wl_name) {
      Some(w) => w,
      None => {
        eprintln!("Unknown workload: {}", wl_name);
        continue;
      }
    };

    println!(
      "Running {} ({})...",
      wl.name(),
      wl.description()
    );

    let result = match wl {
      Workload::Fanout => run_fanout(&args.host, args.port, args.payload_size, args.duration)?,
      Workload::Fanin => run_fanin(&args.host, args.port, args.payload_size, args.duration)?,
      Workload::P2p => run_p2p(&args.host, args.port, args.payload_size, args.duration)?,
      Workload::Burst => run_burst(&args.host, args.port, args.payload_size, args.duration)?,
    };

    if args.csv {
      result.print_csv(&args.system, &args.runtime);
    } else {
      result.print_summary();
    }
  }

  Ok(())
}
