# Micro Benchmarks

Per-primitive microbenchmarks (paper section "Micro Benchmarks") that isolate the
runtime's own overhead — scheduler, waker, timer wheel, and I/O-readiness
dispatch — by comparing Lion against Tokio on three primitives:

| binary | primitive | what it stresses |
|---|---|---|
| `src/bin/micro_tcp_echo.rs` | TCP echo | socket readiness + wakeup dispatch |
| `src/bin/micro_timer.rs`    | timers   | timer registration / cancellation |
| `src/bin/micro_fs.rs`       | file I/O | async file read/write |

These run **locally** (loopback): the goal is to attribute any Lion-vs-Tokio gap
to the runtime, not the network (timers and file I/O have no network component;
running TCP echo over a real link would make it bandwidth/RTT-bound). End-to-end
behaviour over a real network is covered by the `../real-world/` experiments.

## Run

```bash
../setup.sh                        # one-time: plotting venv (matplotlib, numpy)
./run.sh                           # runs all three; per-run raw CSV under results/
python3 plot.py --data results/<stamp>-batch1   # render the figure from a run
```

Collected batches live under `results/<stamp>-batchN/` (raw CSVs +
`PROVENANCE.txt`); `../collect_paper_data.sh` produces them with the paper
protocol (10 s x 10 runs, `MT_THREADS="1 2 3"`). `ref-result/` is the
reference batch from the paper anchor machine (EPYC 7702P), with the rendered
figure — compare your run against it.

## Reading the timer results: the 5.0 M ops/s Tokio plateau

In the multi-thread timer panel, `tokio-part` (and Tokio generally, once CPU
stops being the bottleneck) flatlines at exactly **5.00 M ops/s regardless of
thread count**. This is not a scheduling-capacity ceiling and not a harness
artifact — it is Tokio's timer granularity, and the raw data proves it: at
≥ 2 threads tokio-part's p50 iteration latency pins to **1.999 ms** (p99
≈ 2.01 ms). Tokio's timer wheel has 1 ms resolution and rounds deadlines up,
so a `sleep(1ms)` registered mid-millisecond snaps to the next boundary and
fires on the tick after it — a deterministic 2 ms period. The benchmark's
throughput ceiling is therefore `load × 1000 / 2 = 10000 × 500 = 5.0 M ops/s`,
independent of threads. (Check it yourself: `ops ≈ load × 1000 / p50_ms` holds
row-by-row in `timer_mt_raw.csv`, for every runtime.)

Lion has no such quantum — its wheel fires within the clock's 1 ms granularity
of the true deadline — so its p50 varies continuously (≈ 1.2 ms at its best)
and its throughput reflects actual scheduling capacity, which is how it can
exceed Tokio's 5.0 M plateau. In this workload shape, timer *timeliness*
converts directly into *throughput*.
