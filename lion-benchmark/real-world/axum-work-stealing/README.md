# axum-work-stealing

Where does a **thread-per-core** runtime (Lion) stand against a **multi-threaded
work-stealing** one (Tokio) when per-request CPU cost is highly variable? This
benchmark sweeps two axes at once — CPU utilisation and request-cost variability
— and reports where each design wins.

## What it models

A common web-service pattern: most requests are cheap, some trigger an expensive
CPU-bound operation (compression, hashing, report generation). A single endpoint
`GET /work?n=<iters>` runs `n` chained SHA-256 rounds **inline in the async
handler** (no `spawn_blocking`), so a heavy request occupies its executor
thread/core for the whole computation.

* **Tokio** (`ws-tokio`, `--cores N` worker threads): a heavy request pins one
  worker, but idle workers **steal** the light requests queued behind it.
* **Lion** (`ws-lion`, N per-core executors): each connection is accepted on a
  per-core `SO_REUSEPORT` listener and **stays there**. A heavy request pins its
  core; work queued behind it waits, and no other core can take it.

That is the naive framing the benchmark was built to test. The measured story is
more specific and, in the low-load regime, *inverts*: see **Findings** below.
The distinction that actually explains the low-load behaviour is not
"stealing vs no stealing" but **resident poller vs on-demand wakeup** — a
tunable implementation choice, not a property of either paradigm.

## Why the axes are utilisation and CV

Queueing theory says the two designs differ as N independent M/G/1 queues versus
a pooled M/G/N. The *waiting time* ratio is `rho*N / ErlangC(N, rho)`, which
grows without bound as utilisation falls — but the *response* time ratio tends to
1 there, because waiting is a vanishing part of a response that is mostly
service. The two limits fight, so the observable gap is non-monotonic in
utilisation and its peak moves with CV. Sweeping CV alone (at the saturation a
closed-loop generator forces) would only ever sample one slice of that surface.

## Method

**Open loop.** Load is offered at a constant rate with `vegeta`, set from a
calibrated service time: `lambda = rho * CORES / E[S]`. Utilisation is the
x-axis, so it has to be an input; under a closed-loop generator every connection
doing pure CPU work drives the server to saturation and rho becomes an output
pinned near 100%. Closed-loop load also suffers coordinated omission, which
understates the tail — and the headline metric here is p99.

**Not wrk2.** wrk2 was tried first and rejected on measurement. Against a server
whose true service time is ~4.4 ms, at 556 req/s:

| generator | p50 | p99 | note |
|---|---|---|---|
| sequential probe (idle server) | 8.6–10.2 ms | — | de-boosted ground truth |
| wrk2 `-t16 -c256` | 34.7 ms | 114.8 ms | sampling interval 135–152 ms |
| wrk2 `-t2 -c16` | 10.3 ms | 15.6 ms | sampling interval 24 ms |
| vegeta | 5.1 ms | 11.4 ms | rate 556.09 of 556 requested |

wrk2 issues in batches sized by an internally calibrated sampling interval, and
the recorded latency includes each request's wait inside that batch. The
inflation tracks the interval, lands on p99, and depends on threads and
connections — so per-cell tuning would vary the instrument along the x-axis.
(wrk2 also segfaulted at `-t16 -c64`.)

**Paired workload.** The per-request cost sequence is pre-generated to a file
(`bench/gen_targets.py`) and replayed identically by both runtimes and every
repetition, so the comparison is paired rather than two independent samples.
That is what makes 3 repetitions enough.

**Truncated, renormalised log-normal.** `n` is log-normal with a nominal CV,
rejected above `CAP*MEAN` so one request cannot hold a core for seconds. Plain
truncation would cut offered load by a CV-dependent amount (10.9% at CV=8,
CAP=100) and confound the CV sweep with a load sweep, so `bench/lognorm_mu.py`
solves for the mu whose *truncated* mean is exactly MEAN. Truncation still lowers
the achievable variance, so the plotted series are labelled with the **realized**
CV, not the nominal one — at CAP=400 nominal {1,2,4,8} give realized
{1.0, 2.0, 3.7, 5.4}.

## Reading the results: two confounds that are measured, not assumed

**DVFS.** On zoo-002 (EPYC 7702P, schedutil, no root to pin the governor) an
idle core sits at 1.50 GHz and a sustained-busy core reaches 3.31 GHz — a 2.21x
swing, which `scaling_max_freq` does not reveal (it reports 2.18 GHz; AMD core
performance boost goes above it). Consequences:

* `E[S]` is not a hardware constant. `calibrate.sh` measures it under *sustained*
  load; probing with one-shot requests measures the de-boosted clock and
  overstates it by ~2x.
* Raw latency curves can *fall* as utilisation rises — partly because higher load
  boosts the clock faster than queueing adds delay (the other part is unpark
  latency; see Findings §5). `plot.py` emits a clock-normalised figure alongside
  the raw one; the normalised figure is a derived quantity and never replaces the
  measurement.
* The arms can clock differently, since they distribute load differently.
  `plot.py` reports the per-cell clock ratio and warns above 5%.

**Per-core imbalance** is recorded for every cell (mean/min/max/stdev of
utilisation across the pinned cores). It is the direct mechanistic evidence:
thread-per-core leaves cores idle while others are backlogged; work stealing
keeps them uniform.

## Findings

Grid: 6 utilisations x 3 realized CVs x 2 runtimes x 3 repetitions, 8 cores,
open-loop vegeta, paired request streams. All 108 cells returned
`success_ratio = 1.0` (zero non-2xx, zero timeouts).

### 1. Throughput is equal; the whole story is in the tail

Achieved throughput matched the offered rate on both arms to within ±0.6% at
every utilisation. This is partly constructive (open-loop delivered rate = offered
rate while stable), but it also confirms neither arm dropped or queued-to-death.
Per-request CPU cost converges to within 1% by high load (Lion uses 9-12% less
CPU at low load, 0% by rho=0.9), so saturation capacity is also close. The
runtimes differ almost entirely in **p99**, not throughput.

### 2. The p99 ratio is non-monotonic and crosses over

`p99(Lion) / p99(Tokio)`, median of 3 reps:

| rho (util) | CV=1.0 | CV=3.8 | CV=5.3 |
|---|---|---|---|
| 0.2  | 0.84 | 0.38 | **0.37** |
| 0.35 | 0.94 | 1.15 | 0.70 |
| 0.5  | 1.20 | 2.15 | 1.24 |
| 0.65 | 1.62 | 2.62 | **3.35** |
| 0.8  | 2.56 | 3.03 | 3.32 |
| 0.9  | 2.89 | 2.52 | 2.52 |

**Lion wins at low utilisation** (by up to 2.7x), Tokio wins in the mid-to-high
range (peak 3.35x near rho 0.65-0.8), and the gap narrows again toward saturation.
Higher CV amplifies both sides without changing the direction. This is the
two-limits shape predicted in "Why the axes are utilisation and CV".

### 3. Mechanism: per-core imbalance (the Tokio-wins side)

Stdev of per-core utilisation, an order of magnitude apart with no overlap:

| | tokio | lion |
|---|---|---|
| range over all cells | 0.003–0.028 | 0.055–0.207 |

A heavy request pins one Lion core while others idle; the tail is set by the
*busiest* core, whose congestion factor `rho/(1-rho)` sits far up the convex
curve (e.g. at rho=0.65 the busiest core runs at ~0.89, congestion factor 7.9
versus 2.0 at the mean — a ~4x super-linear penalty). Tokio's stealing keeps the
cores uniform, so it stays at the mean. This is why Lion loses once utilisation is
high enough for imbalance to bite. Both arms track their own queueing model
(Lion ≈ 8 independent M/G/1; Tokio ≈ M/G/8), Lion within 0.7–1.2x, Tokio within
1.0–1.6x above rho=0.5.

### 4. Mechanism: unpark latency (the Lion-wins side)

The low-load crossover is *not* a Lion advantage in the pooling sense — with no
variance, pooling favours Tokio (CV=0 control, matched rate/concurrency: Tokio
p99 5.44 ms vs Lion 10.23 ms, because a request waits only if all 8 cores are
busy, ~744x less likely than one specific core being busy). What flips it under
high CV is that **Tokio pays a wakeup cost that Lion does not**:

* At rho=0.2 Tokio's workers are parked 70% of the time, averaging **14.9 ms per
  park**; by rho=0.9 that falls to 9% and 0.8 ms.
* A small request queued behind a heavy one must wait for a parked worker to be
  unparked before it can be stolen. Stealing *does* happen (~0.5 steals/request
  even at low load), so the tail is unpark *latency*, not absence of stealing.
* **Decisive test** (`ws-tokio-metrics --keepalive`): pin one busy yield-loop per
  worker so no worker ever parks (`parks` 6945 → 2), holding everything else
  fixed. Probe-request p99 collapses from **509 ms to 5.2 ms** — and it does so
  even though that run happened to sit at a *lower* clock (1.74 vs 3.35 GHz), so
  frequency cannot be the cause. Eliminating parking eliminates the low-load tail.

Lion has no unpark step: each core runs a **resident reactor** blocked in
`epoll_wait`, and a connection's events are handled on the core that owns them.
So the low-load difference is **resident poller vs on-demand wakeup**, a tunable
implementation choice — not intrinsic to thread-per-core vs work-stealing.

### 5. Why Tokio's raw p99 curve is U-shaped (falls, then rises)

The pre-trough *decline* has two components, both easing as utilisation rises,
of comparable size (CV=5.3, rho 0.2→0.65, raw p99 277→88 ms = 3.1x):

* **DVFS** (~half): high-CV arrivals are bursty, so at low load cores idle and
  de-boost (1.75 GHz), while at higher load they stay boosted (2.6 GHz). This
  component is **symmetric across arms** (confirmed: a fixed-size probe injected
  into the stream has the same latency on both) — it inflates absolute numbers but
  not the comparison.
* **Unpark** (~half): parking shrinks with load as in §4. This component is
  **Tokio-only**, and is the true source of the low-load crossover.

Past the trough (rho ≳ 0.65) queueing diverges with utilisation and stealing can
no longer hide it, so p99 rises on both arms; Tokio still leads by 2.5x at
rho=0.9 (it does *not* converge to Lion — throughput converges, tail latency does
not).

### 6. What was ruled out

The unpark conclusion in §4 survived elimination of every other candidate, each
by direct measurement: single-request path overhead (sequential probe, ratio
1.01 across idle gaps), a single blocked accept task (pre-warmed connection pool,
no change), too few workers (8→64, no change), stealing onto cold/de-boosted
cores (probe latency identical across arms), asymmetric DVFS between arms
(pegged-frequency probe identical), and parking *count* suppressing stealing
(counts are *lowest* at low load — it is park *duration* that matters).

### Scope / limitations

This is an **adversarial** workload for thread-per-core, and deliberately strips
out what thread-per-core is actually for. The handler is stateless pure CPU, so
data-sharding affinity — the real reason Seastar/ScyllaDB-style systems choose
thread-per-core — brings no benefit and stealing costs nothing to allow. CPU work
is placed **inline with no yield points**, disabling the cooperative scheduling
(task quotas, explicit yields, `spawn_blocking`) a production thread-per-core
system would use. And it sweeps to high utilisation, whereas latency-critical
deployments run with headroom. The honest headline is therefore not
"thread-per-core is worse" but: *a naively-written thread-per-core service — with
unbounded CPU work inline and no offload — pays 2.5–3.3x tail latency at mid-high
load under high cost variance, and wins at low load only because the compared
work-stealing runtime parks its idle workers.* Magnitudes are also
hardware-specific (the 2.2x DVFS swing, the ~15 ms park depth).

## Layout

```
axum-work-stealing/
  src/lib.rs                  # shared workload (the /work handler)
  src/bin/ws_tokio.rs         # Tokio arm  (multi-thread work-stealing)
  src/bin/ws_lion.rs          # Lion arm   (thread-per-core, pinned per core)
  src/bin/ws_tokio_metrics.rs # Tokio + RuntimeMetrics + --keepalive (parking test;
                              #   needs RUSTFLAGS="--cfg tokio_unstable")
  bench/lognorm_mu.py         # truncated-log-normal mu solver
  bench/gen_targets.py        # pre-generated paired request stream
  calibrate.sh                # measure SEC_PER_ITER under sustained load
  probe_idle.sh               # per-request service path with no queueing
  run.sh                      # the rho x CV sweep
  plot.py                     # figures + sanity checks
  sync.sh                     # push sources to the server (keeps results/)
```

## Run

Cross-machine is required: the load generator must not share CPU with the
server. Topology and credentials come from `../hosts.env` (gitignored).

```bash
./sync.sh                                    # push to SERVER_HOST
# on the server, once per host:
./calibrate.sh                               # -> results/calibration.env
CORES=8 RUNS=3 DURATION=20 ./run.sh          # -> results/<stamp>/work_stealing_raw.csv
../../micro/.venv/bin/python plot.py --data results/<stamp>
```

`run.sh` loops repetitions on the OUTSIDE, so the first pass is already a
complete grid — enough to check the shape before committing to the rest.

Output columns: `system,runtime,cores,mean,cv_nominal,cv_realized,rho_target,run,
rate_target,rate_achieved,throughput,util_measured,p50_ms,p90_ms,p99_ms,max_ms,
cpu_khz,percore_util_{mean,min,max,sd},requests,success_ratio,non_2xx,first_error`.

Unlike the other real-world benchmarks (which run both runtimes single-threaded
to compare per-core efficiency), this one is inherently **multi-core** — work
stealing only exists across cores.
