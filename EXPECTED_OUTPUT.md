# What a run should look like

For each step: what it prints when it is working, which alarming-looking
messages are expected, and which messages mean the result is invalid. For what a
machine needs before running any of it, see [`REQUIREMENTS.md`](REQUIREMENTS.md);
for how to run an individual experiment, see its own `README.md` under
`lion-benchmark/`.

Every excerpt below is verbatim from a real run on a 6-core/12-thread desktop —
not the machine the reference dataset came from. **Compare the shape of the
output, not the numbers inside it.** Where a number is worth comparing, it is
called out.

---

## `./setup.sh` and `lion-benchmark/setup.sh`

Both are idempotent and print what they install or skip
(`cmake already installed.`, `Verus already installed at ... — skipping download`).

**Expected, not a problem.** The system-package steps *warn* instead of failing:
`Warning: failed to install <pkg>.`, `Warning: Dafny 3.4.0 download/unzip
failed; install manually.`, `Warning: .NET 6.0 install failed; install
manually.`, `Warning: failed to install scons; install manually.` A warning
means that dependency is missing and the experiment needing it will fail later —
read the tail of the output, not just the exit code.

`./setup.sh` ends with `Done. Try: cd lion-liveness && ./verify.sh`.

---

## `./ci.sh` — verifying the proofs

Verbose by design: ~30,000 lines, the great majority of them Verus `note:` lines
about automatically chosen quantifier triggers (~4,100 of them). They appear on a
fully passing run. Each crate's block ends in `PASSED`:

```
######################################################################
### [lion-reactor] verifying
######################################################################
...
verification results:: 206 verified, 0 errors
### [lion-reactor] PASSED
```

The counts to expect, in the order `ci.sh` runs them:

| crate | verified |
|---|---|
| lion-framework-spec | 8 |
| lion-executor-spec | 12 |
| lion-slab | 5 |
| lion-timer-wheel | 123 |
| lion-reactor-spec | 57 |
| lion-reactor | 206 |
| lion-executor | 99 |
| lion-utility | 90 |
| lion-liveness | 556 |

and the run ends with:

```
==========================================
All checks passed
==========================================
```

**Expected, not a problem:**

- `note: automatically chose triggers for this expression:` and the
  `note: trigger N of M:` lines under it — Verus explaining its trigger
  inference. Thousands of them.
- `warning: function 'WK' should have a snake case name` (likewise `UID`) —
  spec functions named after the paper's notation.
- `warning: private item shadows public glob re-export` in `lion-reactor`.
- **A crate whose build is already cached prints no `verification results::`
  line at all** — only `Verifying <crate>...` and `PASSED`. `verify.sh` drives
  `cargo-verus build`, so an up-to-date crate is not re-verified; touch its
  sources to force a full re-run. A second `./ci.sh` in a row is therefore much
  quieter than the first, and a missing count line is not a missing proof.

**Means the result is invalid:** any `error:` line, a crate block that does not
end in `PASSED`, or a non-zero exit. `ci.sh` stops at the first failing crate.

**Not a failure of the artifact:** a plain `cargo build` of `lion-liveness`
fails on an unresolved import of ghost-only spec-fn re-exports. `./verify.sh` /
`./ci.sh` is the gate — see the README.

---

## `correctness-stress/run.sh`

**Nine of the thirty cells are supposed to hang.** The claim this experiment
supports is that every bug-carrying Tokio release stalls permanently under the
stress workload while Lion does not, so a red `3/3 HANG` on those cells *is* the
result. Each of those runs costs the full 15 s timeout, so the run has long
quiet stretches.

```
==========================================
 Runtime Correctness Stress Test
 REPS=3  timeout=15s per run
==========================================
Building tokio-1.21...
    Finished `release` profile [optimized] target(s) in 4.58s
...

Test            tokio-1.21          tokio-1.42          tokio-1.44          tokio-latest        lion
─────────────────────────────────────────────────────────────────────────────────────────────────────
current         3/3 HANG            0/3 (3039ms)        0/3 (3040ms)        0/3 (3037ms)        0/3 (3058ms)
multi           0/3 (3025ms)        3/3 HANG            3/3 HANG            0/3 (3025ms)        0/3 (3060ms)
```

Green `0/REPS (Nms)` = every repetition completed, with the median completion
time; red `N/REPS HANG` = that many repetitions hit the timeout. **This matrix is
the comparable result** — it reproduces cell for cell across machines:
tokio-1.21 hangs on `current` (issue #5020); tokio-1.42 and tokio-1.44 hang on
`multi` (issue #7209); tokio-latest and Lion pass both. The completion times
inside the green cells are machine-dependent.

Then the heat-map input is captured:

```
Capturing heatmap event log (lion, current) -> events.tsv
Loaded 20440 events
Saved: .../stress_heatmap.pdf (20,440 events, 61 bins x 5 groups)
stress_heatmap.pdf rendered
```

The heat map illustrates one Lion run; it is not a measurement, and its exact
appearance depends on the machine and the workload version. Nothing about the
claim in the paper rests on it.

**Expected, not a problem:** the red cells and the ~15 s of apparent inactivity
each costs; `WARNING: heatmap capture run did not complete`; `NOTE: plotting venv
missing — run lion-benchmark/setup.sh` (only the PDF is skipped, `events.tsv` is
kept).

**Worth reporting:** a yellow `N/REPS ERR` cell — the binary exited non-zero,
which is neither a pass nor a hang.

Raw per-run records go to `results.jsonl`, one JSON object per run.

---

## `micro/run.sh`

```
=========================================
  Micro Benchmark — Local Run
  Duration: 10s x 10 runs
  Cores:    12
=========================================
### (a) TIMER: single-thread ###
  tokio      load=1000   ops/s=458780
  tokio      load=5000   ops/s=2400365
  ...
```

Five panels in order: (a) timer single-thread, (d) timer multi-thread, (b) TCP
echo single-thread, (e) TCP echo multi-thread, (c) filesystem blocking-pool
scaling. 480 runs, ~82 min. Each prints a mean per cell as it finishes and
appends every individual run to `results/local/*_raw.csv` — five files, 480 data
rows in total, which is the completeness check.

**Expected, not a problem:**

- `warning: 'lion-micro-bench' (bin "micro-timer") generated 1 warning` during
  the build.
- **Memory.** The Lion timer cells grow to ~9.5 GB resident over a 10 s run
  (~0.95 GB/s; Tokio at the same configuration stays at 9 MB). This is expected
  — see `REQUIREMENTS.md` §4 — and it is why 16 GB is the recommended minimum.

**Worth investigating:** `!! skipped <runtime> load=... run=N` on stderr — a run
failed three times and was dropped, leaving that cell short of 10 samples. A
healthy run prints none of these.

---

## The real-world benchmarks (`real-world/*/run.sh`)

Each one states its topology before it measures anything, then builds both
runtimes' binaries, then prints one CSV line per run and a trimmed-mean summary:

```
[bench] server=127.0.0.1 client=127.0.0.1 out=.../results/<stamp>-paper
== build ==
    Finished `release` profile [optimized] target(s) in 32.04s
== run (server=127.0.0.1 client=127.0.0.1 30s x 10, conns: 50 200) ==
pingora,tokio,conns50,50,1,136651.79,364.88us
pingora,lion,conns50,50,1,136110.08,366.35us
...
== summary ==
system,runtime,workload,metric,mean,stddev,unit
pingora,lion,conns50,throughput,135950.85,262.90,ops/s
pingora,tokio,conns50,throughput,136492.72,127.38,ops/s
```

**Read the topology lines.** `[bench] no real-world/hosts.env — running fully
local` means you are getting a single-machine smoke, not the paper's
cross-machine measurement, for rumqtt and axum. `[bench] server=X client=Y`
reports what `hosts.env` and the environment resolved to, and the `== run
(server=... client=...) ==` line states what the run actually used. Pingora is
measured on a single host by design and says so explicitly when a cluster is
configured:
`[bench] pingora is measured on a single host — overriding the above to ...`.

Runs are interleaved A-B (runtime inner, run outer) with the server restarted
between arms, so tokio and lion lines alternate throughout rather than arriving
in blocks.

**Means the result is invalid** — all of these abort rather than record a
number, so a completed run cannot be silently wrong in these ways:

- `FATAL: wrk script <path> missing` / `FATAL: wrk could not load <path> on <host>`
- `FATAL: wrk failed locally` / `FATAL: wrk failed on client <host>`
- `FATAL: '<tool>' not found on client <host>` — run `lion-benchmark/setup.sh`
  on the client host too
- `the client is not receiving file bodies; the number above measures errors.`
  (axum) — the request rate is real but the responses were empty, so it is not
  throughput

**Expected, not a problem:** `NOTE: You need to provide rumqttd config files.`
during rumqtt setup; the rumqtt client runs four workloads back to back per
invocation (`W-Fanout`, `W-Fanin`, `W-P2P`, `W-Burst`) while the paper reports
three of them.

---

## `ironfleet/run.sh`

```
== topology: replicas and client both on 127.0.0.1 (LOCAL — not the paper's
   cross-machine setup; set SERVER_HOST/CLIENT_HOST in real-world/hosts.env for that) ==
== build Lion I/O cdylib ==
    Finished `release` profile [optimized] target(s) in 6.42s
== build C# IronRSL app (scons --no-verify) ==
scons: `bin/IronRSLCounterClient.dll' is up to date.
scons: done building targets.
== generate certs (3 replicas @ 127.0.0.1:4001 4002 4003) ==
== start 3 servers (RUNTIME=lion lion=true, CONFIG=unpin) ==
   waiting for [[READY]] s1 s2 s3
== run client (nthreads=2 duration=5s) from 127.0.0.1 ==
== results (lion / unpin) ==
  Throughput : 2870 req/s   (14348 reqs / 5s)
  Avg latency: 0.24 ms   p50 0.19  p99 0.51
  Peak server CPU (leader proxy): 0%
  raw: .../results/lion_unpin.reqlog
```

The topology line comes first and is unambiguous — a local run cannot be
mistaken for a cross-machine one afterwards. `run_all.sh` drives all four cells
(`{lion,csharp} × {unpin,1core}`) in one command.

**Expected, not a problem:** `scons: 'bin/....dll' is up to date.` on a rebuild.

**Means the result is invalid:**

- `no #req lines parsed; see <path>.reqlog` — the client produced no
  measurements. Open the `.reqlog`: a single line such as `cd: ...: No such file
  or directory` means the client host could not run the app.
- `FATAL: replica(s) never printed [[READY]] — aborting instead of running the client`
- `FATAL: no dotnet on client <host>` — the IronRSL client is a .NET app; run
  `SETUP_IRONFLEET=1 lion-benchmark/setup.sh` there too
- `build incomplete: bin/<dll>.dll missing — full scons output follows`
