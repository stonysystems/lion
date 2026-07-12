# Evaluation Audit Checklist — do the experiments faithfully reflect their purpose?

> Scope: everything under `lion-benchmark/` that feeds a paper claim — the three
> real-world apps (`real-world/{axum,pingora,rumqtt}`), the micro suite
> (`micro/`), IronFleet (`ironfleet/`), and the correctness-stress suite
> (`correctness-stress/`), plus the orchestrator `collect_paper_data.sh`.
>
> Purpose: a benchmark can be green, reproducible, and statistically clean and
> STILL not measure what the paper says it measures. The three failure classes
> this checklist targets:
> **(A) substitution failure** — the "Lion" arm does not actually run on Lion
> (silent fallback to Tokio, wrong binary, wrong flag, unloaded cdylib);
> **(B) identity failure** — the Lion that is benchmarked is not the Lion that
> was verified (facade bypasses the verified crates, benchmark-only patches);
> **(C) purpose failure** — the workload/metric doesn't exercise or capture the
> thing the claim is about (runtime overhead swamped by app logic, warmup
> artifacts, unequal baselines).
> Provenance/recomputability of the *numbers* was a prior benchmark
> audit's subject (R1–R5 regeneration campaign); this checklist is about the
> *meaning* of the experiments. Items give "why it matters" + "how to check".

---

## §0. Mechanical gate (greppable; run first)

- [ ] **Lion-arm sources are Tokio-free on the measured path**:
      `grep -rn "tokio::" real-world/*/src/lion-*/src/` — every hit must be
      trait-level plumbing (`AsyncRead/Write` ext traits, service traits), never
      `tokio::spawn`, `tokio::net`, `tokio::time`, `tokio::fs`, or a Tokio
      runtime builder. (Current expected state: axum's lion arm has zero
      `tokio::` calls in `main.rs`; the driver is `lion::runtime::Builder` +
      `lion::net::TcpListener` + `lion::spawn` + `lion::fs::read`.)
- [ ] **Justify every Tokio feature in every Lion-arm `Cargo.toml`**: e.g.
      `real-world/axum/src/lion-axum/Cargo.toml` enables
      `tokio = { features = ["sync","macros","io-util","signal","fs","rt","time"] }`.
      Each feature needs a one-line reason (which dependency demands it —
      hyper-util's `tokio` feature, axum's trait bounds, …). `rt`/`time`/`fs`
      in a LION arm are red flags until explained: they make it *possible* for a
      library to silently construct a Tokio runtime inside the measured process.
- [ ] **The `lion` facade is a re-export shim**: `grep -rn "tokio::" lion/src/`
      — expected: a single trait re-export (`tokio::io::*`). Any executor/
      reactor/timer/fs functionality imported from Tokio into the facade is a
      substitution failure. Also justify the facade's own Tokio features
      (`sync`,`macros`,`io-util`,`rt` in `lion/Cargo.toml`) the same way.
- [ ] **Facade wiring**: `lion/Cargo.toml` depends on `lion-executor`,
      `lion-reactor`, `lion-utility` (verified crates) + `lion-macro`. Confirm
      `cargo tree -p lion` shows them, and confirm each public facade module
      (`net`, `time`, `sync`, `fs`, `spawn`, `runtime`) resolves to a verified
      crate (or disclosed glue), not to Tokio or a private reimplementation.
- [ ] **Per-run raw data retained** (repo policy: per-run raw retained): every result dir has
      per-run `*_raw.csv` / `results.jsonl`, and summaries (trim-2 mean ± std)
      are recomputable from the raw rows — spot-recompute one table.
- [ ] **PROVENANCE.txt present** in every `results/<stamp>-*/` batch (commit,
      host, CPU, kernel, governor, RTT, protocol) — `collect_paper_data.sh`
      writes it; hand-made batches must too.
- [ ] `./ci.sh` green at the benchmarked commit (the PROVENANCE commit), so the
      benchmarked Lion is a *verified* Lion (see §2).

---

## §1. Substitution authenticity — the "Lion" arm really runs on Lion

> Core risk (A): the headline claim is "we replaced the runtime with Lion"; if
> any measured path still runs on the baseline runtime, the comparison is
> meaningless in the flattering direction.

### 1.1 Real-world apps (axum / pingora / rumqtt)
- [ ] For each app, read the lion-arm entrypoint and trace the measured request
      path end to end: accept loop, per-connection tasks, timers, file reads.
      Every `spawn`/`sleep`/socket/file op on that path must be `lion::*`.
      The Tokio twin (`src/tokio-<app>/`) must be the mirror image.
- [ ] **Runtime canary (build-independent)**: while the lion arm is under load,
      inspect its threads (`ls /proc/<pid>/task/*/comm` or `ps -T`). A Tokio
      multi-thread runtime names workers `tokio-runtime-w*`; the lion arm should
      show the Lion current-thread runtime's thread(s) only. Do the inverse
      check on the Tokio arm. Record the observation in the result dir.
- [ ] **Feature-unification hazard**: `cargo tree -e features -p lion-axum-fileserver`
      (and the other lion arms) — confirm no dependency turns on Tokio's
      `rt-multi-thread`/`net` in the lion arm via feature unification. A
      library that quietly does `tokio::runtime::Handle::try_current()` with a
      fallback runtime would run its I/O on Tokio while the app "runs on Lion".
- [ ] **Single-threaded parity claim**: the paper says both runtimes run
      current-thread. Verify the Tokio arm actually builds
      `new_current_thread` (not `#[tokio::main]`'s default multi-thread), and
      the lion arm's `new_current_thread` is the same scheduling shape.

### 1.2 IronFleet (C# + Lion cdylib)
- [ ] The `lion=true` server flag must be *load-bearing and fail-loud*: confirm
      `IoNative.cs`'s `CreateWithLion` path P/Invokes `ironfleet_io_lion` and
      that a missing/unloadable `libironfleet_io_lion.so` **crashes** the run
      rather than silently falling back to the C# `IoScheduler` (a silent
      fallback would benchmark C# against C# and report it as Lion).
      Check `run.sh` passes the flag iff `RUNTIME=lion`, and that logs from a
      lion run contain a Lion-side marker (e.g. the cdylib's startup line).
- [ ] The cdylib itself runs a **Lion** current-thread runtime (`lion::net` +
      `lion::spawn` + `lion::time`): `grep -rn "tokio::" ironfleet/lion-io/src/`
      — expected: ext-trait imports only (its README discloses tokio's
      `AsyncRead/Write` ext traits over Lion stream halves).
- [ ] **Protocol-core invariance**: the Dafny-generated Paxos core is byte-
      identical between the two configurations (the claim is "only the I/O layer
      differs"). Diff the C# sources used by the two arms; the only deltas
      allowed are the disclosed ones — I/O selection (`LionIoScheduler.cs` /
      `IoNative.cs`), the two scheduling constants (adjusted **identically** for
      both arms — verify identical), and the TCP_NODELAY baseline fix
      (`tcp_nodelay_fix.md`, a fairness fix FOR the baseline).

### 1.3 Correctness-stress
- [ ] The suite's design claim: `shared/workload.rs` compiled **unchanged**
      against each runtime, per-runtime crates differing only in what `rt`
      renames to. Verify: `diff` the per-runtime crates' `src/` (should be
      trivial shims) and confirm `lion/Cargo.toml`'s `rt` is the `lion` facade
      while `tokio-*/Cargo.toml` pin the exact advertised Tokio versions
      (1.21 / 1.42 / 1.44 / latest).
- [ ] The C ports (`libevent-tests/`, `libuv-tests/`) claim "the same test
      design ported to C" — check each `summary.md` maps its scenarios 1:1 to
      the Rust workload's patterns, and any scenario that could NOT be ported is
      listed, not silently dropped.

---

## §2. Identity — the benchmarked Lion is the verified Lion

> Core risk (B): the paper's story is "a *formally verified* runtime at Tokio-
> class performance". That story dies if the benchmarked code differs from the
> verified code.

- [ ] The lion arms consume the verified crates **by path** (`lion = { path = … }`
      → `lion-executor`/`lion-reactor`/`lion-utility` in this same checkout):
      no crates.io versions, no git pins to another revision, no `[patch]`
      redirections. `cargo tree` from each lion arm should terminate in this
      repo's crate paths.
- [ ] **No benchmark-only patches to verified crates**: at the PROVENANCE
      commit, `git status`/`git diff` clean over `lion-*/src` during collection
      (`collect_paper_data.sh` records the commit; confirm the recorded commit
      verifies green with `./ci.sh`). Any perf tweak must land in the verified
      crates and re-verify BEFORE being benchmarked (the real-world README's
      acceptance rule states exactly this: fix the implementation, never weaken
      the proofs).
- [ ] The facade layers (`lion/`, `lion-macro/`, `lion-utility`'s trusted glue)
      are OUTSIDE the verified perimeter — the paper/report must not describe
      the benchmarked binary as "fully verified"; the honest phrasing is
      "routes through the verified kernels via the disclosed trusted glue"
      (TCB_and_limitations.md). Check the paper's wording against this.
- [ ] Version skew: the benchmark deps (`axum 0.8`, `hyper 1`, tokio `1.x`
      resolved lockfile version, .NET 6.0, Dafny 3.4.0) match what the paper's
      setup section states; `Cargo.lock` (or the PROVENANCE record) pins the
      Tokio version the baseline arm actually ran.

---

## §3. Workload–purpose alignment — each experiment exercises what it claims

> Core risk (C): the numbers are real but the workload doesn't stress the
> replaced component, so the claim "Lion performs like Tokio" is untested even
> though the table says 97–111%.

- [ ] **Micro** claims to isolate runtime overhead (scheduler/waker/timer
      wheel/readiness dispatch). Confirm each binary's inner loop is dominated
      by the primitive it names (tcp echo = readiness+wakeup, timer =
      register/cancel, fs = async read/write) and runs on loopback (its stated
      reason: exclude network variance). Any workload change since the paper's
      anchor batch invalidates `ref-result/` comparisons — diff `src/bin/*.rs`
      against the anchor batch's recorded commit.
- [ ] **Real-world** claims end-to-end behaviour over a real link: confirm the
      cross-machine deployment (server zoo-001 / client zoo-004, `hosts.env`)
      is what the paper table reports, with axum's localhost deployment
      reported as its own row (the dual-deployment protocol), never mixed.
- [ ] **IronFleet** claims "improving a verified system with Lion async I/O".
      The C# Paxos busy-loop pins ~100% of a core in BOTH arms — so
      throughput/latency deltas are attributable to the I/O layer, and CPU
      claims must be phrased as *leader total* (~140%) not "Lion uses X%".
      Check the paper's sentence-level phrasing against `run.sh`'s parse.
- [ ] **Stress** claims "keeps every task live under ordinary concurrent
      usage". The oracle is timeout-as-hang: confirm the timeout is generous
      relative to the workload's natural completion (a too-tight timeout
      manufactures hangs; check the margin), that the SAME timeout applies to
      every runtime, and that `tokio-latest` is honestly labeled a fixed
      version (negative control), not "latest forever".
- [ ] For every paper claim of the shape "Lion is within X% of Tokio": the
      workload behind it must actually bottleneck on the runtime. If a config
      is bandwidth/RTT-bound or disk-bound, parity there is trivial — the
      paper must not present it as evidence of runtime parity (check which
      configs the parity range is computed over).

---

## §4. Comparison fairness — the baseline is not handicapped (or favored)

- [ ] **Build parity**: both arms `--release` with the same profile — compare
      `[profile.release]` (lion-axum sets `opt-level 3, lto, codegen-units 1`;
      the Tokio twin must match exactly). Same for pingora/rumqtt and the
      stress crates.
- [ ] **Config parity**: same worker model (current-thread vs current-thread),
      same listen backlog / buffer sizes / file set / connection counts; diff
      the two arms' CLI args in `run.sh`.
- [ ] **Baseline hygiene fixes are symmetric**: TCP_NODELAY was fixed FOR the
      C# baseline (`tcp_nodelay_fix.md`) — confirm both arms now run with
      Nagle disabled; the two IronFleet scheduling constants are identical in
      both arms.
- [ ] **Interleaved A-B protocol**: `collect_paper_data.sh` claims interleaved
      runs (defends against thermal/noise drift favoring whichever arm runs
      second). Confirm the runners actually alternate arms within a batch
      rather than running 10×Lion then 10×Tokio.
- [ ] **Warmup handling is symmetric**: the CPU-peak exporter skips the first
      5 lifetime-average samples (a .NET startup-burst artifact). Confirm the
      skip applies to BOTH arms (the Rust side too), and that throughput
      windows likewise exclude/include warmup identically.
- [ ] **Environment parity**: same hosts, same governor, same NUMA/pinning
      (`CONFIG=unpin|1core` applied to both arms), background load absent —
      PROVENANCE captures governor/host; spot-check one batch.

---

## §5. Metric & statistics faithfulness

- [ ] Each paper metric is measured where the claim implies: throughput at the
      **client** (load generator side), latency percentiles from client
      timestamps, CPU from the server process — confirm the parse in each
      `run.sh` matches the paper's table caption.
- [ ] The shared statistic is trim-2 mean ± std over 10 runs: confirm every
      summary was computed post-hoc from raw rows (never inline-discarded,
      repo policy) and the paper states the same aggregation it uses.
- [ ] The "97–111%" style parity envelope: recompute it from `ref-result/` raw
      data and confirm the paper's range quotes the same set of (app, config)
      cells — no cherry-picking cells into the envelope.
- [ ] Plot faithfulness: `plot.py` axes (linear/log), error bars = std of the
      same trimmed set, and no silent unit changes (req/s vs msg/s vs KB/s per
      app as the README table declares).

---

## §6. Claim ↔ artifact mapping & known debts

- [ ] Build the table: every paper number/figure → generating script + exact
      result dir (`ref-result/` or `ref-result-2/`) + PROVENANCE commit. Any
      paper number with no on-disk generating artifact is a blocker (this was
      the prior benchmark audit's headline finding; the R1–R5
      full-regeneration decision covers it — confirm executed before release).
- [ ] **Known debt**: micro figures (a)(d) must come from post-fix code — the
      `scan_wheel_min` late-fire bug inflated pre-fix timer numbers by ~25%
      (baselines/tcb-reduction/05-final/). Confirm the paper's figures are
      regenerated from a post-fix PROVENANCE commit, and that `ref-result/`
      batches predating the fix are either regenerated or clearly marked
      pre-fix and unused by the paper.
- [ ] `ref-result-2/` is the clean-clone validation batch — confirm it agrees
      with `ref-result/` within noise for every table the paper cites (any
      disagreement is a reproducibility finding, not a rounding note).
- [ ] The real-world acceptance rule (verified Lion must not regress beyond
      the paper's measured gap) has a recorded pass for the current code:
      compare the latest `results/*/COMPARISON.md` against `ref_result/`.
- [ ] Expected run cost documented (~4h full campaign, hosts.env required, no
      local default for real-world) so an external reviewer can actually
      reproduce — README section must match `collect_paper_data.sh` behavior.

---

## One-shot quick self-check

No script covers this yet; the §0 items are directly greppable:

```bash
grep -rn "tokio::" lion-benchmark/real-world/*/src/lion-*/src/ lion-benchmark/ironfleet/lion-io/src/ lion/src/
grep -rn "features" lion-benchmark/real-world/*/src/lion-*/Cargo.toml lion/Cargo.toml
find lion-benchmark -name PROVENANCE.txt | head
```

The runtime canary (§1.1), protocol-core diff (§1.2), and claim↔artifact table
(§6) are manual.
