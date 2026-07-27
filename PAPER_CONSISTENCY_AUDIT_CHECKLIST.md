# Paper Consistency Audit Checklist

> Scope: consistency between the paper (`lion-paper`) and the artifacts in this
> repository that the paper's claims rest on. Each section pairs one class of
> paper claims with its ground-truth source in the repo and gives a concrete
> verification procedure. This file complements PROOF_AUDIT_CHECKLIST.md (proof
> soundness) and EVALUATION_AUDIT_CHECKLIST.md (benchmark numbers): those audit
> the artifacts themselves; this one audits whether the *prose* faithfully
> reports them.
>
> Purpose: prose drifts silently. A table cell edited for style, a number
> rounded for readability, or a mechanism "clarified" from memory can turn an
> accurate summary into an over-claim with no build or CI signal. Every item
> here is checkable against a file in this repo or a cited public source, so an
> audit run needs no access to the authors' recollection.
>
> How to use: work through each section item by item. For every discrepancy,
> record it with the exact paper location (file:line or issue row) and the
> contradicting source quote, then either fix the paper or document why the
> paper's wording is a deliberate, defensible gloss. An item passes only when
> every claim in its scope is either directly sourced or explicitly marked in
> the paper as the authors' own inference.

---

## §1. Appendix bug study vs. original issues

> Paper location: `lion-paper/sections/appendix.tex` (the per-issue longtables:
> Tokio, libevent, libuv). Ground truth: `assets/downloaded_issues/<project>/issue-<N>.json`
> (GitHub issue exports: `title`, `body`, `comments[].body`, timestamps), plus
> the fix PRs cited in the root-cause cells — the issue thread alone often
> contains no diagnosis, so the PR must be fetched from GitHub and read.
>
> Why it matters: this table is the sole substantiation of the main text's
> "confirmed liveness bugs" claim. A reviewer who spot-checks one row against
> the public thread and finds an unsupported clause will distrust the entire
> study.

- [ ] **Coverage is 1:1.** Every issue row in the appendix has exactly one JSON
      file under `assets/downloaded_issues/`, and vice versa — no row without a
      downloaded source, no downloaded issue silently dropped from the table.
      Cross-check the main text's issue counts against the table (e.g.
      "N more confirmed liveness bugs" = table rows minus issues discussed in
      the main text).
- [ ] **Symptom cells report what the reporter reported.** Compare each Symptom
      cell against the issue title and the reporter's observed behavior — not
      against the maintainer's generalized mechanism. Flag any symptom that
      states a failure branch the reporter explicitly did not observe, names
      the wrong task/side as the one that hangs, or adds unstated qualifiers
      ("repeatedly", "always", "never") absent from the thread.
- [ ] **Root-cause cells trace to a diagnosis, not a reconstruction.** For each
      causal clause, find the supporting statement in the issue thread or the
      cited fix PR (description, diff, or linked follow-up issue). Clauses that
      are the paper's own elaboration must be direction-neutral and consistent
      with the fixed code's actual control flow — do not assign roles (which
      task clears/starves, what triggers the path) beyond what the sources
      state. Where the thread never localized the bug, the cell must say so
      rather than present a conjecture as diagnosis.
- [ ] **Module attribution matches the fix location.** The Module column should
      agree with where the fix landed (or the issue labels), not just with the
      API the reporter used. For libevent/libuv rows, keep the caveat paragraphs
      about their looser modularity in sync with the labels actually used.
- [ ] **Quantitative claims are exact.** Any number attached to an issue in the
      paper (thresholds like "128 or more", counter widths, commit/review
      counts, open-duration claims) must be recomputed from the JSON timestamps
      or the cited PR's metadata. Prefer exact figures over rounded-up
      narrative ones.
- [ ] **The same issue tells the same story everywhere.** An issue discussed in
      multiple sections (appendix table, background, discussion, verification)
      must carry one consistent epistemic status: if the appendix says the root
      cause was never localized, no other section may cite that root cause as
      established fact — speculation must be marked as the authors' conjecture
      wherever it appears.

---

## §2. IronFleet integration experiment vs. `lion-benchmark/ironfleet`

> Paper location: `lion-paper/sections/lion_evaluation.tex`, subsection
> "Improving Verified Systems with Async I/O" (`\label{sec:ironfleet}`,
> Table `tab:ironfleet`). Ground truth: `lion-benchmark/ironfleet/` —
> `lion-io/` (the Rust cdylib I/O layer), `ironrsl-app/` (the C# IronRSL app;
> baseline in `src/Dafny/Distributed/Common/Native/IoFramework.cs`), `run.sh`
> (orchestration and knobs), `ref-2/` (raw per-rep `.reqlog`/`.cpulog`/`.arm`
> files, one triple per {runtime}×{config}×rep), `export_table.py` (recomputes
> the paper table from raw files), and the directory README's Measurement notes.
>
> Why it matters: this experiment supports the paper's headline claim that Lion
> improves an *existing verified system*. Its prose makes architecture
> assertions about code the authors did not write (the C# IoFramework) and
> quantitative claims that must reproduce from archived raw data — both easy to
> drift as the text is polished.

- [ ] **Architecture description matches the code.** Verify in source, not from
      the README: the integration is a Rust `cdylib` loaded into the C# process
      via P/Invoke with the stated FFI surface; the C# baseline really creates
      three dedicated threads per TCP connection (name them in
      `IoFramework.cs`) and the "7+ threads per replica in a 3-node cluster"
      arithmetic follows; "every message crosses 2--3 thread boundaries, each
      involving a queue operation and a kernel thread wake" is traceable
      through the baseline's send/receive paths; the Paxos main loop is a busy
      `while(true)` spin in both arms; on the Lion side, readers, writers, and
      connection management run as async tasks. Flag any load-bearing design
      fact the paper omits that changes interpretation (e.g. the single
      background OS thread owning a current-thread runtime, and the
      C#-to-runtime handoff via thread-safe channels — the paper's "lightweight
      async tasks" wording must not imply the C# thread itself runs async).
- [ ] **Mechanism constants exist in code.** "After 64 consecutive empty
      receives, the receive call blocks for up to 50 ms on the inbound
      channel" — locate both constants (64, 50 ms) in `lion-io/src/` and
      confirm the trigger condition (consecutive empty receives) and the
      blocked-on object (inbound channel) are as stated.
- [ ] **"Unmodified verified core" is qualified consistently.** The repo
      discloses two protocol-constant changes applied identically to both arms
      (`max_batch_size` 32→1 — the paper's "no request batching" — and
      `max_log_length` 7→1000). Check the paper's "verified Paxos core
      unmodified" / "core logic is identical in both configurations" wording
      remains defensible given these, and that measurement caveats affecting
      absolute numbers (client workers sleep 3 s inside the measured window;
      peak CPU is a process-lifetime `ps` average sampled per second, warm-up
      samples dropped) either do not touch any paper claim or are disclosed
      (the paper's "we sample CPU per process, not per thread" sentence must
      stay true of how `.cpulog` is produced).
- [ ] **Workload parameters match the harness.** 3 replicas, remote client, 2
      concurrent connections, no batching, 30 s duration, unpinned vs
      one-core-per-replica pinning — check against `run.sh` knobs
      (`NTHREADS`, `DURATION`, `CONFIG=unpin|1core`) and the `ref-2/` file
      naming (`{lion,csharp}_{unpin,1core}.rN.*`); confirm the client is
      remote in the reference topology.
- [ ] **Every table cell recomputes from `ref-2`.** Run
      `./export_table.py ref-2` (trim-2-over-reps is the project-wide rule;
      pass `--duration` matching the paper) and compare all 12 cells of
      `tab:ironfleet` (throughput, avg latency, peak leader CPU × Lion/C# ×
      unpin/1-core). Any cell that does not match must be traced to a
      deliberate, documented rounding — not silently accepted.
- [ ] **Derived prose figures recompute from the table.** "2.0× the
      throughput", "only 27% CPU of the C# backend (138% vs. 505%)", "a 6.1×
      gap" — recompute each ratio from the table cells and check the rounding
      direction never favors the paper's claim.
- [ ] **Attribution claims stay within the measurement's power.** "Lion's 138%
      is dominated by the Dafny-generated Paxos busy loop" and "505% reflects
      the overhead of 7+ threads" are interpretations; per-process CPU sampling
      cannot apportion blame between threads. Confirm the paper hedges these as
      interpretation (and keeps the per-process-sampling caveat) rather than
      presenting a per-thread breakdown it does not have.

---

## §3. Mutation study vs. `mutation-test/`

> Paper location: `lion-paper/sections/lion_evaluation.tex`, subsection
> "Proof Sensitivity to Broken Logic" (`\label{sec:mutation}`). Ground truth:
> `mutation-test/` — `mutants/` and `patches/` (the mutant definitions),
> `run.sh` (apply–build–verify–revert harness), `RESULTS.md` and `results/`
> (recorded outcomes, including the baseline matrix M01--M10 CAUGHT,
> C1/C3 SURVIVED, C2 CAUGHT), and the provenance notes recording that the
> mutant list is LLM-generated and was fixed before execution.
>
> Why it matters: this section's argument is methodological — the proofs are
> claimed to be non-vacuous *because* of the experimental discipline (build
> gate, isolation, pre-registered list, controls). A reviewer who finds one
> undocumented deviation between the described discipline and the harness will
> discount the whole result. Unlike §2, most claims here are re-runnable:
> prefer re-execution over trusting archived outcomes when auditing.

- [ ] **Mutant census and chain mapping.** The paper's counts — ten
      verified-region mutants covering all four links (four in timer fire, two
      in the wakeup drain, three in FIFO order, one in the poll loop) plus
      three trusted-code controls — must match the mutant definitions:
      Fire = M01--M04 (timer wheel), Drain = M07/M10, FIFO = M06/M08/M09,
      Poll = M05, Controls = C1--C3. Verify each mutant's patch actually
      touches the module its link implies (file paths in `RESULTS.md`), and
      that no mutant in the repo is silently omitted from the paper's census.
- [ ] **The build gate holds for every mutant.** The paper claims every mutant
      still passes a plain `cargo build`, so a verifier rejection is a violated
      proof obligation, not a type error. Check the recorded build column is
      OK for all thirteen, and spot-re-run at least one mutant through
      `run.sh` to confirm the harness really builds before verifying (a
      harness that verifies first would silently weaken this claim).
- [ ] **Discipline claims match the harness.** "Applied, built, verified, and
      reverted in isolation" — confirm `run.sh` applies one patch at a time
      and restores a clean tree between mutants (no compounding). "The list
      was fixed before any of them was run" and the LLM provenance — confirm
      both are recorded in the repo's provenance notes, not just asserted in
      the paper.
- [ ] **Every catch is on-topic.** "All ten are rejected, each by the invariant
      governing the link it breaks" — for each M-mutant, the recorded verifier
      error must point into the proof obligation of the mutated link's module
      (e.g. the poll-loop mutant failing the poll postcondition
      queue-nonempty-implies-poll), not an incidental unrelated failure.
      Verify the worked example's formula in the paper matches the actual
      postcondition in the verified source.
- [ ] **The level-0-scan narrative is exact.** Three sub-claims: (a) the mutant
      reproduces the shape of a real bug that once verified green inside a
      trusted body — cross-check against the repo's record of the
      `scan_wheel_min` bug; (b) exactly three verified-region mutants were
      additionally run under the stress suite and the level-0 scan is the only
      one the suite passes — match the recorded dynamic-run outcomes, and
      confirm the paper does not imply all ten were stress-tested; (c) the
      100 ms park cap explanation is consistent with the executor's actual
      park bound.
- [ ] **Controls behave as printed.** C1 (empty thread-local taker) and C3
      (no-op mio registration) verify green and hang the stress suite in all
      three runs; C2 (dropped ghost-log event) is caught by the verifier.
      Match identities and outcomes against `RESULTS.md`; confirm "all three
      runs" matches the recorded run count per dynamic test; and check the
      paper's interpretive claim (trusted surface narrower than declared)
      rests only on C2's catch, not on extrapolation.
- [ ] **Cross-document baseline agreement.** The expected matrix in
      PROOF_AUDIT_CHECKLIST.md's mutation-regression item (M01--M10 CAUGHT,
      C1/C3 SURVIVED, C2 CAUGHT), `mutation-test/RESULTS.md`, and the paper's
      prose must all tell the same story; a future re-run that deviates
      invalidates the paper sentence, so this item should be re-checked after
      any proof or trust-boundary refactor.

---

## §4. Correctness-stress experiment vs. `lion-benchmark/correctness-stress`

> Paper location: `lion-paper/sections/lion_evaluation.tex`, subsection
> "Correctness Under Stress" (`\label{sec:correctness-stress}`,
> Table `tab:correctness`, Figure `fig:stress-heatmap`). Ground truth:
> `lion-benchmark/correctness-stress/` — the Rust workload (`lion/`, `shared/`,
> `tokio-*/`), the C harnesses (`libevent-tests/`, `libuv-tests/`), `run.sh`
> (rep count, timeout, hang classification), `plot.py` (heatmap generation),
> and `ref-2/` (`results.jsonl` per family, `events.tsv`, `stress_heatmap.pdf`,
> `PROVENANCE.txt`).
>
> Why it matters: this section carries two different kinds of claims that fail
> differently — workload-description numbers (some are configured constants,
> some are measured event counts; conflating them turns an honest measurement
> into an unfalsifiable assertion) and a reproduction matrix whose force
> depends entirely on version pinning and the negative controls. The
> hang-classification argument (timeout ⇒ permanent stall) is load-bearing for
> every "Hang" cell.

- [ ] **Configured constants match the workload source.** 200 request tasks
      (1 ms sleep inside a 5 s timeout), 50 cooperative tasks, 10
      scatter/gather coordinators spawning waves of 10 children, a 50 ms
      heartbeat, a TCP echo server with 48 waves of 15 concurrent clients, the
      3 s run deadline, and the multi-threaded configuration's
      blocking-offload worker — locate each constant in the Rust harness
      source and confirm the Lion and Tokio arms share the same workload
      definition (a diverging constant between arms invalidates the
      comparison).
- [ ] **Derived and measured counts recompute, and the paper does not conflate
      them.** ~510,000 registration/cancellation pairs, ~43,500 yields, 54,750
      child tasks, 720 connections, ~400 concurrently live tasks, "over
      56,000" spawns, "more than 550,000" timer and yield operations —
      recompute each either arithmetically from the configured constants
      (e.g. 720 = 48×15) or from `ref-2` telemetry (`events.tsv`,
      `results.jsonl`), and record which of the two each figure is. A figure
      presented as measured must exist in the archived telemetry; a derived
      figure must follow from constants the harness actually uses.
- [ ] **Issue anchoring is real, not decorative.** Each task class cites a bug
      it stresses (#3069 timer registration/cancellation, #5020
      spawn/wakeup-notification) and the C harnesses claim to include "the
      library-specific API sequences that the listed issues document" — check
      the C test code actually performs those sequences (libevent:
      `evhttp_set_bevcb` filter path for #237, `EV_CLOSED` subscription for
      #984; libuv: bind/listen on a closing handle for #3503), and that the
      table's Issue(s) row matches which harness/version each issue is
      actually triggered in.
- [ ] **The version matrix is pinned and justified.** Buggy versions (Tokio
      1.21/1.42/1.44; libevent 2.1.5/2.1.11; libuv 1.43.0) must be pinned in
      the harness build files, and each must actually contain its listed bug
      (cross-check against the fix versions from §1's issues). The negative
      controls (Tokio 1.52.3, libevent 2.1.12, libuv 1.44.2) must contain the
      fixes and be recorded in the harness; "pass 3/3" for them must appear in
      `ref-2` results. Version strings quoted in the paper are upstream facts
      and are exempt from the repo's no-dates rule, but must match the pins
      exactly.
- [ ] **Adjudication protocol matches the harness.** Three runs per cell, 15 s
      timeout, timeout recorded as Hang — confirm in `run.sh`. The "longest
      honest critical path of 8 s (3 s deadline plus the 5 s backstop
      timeout)" arithmetic must follow from the same constants item 1 located;
      15 s must exceed it with the margin the paper implies. Check every table
      cell's Hang/Pass against `ref-2` `results.jsonl` run-by-run (3/3, not
      2/3 silently rounded).
- [ ] **The heatmap is regenerable and honestly described.** `plot.py` over
      `ref-2/events.tsv` must reproduce `stress_heatmap.pdf`, and the copy the
      paper embeds (`lion-paper/fig/stress_heatmap.pdf`) must match the
      archived one. The caption/prose claims — five event categories, "all
      event types remain active throughout the test" — must be checkable from
      `events.tsv` itself (no category's events vanish for a sustained
      window), and the figure must carry no date/timestamp (repo convention).
- [ ] **Scale reduction and scope are disclosed accurately.** "The C harnesses
      preserve the same five-class stress pattern at a reduced scale" — record
      the actual C scale factors and confirm all five classes exist in both C
      harnesses; the paper's totals (~400 live, >56,000 spawns, >550,000 ops)
      must be claimed only for the Rust workload, not implied for C. Also
      check the broader scope claim — "hang 3/3 on a confirmed liveness bug
      triggered by the stress workload" — is supported per cell: the
      attribution rests on the fixed-version negative control flipping the
      outcome, so every buggy/fixed pair must differ only in the library
      version, not in workload or harness code.

---

## §5. Real-world applications vs. `lion-benchmark/real-world`

> Paper location: `lion-paper/sections/lion_evaluation.tex`, subsection
> "Real-World Applications" (`\label{sec:real-world}`, Table
> `tab:real-world`). Ground truth: `lion-benchmark/real-world/` — the three
> ports (`rumqtt/`, `pingora/`, `axum/`), shared orchestration (`lib/`,
> `hosts.env.example`), `ref-2/` (per-run raw CSVs), `ref_paper_setup.md`
> (topology record), and `axum/attribution_note.md` (the serve-path /
> blocking-pool attribution experiment).
>
> Why it matters: this section's force is the *twin* discipline — same
> application, runtime swapped, nothing else. Every number is only as strong
> as the symmetry behind it, and the headline "drop-in with negligible cost"
> invites the stronger misreading that the verified core itself is faster;
> the attribution experiment shows the localhost lead lives mostly in the
> unverified blocking pool, so wording that steers attribution matters.

- [ ] **App characterization is sourced.** The LOC figures (30K/75K/30K), the
      descriptors ("production MQTT broker", "Cloudflare's HTTP server
      replacing nginx", "one of the most popular Rust web frameworks"), and
      the coverage claim (network middleware / HTTP serving / filesystem I/O
      span "the major async runtime usage patterns") — recompute LOC against
      the actual forked trees (state the counting rule), and confirm the
      descriptors are upstream facts, not embellishments.
- [ ] **Port-cost figures recompute.** "49 to 343 changed lines (added plus
      removed) per application" — recompute each port's diff against its
      upstream base (the forks' diff-vs-upstream, or the recorded port
      diffs); confirm the min/max match, the counting rule (added+removed)
      is the one used, and no port exceeds the stated range. This is the
      "drop-in" claim's quantitative backbone.
- [ ] **Twin symmetry per app.** For each port, the full diff between the
      Tokio and Lion arms must reduce to the runtime swap plus disclosed
      off-path components (pingora: tokio-arm-only idle UDS listener off the
      measured port, orchestration loop on tokio in BOTH arms; axum: serve
      path shape — settled as performance-nil in `attribution_note.md`).
      "Both configured with a single-threaded runtime" must hold in source
      for all three (axum/rumqtt `new_current_thread`; pingora
      `threads: 1, work_stealing: false`). Build profiles identical per pair.
- [ ] **Topology claims match the recorded setup.** rumqtt cross-machine
      (1 Gbps, ~0.25 ms RTT), Pingora "canonical single-host", Axum dual
      (cross ~0.38 ms RTT + localhost) — check against `hosts.env.example`,
      `ref_paper_setup.md`, and the ref-2 provenance records; RTT figures
      must come from a recorded measurement, not memory. The
      bandwidth-limited rationale for Axum-cross must be arithmetically true
      (payload × rate ≈ line rate for the larger payloads).
- [ ] **Workload definitions match the harness.** rumqtt Fanout (1 publisher
      → 50 subscribers, rate-limited), Fanin (50 → 10), P2P (50 independent
      pairs); Pingora low-conc 50 / high-conc 200 connections, large payload
      10 KB; Axum API-4KB / Static-64KB / Mixed lua workloads — locate each
      constant in the benchmark configs/scripts. The table's measurement
      caliber note (rumqtt rows are subscriber-side *delivered* throughput,
      with the publish-returns-on-local-enqueue rationale) must match how
      the harness actually computes the number.
- [ ] **Every table cell and ± recomputes from ref-2, and the statistic is
      disclosed.** Recompute all 12 rows (Tokio, Lion, ±, Ratio) from the
      ref-2 per-run CSVs using the project statistic; check each Ratio cell's
      rounding. The paper currently does not say what ± is or how many runs
      (the "(trimmed mean ± std, 10 runs)" caption note is commented out) —
      either the caption discloses the statistic or this item fails on
      disclosure grounds.
- [ ] **Prose percentages recompute and stay within claim scope.** "Within
      4%" / "3% ahead" / "inside run-to-run variation" (rumqtt), "within 3%
      ... inside the run-to-run spread" (pingora), "identical throughput"
      (axum cross), "19% / 8% / 7% faster" (axum local), "99–119% across all
      nine workloads (using Axum localhost)" — recompute each from the table;
      "inside run-to-run variation" claims must actually be within the ±
      spread of both arms; the nine-workload span must match the cell set it
      names.
- [ ] **Attribution stays honest.** The section may claim drop-in parity and
      report the localhost lead, but must not attribute the Axum lead to the
      verified scheduler core: per `axum/attribution_note.md`, the serve-path
      shape is performance-nil and the lead is dominated by the (unverified,
      trusted) blocking-pool implementation, with an equalized-runtime
      residual near noise. Check the section's wording (and any other section
      quoting the 119% figure) against this guard; if the paper adds an
      attribution sentence, it must cite the note's finding, not exceed it.

---

## §6. Micro benchmarks vs. `lion-benchmark/micro`

> Paper location: `lion-paper/sections/lion_evaluation.tex`, subsection "Micro
> Benchmarks" (`\label{sec:micro-benchmarks}`, Figure `fig:micro-benchmarks`
> = `fig/micro_bench_paper.pdf`, five panels a–e). Ground truth:
> `lion-benchmark/micro/` — the benchmark harnesses and run scripts, the
> plotting pipeline (script + `.venv`), and `ref-2/` (per-run raw data +
> provenance).
>
> Why it matters: this section carries the paper's densest concentration of
> raw performance numbers (~20 quoted values and ratios across five panels)
> plus mechanism claims about *other people's* runtimes (Tokio's timer wheel
> internals, Monoio's io_uring constraints). It also has a known history: the
> timer panels were once inflated ~25% by the `scan_wheel_min` bug and were
> regenerated wholesale after the fix — lineage must be re-verifiable forever.

- [ ] **Benchmark definitions match the harness.** Timer cancel: each task
      registers a long timer and cancels it via a short 1 ms timer, looping —
      find the loop and both durations in the harness; concurrency points
      1K/5K/10K. TCP echo: 64-byte ping-pong; connection points
      10/50/100/500; multi-thread echo uses SO_REUSEPORT with 500
      connections. Filesystem: 50 concurrent tasks doing reads AND writes
      (the paper says both — confirm the harness does writes, not just
      reads); blocking pool swept 1→8 threads. Multi-thread timer: 10K timers
      TOTAL split across threads (fixed load, not 10K per thread) — confirm
      the harness divides, since this wording was corrected once before.
- [ ] **Comparison arms are what the paper says.** Four arms: Tokio, Lion,
      Monoio (single-thread only), Tokio-Partition (multiple independent
      single-thread Tokio runtimes behind the same round-robin interface as
      Lion — confirm the construct exists in the harness and the interface
      really is shared with Lion's multi-instance path, not a reimplementation).
      Monoio's exclusion rationale ("I/O operations cannot migrate across
      threads") must be an upstream-documented fact. Machine claim (EPYC
      7702P, 64 cores / 128 threads, 512 GB) must match ref-2 provenance.
- [ ] **Every quoted number recomputes from ref-2.** All panel-referenced
      values and ratios: timer ST 563K/379K (1.5×), 1.4× at 5K, 2.86M/2.64M
      (8%) at 10K, Monoio's ordering claims; timer MT 2.63M→5.99M (2.3×),
      Tokio-Partition plateau 5.00M, Tokio 2.85M→0.59M degradation; echo ST
      "within 2.3%" at 10/50/100, Monoio "within 1%", Tokio ahead "by 11%
      (62.1K vs 55.1K)" at 500 — check the ratio convention here: 62.1/55.1
      is +12.7% of Lion's rate; 11% only as 1−55.1/62.1 — the denominator
      must be stated or the number corrected; echo MT "within 3.5% at 4
      threads"; fs ~17K→~38K, Lion +11% at 4 threads, convergence at 8,
      Monoio 21K single-thread and the crossover at pool size 2. Recompute
      each from ref-2 raw data with the project statistic; flag any value
      that only matches a superseded batch.
- [ ] **Figure integrity and statistic disclosure.** The embedded
      `fig/micro_bench_paper.pdf` must match the archived ref-2 figure (or
      regenerate identically from ref-2 raw via the plotting pipeline); error
      bars must be the project statistic, and the caption's "(10 runs,
      trimmed mean ± std)" should disclose the trim rule (two highest and two
      lowest dropped; sample std over the middle six) to the same standard as
      the real-world table; panels/axes must match the caption's five-panel
      description; no dates in rendered figure content.
- [ ] **Post-fix lineage of the timer panels.** Panels (a) and (d) must
      derive from the post-`scan_wheel_min`-fix regeneration: check ref-2's
      recorded commit postdates the fix, that the plotted values match the
      regenerated batch (not the inflated pre-fix archives), and that no
      pre-fix number survives in the prose. This item exists because the
      pre-fix figures were ~25% inflated; it must be re-checked after any
      timer-wheel change.
- [ ] **Mechanism and attribution claims are sourced or hedged.** "Tokio's
      timer wheel is heavily optimized with pointer-based shared state and a
      fast-path insertion that bypasses locking" — verify against Tokio's
      source (or cite); "degrades ... due to cross-thread synchronization
      overhead on its shared timer wheel" — attribution must be supported
      (e.g. by the Tokio-Partition contrast, which shares everything but the
      wheel) or hedged; "benefiting from Lion's more lightweight timer
      implementation" and the closing "no significant runtime overhead" must
      stay within what the data shows (Lion loses 8% at 10K timers and 11% at
      500 connections — the summary sentence must not erase the disclosed
      losses).

(Remaining: §7 verification-claim wording (lion_verification.tex numbers vs
proof artifacts) — to be added if needed; §7.3's figure/claims are largely
covered by the §7.3 trim analysis.)
