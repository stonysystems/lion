# Two hang-fixing stories

Two liveness incidents from Lion's development, both diagnosed at the
verified/trusted boundary — one from the wrong side of it, one saved by it.

---

## Story 1: a lost-wakeup hang in `Connect::poll` (trusted glue)

### Symptom

During a micro-benchmark batch on `zoo-004` (Xeon E5-2683 v4, kernel 6.2-pve), a
single-threaded `micro-tcp-echo --runtime lion` run that should finish in 10 s
wedged for 65+ minutes. Frequency ~1 in 20 runs on that machine; **zero**
reproductions in 30 attempts each on a Ryzen desktop and on the identically-CPU'd
`zoo-003`. A watchdog wrapper (`timeout`, now part of `micro/run.sh`) and a
hang-hunter harness that keeps wedged processes alive (`SIGSTOP`) captured live
specimens.

### Forensics

Every specimen showed the same signature:

- all TCP connections `ESTABLISHED` with **empty send and receive queues** —
  no data in flight, both sides waiting for the other;
- the runtime thread parked in `epoll_wait`, the main thread in `futex_wait`;
- only **2 voluntary context switches** — the process hung during connection
  setup, not in steady state.

A single-threaded runtime rules out data races: this had to be a logic hole,
not a race. The empty queues plus the setup-phase timing pointed at the
connect path.

### Root cause

Lion tracks per-resource readiness in a userspace bitmap (edge-triggered mio
underneath: a flag, once consumed, is only re-set by a **new** epoll edge).
`Connect::poll` cleared the writable flag unconditionally:

```text
init_readiness(rid)            # optimistic: READABLE|WRITABLE
Connect::poll #1               # flag set -> CLEAR -> peer_addr: NotConnected -> arm waker
  ... connect completes; reactor delivers the real writable EDGE:
  ...   flag set again + armed waker fired
Connect::poll #2               # flag set -> CLEAR -> peer_addr: Ok -> Ready(stream)
first poll_write               # flag CLEAR -> arm WRITABLE waker -> Pending
                               # an idle connected socket never produces
                               # another writable edge  ==>  permanent hang
```

The bug only bites on this **two-poll connect path**. On the common one-poll
path (connect already complete at the first poll — the loopback norm) the
clear consumes only the *optimistic* init flag while the real edge is still
undelivered; the next reactor park re-sets the flag and everything works. That
scheduling lottery is why the hang was sporadic and machine-dependent.

An audit of every other readiness clear in `lion-utility` (`poll_read`,
`poll_write`, accept, UDP send/recv, `try_io`) found each one justified by a
preceding `WouldBlock` — the only edge-trigger-safe place to clear.
`Connect::poll` was the sole violator.

The flag-clearing pattern was itself introduced by the fix for an *earlier*
connect hang, found during the same IronFleet integration campaign as Story 2
(commit `5129c719`) — a fix-induced regression that survived four months
behind the one-poll fast path.

### Fix

Keep the flag on the connected path — the socket genuinely is writable, and
`poll_write`'s own `WouldBlock` branch remains the only clearing site; consume
the flag only on the `NotConnected` fall-through before arming
(`lion-utility/src/net/tcp/stream.rs`). Trusted-glue change, no proof impact;
full `./ci.sh` green and all 24 utility regression tests pass.

### Why the verifier could not see it

The bug lived in the **trusted glue layer** (`verus::trusted`), on the far
side of the verified region's boundary: the readiness bitmap, the epoll edge
contract, and `Connect`'s Future impl are all part of the modeled-environment
plumbing that the liveness proof *assumes* (io readiness forwarding), not code
it verifies. This is exactly the class our own trust inventory ranks highest
(`TCB_and_limitations.md` §1: mio/OS boundary and wake plumbing), the class
the mutation experiment's surviving controls (C1/C3) map out, and the third
liveness bug found in this layer (two deadlocks were found in sync glue during
the utilities audit). The verified region has yielded none.

---

## Story 2: the hang that wasn't — `block_on` + `yield_now`, 100 ms at a time

### Symptom

During the IronFleet integration (a Verus-verified Paxos core driven over an
*unverified* async I/O wrapper — TCP connection management, stream splitting,
reader/writer tasks, channel routing — on Lion), the 3-replica cluster
appeared to hang on deployment: the leader progressed through consensus phases
(1a, 1b, phase 2) and batched client requests, but replies never reached the
benchmark client. 0–2 requests completed before the 10-second timeout —
effectively zero throughput.

### Unguided debugging: 3 hours, 6 wrong hypotheses

Without being told which components were verified, the debugging effort spent
roughly three hours exploring hypotheses spanning **every layer of the
system**: waker overwrite under concurrent read/write interest, stream
splitting invalidating prior registrations, cross-thread registration races,
nested cross-thread spawns losing tasks, the reactor skipping parks under this
task topology, and the Paxos state machine failing to advance replication. It
produced 25 targeted test programs and instrumented the read path, outbox
drains, and channel routing. Every test passed — and the system still "hung".

All six hypotheses were plausible; each names genuinely complex logic. But
five of the six pointed at code that is **formally verified**.

### Guided debugging: 5 minutes

Treating the verified components (Lion's runtime internals, the Paxos protocol
logic) as unconditionally correct collapsed the search space to the unverified
I/O wrapper — and the root cause surfaced in five minutes.

The system was not hanging. It was making progress **125,000× slower than
expected**. `block_on`'s main task is, by design, not registered in the
executor's task slab (it runs its own polling loop outside the normal task
lifecycle). When that task cooperatively yields via `yield_now().await`, the
executor's `park()` inspects its queues, finds no registered task awaiting
scheduling — the `block_on` task is invisible to it — and sleeps its full
100 ms timeout. The Paxos driver yields once per main-loop iteration, so the
cluster ran one consensus round per 100 ms: near-zero throughput,
indistinguishable from a hang at benchmark timescales.

### Fix

Ten lines (commit `5129c719`): a thread-local `BLOCK_ON_YIELDED` flag, set
when `block_on`'s task defers, checked in `park()` to skip the timeout. After
the fix a yield costs 0.8 µs and the benchmark reached 11,813 req/s.

### What verification did — and didn't — do

Lion's verified liveness guarantee was **never violated**: the main task was
always eventually re-polled after the timeout. The defect was a performance
pathology in trusted entry-point plumbing (`block_on`/`park` glue), not a
correctness failure — "eventually" is not "promptly". But verification still
carried the diagnosis twice over: it let the symptom be reclassified from "the
system is stuck" to "the system is progressing too slowly", and it soundly
excluded the verified region from suspicion, collapsing the search from the
whole system to the glue boundary — a 3-hour search became a 5-minute one.

---

## Takeaways

1. **The trust boundary is drawn where the bugs are.** Every liveness incident
   found in Lion so far — this pair, plus the two sync-glue deadlocks from the
   utilities audit — sits in trusted glue; the verified region has yielded
   none. Shrinking that glue (e.g. verifying the readiness-flag protocol
   against an edge-trigger model, or bringing `block_on` into the modeled
   executor) is the highest-value future verification work.
2. **Verification narrows the debugging search space.** Even when the defect
   is outside the verified region, the proof soundly eliminates most
   hypotheses and sharpens the symptom itself (true hang vs. slow progress).
3. **Benchmarks are liveness tests.** Both incidents were caught because a
   benchmark run misbehaved; the run harness now converts wedges into logged,
   retried failures (`timeout` wrapper), turning every future benchmark run
   into a liveness regression test.
4. **Yesterday's fix is tomorrow's bug.** The `Connect::poll` hang was planted
   by the fix for an earlier connect hang. Liveness fixes in unverified glue
   carry no proof that they don't trade one stall for another.
