# The Decision-Kernel Pattern: Design Rationale

> Why lion-utility is verified differently from the runtime Core, what the
> pattern buys, what disciplines it requires, and where its limits are.
> Companion to `proof_outline.md` (which catalogs what each utility proves).

## Two verification patterns in one codebase

Lion uses two distinct patterns for placing code under verification, chosen by
what the verifier can express:

|                    | Runtime Core (executor/reactor)        | Utilities (this crate)                     |
|--------------------|----------------------------------------|--------------------------------------------|
| Pattern            | **Instrumented implementation**        | **Decision kernel + trusted shell**        |
| What is verified   | The real control flow itself (exec code inside `verus!`) | The protocol **decisions** of a pure state machine |
| Trust shape        | Per-edge `external_body` functions, each with a trusted `ensures`; call protocol visible to the verifier | Whole-module trusted glue executing the kernel's decisions |
| Precondition       | Control flow must be expressible in Verus | Control flow may be idiomatic async Rust  |

The difference is **forced, not aesthetic**. The Core's control flow is Lion's
own and could be written inside `verus!`. A Tokio-compatible utility surface
cannot: `Pin<&mut Self>::poll` signatures, `std::task::Waker` vtables,
`Arc<Mutex<T>>`, generic `T` payloads and `Future` trait objects sit outside
what today's deductive verifiers accept. The decision-kernel pattern is the
adaptation: extract the verifiable heart of each primitive — its protocol state
machine — and verify *that*, leaving the inexpressible plumbing as a thin shell
that executes the kernel's verdicts.

## What a kernel is

Each kernel (e.g. `WaiterKernel`, `ChannelKernel`, `BroadcastKernel`,
`SleepKernel`) plays two roles at once:

1. **Decision oracle.** Every protocol-relevant call returns an explicit
   decision — `WaitAction::{Ready, Park}`, `SignalAction::{Woke, Stored}`,
   `BRecv::{Ready, Lagged, Park}`, `SleepAction::{Complete, Suspend, Fail}` —
   with a verified `ensures` pinning its exact meaning against the kernel
   state. The tricky logic of a synchronization primitive (FIFO ordering,
   permit accounting, ring-window semantics, deadline arithmetic) lives
   entirely on this side of the boundary.
2. **Ghost-log maintainer.** Each kernel step appends to a ghost event log and
   provably maintains the generic utility invariants of `lion-utility-spec`
   (wakeup discipline and resource ownership). This is the half that connects
   the utility layer to the composed liveness story: the invariants a pending
   task is assumed to keep are exactly the ones the kernels provably maintain.

## The disciplines the pattern requires

The pattern is sound in practice only under three design rules, which this
crate treats as part of the architecture rather than as conventions of taste:

1. **The shell consumes every decision mechanically.** A kernel that decides
   `Ready` while the shell parks anyway (or vice versa) would silently decouple
   the verified model from real behavior. Shell code therefore branches on
   every returned decision; no decision is discarded.
2. **Every queue-state change is a kernel step — including cancellation.**
   Dropping a waiting future is legal user behavior, and its effect on the
   waiter queue must round-trip through the kernel (`remove_step`, logging
   `CancelWaker`) so the coupling invariants keep holding; a granted-but-
   unconsumed permit is forwarded through the same verified signal path.
   Nothing mutates protocol state behind the kernel's back.
3. **The seam is guarded by tests.** The kernel/shell boundary is invisible to
   the verifier: kernel `requires` hold at shell call sites by convention, and
   the shell's fidelity to decisions is a convention too. These conventions are
   enforced by regression tests (`tests/cancel.rs`, `tests/decisions.rs`)
   covering the cases a verifier would otherwise own — cancellation,
   permit forwarding, decision fidelity, capacity edges.

## Where utility verification sits in the composed proof

Utilities are the vocabulary through which **user tasks** interact with the
runtime Core. This bounds what verifying them can and cannot achieve:

- **It cannot eliminate user-behavior assumptions.** The top-level theorem's
  task-behavior premises — a task returns `Ready` within a bounded number of
  polls, and never suspends without an armed wake source — are assumptions
  about user code, and remain so no matter how much of the utility layer is
  verified. Verifying the liveness of a *specific application* would require
  modeling that application's tasks; that is application verification, by
  design outside the runtime's scope.
- **What it does achieve** is precise: it converts *legal user behavior* —
  including waiting, spurious wakeups, and dropping a waiting future — into
  *maintained wake discipline*. Between "a peer task calls signal" and "the
  waker is invoked" lies real protocol logic that belongs to neither user code
  nor the Core; that segment is exactly what the kernels verify (the signal
  wakes the true FIFO head; permits are neither lost nor duplicated; a
  cancelled waiter cannot swallow a wakeup).
- **The connection to `lion-liveness` is assume-guarantee, not composition of
  theorems.** The composed proof carries the per-task utility invariants as an
  assumption on task behavior; this crate provides the constructive evidence
  that the assumption is dischargeable by real primitives. The two sides state
  their invariants in different vocabularies (a generic waker-keyed model here;
  a task-log model there), and the correspondence between them is an informal,
  per-clause argument rather than a mechanized theorem. Delivery from the
  shell's `wake()` to the executor's wake queues is likewise part of the
  composed proof's own bounded-arrival assumption, not something this crate
  proves.

## Verification economics

The investment split follows the composed theorem's dependency graph, not
component prestige. The Core's properties (bounded timer/io wakeup, drain
occurrence, FIFO scheduling) are load-bearing: the end-to-end proof consumes
them directly, so the Core gets deep verification of a narrow, algorithmically
dense core (timer wheel, tick structure) with per-edge trust. The utility layer
is a wide, comparatively shallow API surface whose properties enter the
theorem only as satisfiability evidence for an assumption — so it gets compact
kernel proofs plus tests: **prove the deep and narrow, test the wide and
shallow.**

## Honest limits

- The shell is plain Rust outside `verus!` (~53% of the crate's lines),
  trusted whole-module; see `proof_outline.md` §0 and the repository-level
  `TCB_and_limitations.md` for the full trust inventory.
- The binding between the ghost `WakerView` identity and the real
  `std::task::Waker` is trusted, not proven.
- Per-primitive liveness-style lemmas locate wake *delivery* in their
  per-utility environment assumptions; the kernels' machine-checked liveness
  content is the wake-discipline invariant and decision correctness, not
  end-to-end delivery.

The pattern is best read as a deliberate design experiment alongside the
Core's instrumented-implementation approach: two answers to "where do you put
the verification boundary when the verifier cannot swallow the whole program,"
selected per component by what the component's interface allows.
