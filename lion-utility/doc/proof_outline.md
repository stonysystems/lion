# lion-utility Proof Outline

> A concise account of **what each lion-utility utility proves**, where the trust
> boundary sits, and the **call contract** the glue has with the verified kernels.
> It does not cover concrete proof steps.

## In one sentence

lion-utility uses an **IronFleet-style** structure: each utility = a **verified
pure state-machine kernel** + **whole-module trusted glue**. The kernel uses
executable Verus (exec fn + proof) to enclose **the protocol decisions and the
state machine** inside the verification boundary, and maintains inductive
invariants on the ghost state; the glue (whole-file
`#![cfg_attr(verus_keep_ghost, verus::trusted)]`, plain Rust invisible to Verus)
(a) honestly feeds real-world observations (syscall results, readiness, the real
waker identity) into the kernel; (b) carries out the external effects the kernel
decides on (register / set_waker / wake / moving the `T` value); and (c) holds
real-world bookkeeping of its own — waker maps, park episodes, delivery loops,
and cancellation (`Drop`) paths. The glue consumes every kernel decision
mechanically, and the conventions the verifier cannot check are guarded by
regression tests (`tests/cancel.rs`, `tests/decisions.rs`).

## §0 Legitimate trust base (explicitly retained, not provable inside Verus)

- Real syscall results: mio's read/write, readiness (`is_readable`/`is_writable`).
- Real `Waker::wake()` semantics, and the identity mapping between `WakerView=int`
  and the real `Waker`.
- The `Pin`/`Context` plumbing, and std primitives such as `Arc`/`std::sync::Mutex`/`UnsafeCell`.
- The glue modules as a whole: they are plain Rust outside `verus!{}`, so the
  kernel call protocol (right step, right order, `requires` such as
  `signal_step`'s `permit < u64::MAX` upheld) is a convention, checked by
  regression tests rather than the verifier.

Unlike reactor/executor (whose trust is per-function `external_body` edges),
lion-utility's trust is module-granular. What IS verified: the state machines,
their inductive invariants, data semantics, and the protocol decisions — the
kernels decide, and the glue consumes those decisions mechanically.

## Reused templates

`lion-utility-spec`'s `framework/{action_safety, async_contract, module_spec}` +
`generic/{events, log, invariants, contract, extension}`, isomorphic to
lion-liveness.

- `ActionSafety{acceptance, validity}` — `∀i: acceptance(l,i) ⟹ validity(l,i)`.
- `AsyncContract{acceptance, fulfillment, assumption}` (no `arrival` field since
  the S1 framework unification) + `bounded_liveness_env_without_arrival` (the
  env form; the non-env form is not used in this crate).
- `utility_inv(l) = wakeup_guarantee(l) ∧ resource_ownership(l)` (the two general safety invariants).

---

## 1. Wakeup-side kernels

### SleepKernel (`time/sleep/`)
- State: deadline + the ghost log of registered timers.
- Invariant: `utility_inv` (wakeup goes through the **timer** branch; resource_ownership tracks the timer rid).
- Trust boundary: the real clock / reactor registration; liveness is delegated to the reactor's `bounded_timer_wakeup`.

### IoKernel (`net/tcp/`)
- State: resource_id + armed + ghost log.
- Invariant: `utility_inv` (wakeup goes through the **io** branch; resource_ownership tracks the io rid).
- `poll_step(m, was_ready, would_block)` decides `Arm | Complete`, with `(a is Arm) <==> (!was_ready || would_block)`.
- Trust boundary: mio syscall / readiness / set_waker; liveness is delegated to the reactor's `bounded_io_wakeup`.

### WaiterKernel (`sync/waiter/`) — backs Notify / Semaphore / Mutex, and the wakeup side of channels
- State: `permit: u64` + `queue: Vec<u64>` (waiter ids) + ghost log + `init` (initial permits).
- **Invariant (after the §1a tightening)** `well_formed = wf(log) ∧ queue_view(queue)==waiters(log) ∧ permit==init+available_permits(log)`:
  - `waiters(log)`: the sequence of parked waiters implied by the log (PassWaker enqueues, WakeWaker removes the first);
  - `available_permits(log)`: per-event accounting (Signal +1 per tick, WakeWaker −1, Wait-Finished −1).
  - From this it proves: **no phantom/lost waiters, the id woken by a signal must have been parked by a PassWaker, and the permit accounting is consistent**.
- **liveness = PassWaker Contract** (`liveness.rs`): `bounded_liveness_env_without_arrival` — the lemma establishes **wf-preservation** (real, via the §2.1 segment-preservation lemmas) and the **env-filtered response at n=0**, where the env assumption `waiter_wake_env`'s consequent IS the contract's fulfillment (a new WakeWaker since the anchor). Wake **delivery itself is assumed per-utility, not derived** — the kernel has no non-trivial liveness content of its own; its genuine machine-checked content is on the signal side (from the coupling invariant: `signal_step` on a non-empty queue wakes the **true FIFO head**). Hard vacuity is ruled out by a concrete env witness (`lemma_waiter_env_satisfiable`), but genuinely-waiting states (parked, wake not yet arrived) falsify the env and are outside the filtered domain.
- Methods: `new`/`with_permits`/`wait_step`/`signal_step`/`try_acquire_step`/`remove_step` (cancellation withdraw — removes the first queue occurrence and emits CancelWaker; no-op on miss), each maintaining well_formed, 0 assume / 0 admit. `signal_step` has a precondition `permit < u64::MAX` (mirroring tokio's MAX_PERMITS, upheld by convention at the trusted glue call sites).
- Glue call contract: when the recv/acquire side parks it calls `wait_step(id)` (emit PassWaker); the release/notify side calls `signal_step` (emit WakeWaker, or store a permit); when a waiting future is dropped, its `Drop` impl calls `remove_step(id)` to withdraw (or forwards an already-granted permit); the glue holds the real waker and runs `wake()` on the returned id. These conventions are exercised by `tests/cancel.rs`.

---

## 2. Channel data-side kernels (§1b)

Each channel = a **data kernel (this section)** + a **WaiterKernel (wakeup)** + thin glue (moving the real `T`).

### OneshotKernel (`sync/oneshot_kernel.rs`)
- State machine: `Empty → Full → Taken | Closed`, ghost `sent`/`delivered`.
- Theorems: **send-once** (sent≤1), **at-most-once delivery** (delivered≤1), **no delivery without a send** (delivered≤sent).
- Methods: `send_step`/`recv_step`/`close_step` return decisions.

### ChannelKernel (`sync/channel_kernel.rs`) — bounded/unbounded mpsc
- State: `buffered`/`reserved`/`capacity` + ghost `sent`/`recvd`/`buf` (the buffered seq sequence).
- Invariant: `buf` is exactly the contiguous block `[recvd, sent)`, `sent==recvd+buffered`, `buffered+reserved≤capacity`.
- Theorems: **FIFO with no holes** (`buf[i]==recvd+i`, pop delivers the oldest), **no loss, no duplication**, **capacity upper bound**; the reserve/fill/unreserve permit accounting is consistent.
- unbounded = capacity `u64::MAX`.

### WatchKernel (`sync/watch_kernel.rs`)
- State: `version: u64` + ghost `vsent`.
- Theorem: **version is strictly monotonic** (+1 per publish, `version==1+vsent`) → a receiver's seen-vs-current comparison never misses an update or reorders. `changed_step`/`current` are pure queries.

### BroadcastKernel (`sync/broadcast_kernel.rs`)
- State: `next_seq`/`buffered`/`capacity` (`oldest = next_seq - buffered`).
- `recv_step(cursor)` decides `Lagged | Ready | Park` from the ring window. Theorems: **Lagged ⟺ cursor < oldest**, Ready delivers `seq==cursor` (in order), seq monotonic.

---

## 3. Combinator kernels (§1c)

### TimeoutKernel (`time/timeout_kernel.rs`)
- `poll_step(fut_ready, sleep_ready)` decides. Theorem: **`Pending ⟺ !fut_ready ∧ !sleep_ready`** — timeout is Pending only when both sub-futures are Pending, so every Pending carries a wakeup source (the wrapped future's own, or the already-verified Sleep's timer). Compositionally well-formed.

### IntervalKernel (`time/interval_kernel.rs`)
- State: `deadline`/`period` + ghost `first`/`fires`.
- Theorem: **`deadline == first + fires×period`**, strictly +period every tick (monotonic, no drift).

---

## 4. Trust-boundary overview (per trusted-glue file)

Every glue module is trusted as a whole file (`verus::trusted`, plain Rust
invisible to Verus). Glue is not decision-free: it contains waker maps, park
bookkeeping and delivery loops; it consumes every kernel decision mechanically
and carries the cancellation (`Drop`) paths — all guarded by regression tests
(`tests/cancel.rs`, `tests/decisions.rs`):

| glue file | trusted (within §0) | call contract to the kernel |
|---|---|---|
| `time/sleep/future.rs` | Pin/Context, reactor registration | drives SleepKernel.poll_step |
| `net/tcp/{stream,listener,socket}.rs`, `net/addr.rs` | mio syscall/readiness, real waker, UnsafeCell (into_split) | IoKernel.poll_step/new/drop_step |
| `sync/notify.rs`, `semaphore.rs`, `mutex.rs` | Mutex/Arc/AtomicBool, real Waker | WaiterKernel.{wait,signal,try_acquire,remove}_step |
| `sync/oneshot.rs` | Mutex/Arc, real Waker, moving `T` | OneshotKernel + WaiterKernel |
| `sync/mpsc.rs` | Mutex/Arc, real Waker, moving `VecDeque<T>` | ChannelKernel + two WaiterKernels |
| `sync/watch.rs` | Mutex/Arc, real Waker, `T` | WatchKernel + WaiterKernel |
| `sync/broadcast.rs` | Mutex/Arc, real Waker, ring `VecDeque<Slot<T>>` | BroadcastKernel + WaiterKernel |
| `time/timeout.rs` | Pin/Box, sub-future poll | TimeoutKernel.poll_step |
| `time/interval.rs` | real Instant, Sleep | IntervalKernel.tick_step |
| `fs/mod.rs` | all of std::fs (runtime-independent, trusted wholesale) | no kernel (pure blocking-IO wrapper) |

> The glue↔kernel "value/waker ↔ id/seq" correspondence (e.g. real `Waker` ↔
> `WakerView=int`, real `T` ↔ buffered seq) is part of the trust base: the kernel
> proves the protocol layer (order / no-loss / wakeup / capacity), and the glue
> faithfully maintains the correspondence between values and their protocol positions.

## Completion status

`./verify.sh`: 96 verified / 0 errors / 0 assume / 0 admit. §1a/§1b/§1c all have
theorems. `cargo test`: 24/24 (12 cancellation + 11 decision-consumption + 1
interval-ledger regression tests guarding the trusted-glue conventions).
