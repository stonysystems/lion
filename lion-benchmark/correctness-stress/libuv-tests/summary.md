# libuv Correctness Stress Test Results

## Results

```
(REPS=3 per cell; hangs are deterministic)
Test                v1.43.0       v1.44.2
─────────────────────────────────────────────
3503_lifecycle      ✗ HANG 3/3    ✓ PASS
combined            ✗ HANG 3/3    ✓ PASS (~3.0s)
```

## Combined Workload — mapping to the Rust (Tokio/Lion) test

The same test design is ported: 5 workloads run concurrently in one event loop
under a heartbeat, with a timeout = hang oracle. The execution model differs
(libuv event loop + callbacks vs Rust async/await), so the code differs while the
goals and structure are the same. This corresponds to the Rust **current-thread**
configuration; the multi-thread (#7209) path has no event-loop analog.
Also not ported: the Rust workload's LocalSet startup-init pattern (the tokio
#5020 trigger path) — a C event loop has no runtime-owned local task set to
mirror it.

| # | libuv Workload | Scale | Rust subsystem it mirrors |
|---|---|---|---|
| W1 | Timer Cancel Storm | 500 pairs × 100 iter = 50K register/cancel ops | Timer Ops (requests' timeout-guarded op) |
| W2 | Callback Chain Storm | 100 parents × 10 children, each re-fires | Task Lifecycle + Cooperative Scheduling (fan-out + cooperative compute) |
| W3 | TCP Echo Waves | 20 sequential connections with echo | Network I/O (echo workload) |
| W4 | Handle Lifecycle | 10 rounds close → bind/listen (triggers 3503) | libuv's own bug-triggering subsystem (no direct Rust analog) |
| W5 | Heartbeat Monitor | 30 ticks × 100ms | Heartbeat (liveness canary) |

## What "combined" does and does not show

**Disclosure**: unlike the Rust suite (whose combined workload carries no
bug-specific code), the C combined test EMBEDS the library's documented
bug-trigger subsystem in the mix — W4 is exactly the issue-reproducing
lifecycle pattern (and it also exists standalone as the dedicated issue test).
A "combined: HANG" verdict is therefore attributable to that subsystem per the
root-cause analyses below, NOT evidence that the neutral mix (W1/W2/W5 + plain
echo) hangs by itself. For libuv the attribution is: the v1.43.0 combined hang comes from W4 (#3503).

Scales also differ deliberately from the Rust workload (e.g. W1 runs 50 K
count-bounded timer ops vs Rust's deadline-bounded loops): what carries over
is the test design — concurrent mix, completion barrier, timeout-=-hang
oracle, fixed-version negative controls — not the constants. Library versions
are built from upstream release tags by `build_deps.sh` (record the resolved
commit hashes if tag stability is a concern).

## Hang Root Cause

- **v1.43.0 HANG**: W4 triggers issue 3503 — `uv_tcp_bind()` and `uv_listen()`
  do not check `UV_HANDLE_CLOSING`. Operations succeed on a half-torn-down
  handle, leaving the event loop in an inconsistent state. The handle's close
  callback fires but the listen socket remains active, causing `uv_run()` to
  block indefinitely.

- **v1.44.2 PASS**: Fix (commit 8bcd689c04) adds `uv__is_closing(handle)`
  check in `uv_tcp_bind()`, returning `UV_EINVAL` for closing handles.
  All 5 workloads complete in ~3 seconds.

## Issue 4738 (Pipe read hang)

Not tested — this bug is **Windows-only** (depends on Windows named pipes
and IOCP). Cannot be reproduced on Linux.

## Raw Data

```jsonl
{"test":"3503_lifecycle","runtime":"libuv-1.43.0","outcome":"HANG","elapsed_ms":15000}
{"test":"3503_lifecycle","runtime":"libuv-1.44.2","outcome":"PASS","elapsed_ms":0}
{"test":"combined","runtime":"libuv-1.43.0","outcome":"HANG","elapsed_ms":15000}
{"test":"combined","runtime":"libuv-1.44.2","outcome":"PASS","elapsed_ms":3003}
```
