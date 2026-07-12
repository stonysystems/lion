# libevent Correctness Stress Test Results

## Results

```
(REPS=3 per cell; hangs are deterministic)
Test                2.1.5-beta    2.1.11-stable   2.1.12-stable
──────────────────────────────────────────────────────────────────
issue_237_filter    ✗ HANG 3/3    ✓ PASS          ✓ PASS
issue_984_phantom   ✗ HANG 3/3    ✗ HANG 3/3      ✓ PASS
issue_232_ssl       — SKIP        ✓ PASS          ✓ PASS
combined            ✗ HANG 3/3    ✗ HANG 3/3      ✓ PASS (~3.0s)
```

## Combined Workload — mapping to the Rust (Tokio/Lion) test

The same test design is ported: 5 workloads run concurrently in one event loop
under a heartbeat, with a timeout = hang oracle. The execution model differs
(libevent event loop + callbacks vs Rust async/await), so the code differs while
the goals and structure are the same. This corresponds to the Rust **current-
thread** configuration; the multi-thread (#7209) path has no event-loop analog.
Also not ported: the Rust workload's LocalSet startup-init pattern (the tokio
#5020 trigger path) — a C event loop has no runtime-owned local task set to
mirror it.

| # | libevent Workload | Scale | Rust subsystem it mirrors |
|---|---|---|---|
| W1 | Timer Cancel Storm | 500 pairs × 100 iter = 50K register/cancel ops | Timer Ops (requests' timeout-guarded op) |
| W2 | Callback Chain Storm | 100 parents × 10 children, each re-fires | Task Lifecycle + Cooperative Scheduling (fan-out + cooperative compute) |
| W3 | HTTP Filter Echo | 20 requests, new connection per request | Network I/O (echo workload; here HTTP + filter) |
| W4 | Connection Lifecycle | 10 rounds socketpair + `EV_CLOSED` | libevent's own bug-triggering subsystem (no direct Rust analog) |
| W5 | Heartbeat Monitor | 30 ticks × 100ms | Heartbeat (liveness canary) |

## What "combined" does and does not show

**Disclosure**: unlike the Rust suite (whose combined workload carries no
bug-specific code), the C combined test EMBEDS the library's documented
bug-trigger subsystem in the mix — W4 is exactly the issue-reproducing
lifecycle pattern (and it also exists standalone as the dedicated issue test).
A "combined: HANG" verdict is therefore attributable to that subsystem per the
root-cause analyses below, NOT evidence that the neutral mix (W1/W2/W5 + plain
echo) hangs by itself. For libevent the attribution is: the 2.1.5 combined hang comes from W3 (its echo
path deliberately goes through a **filter bufferevent** — the exact #237 trigger
layer), and the 2.1.11 hang from W4 (#984).

Scales also differ deliberately from the Rust workload (e.g. W1 runs 50 K
count-bounded timer ops vs Rust's deadline-bounded loops): what carries over
is the test design — concurrent mix, completion barrier, timeout-=-hang
oracle, fixed-version negative controls — not the constants. Library versions
are built from upstream release tags by `build_deps.sh` (record the resolved
commit hashes if tag stability is a concern).

## Hang Root Causes

- **2.1.5-beta HANG**: W3 triggers issue 237 — `be_filter_ctrl` omits fd event
  registration that `be_socket_ctrl` performs; the server never reads the HTTP
  request through the filter layer.

- **2.1.11-stable HANG**: W4 triggers issue 984 — `evmap_io_active_` preserves
  the internal `EV_ET` flag during event masking; `close()` produces `EPOLLHUP`
  which maps to `EV_READ|EV_WRITE`, but the mask reduces to just `EV_ET`
  (phantom callback). The real `EV_CLOSED` is never delivered, so the
  connection lifecycle monitor hangs.

- **2.1.12-stable PASS**: Both issues fixed; all 5 workloads complete in ~3s.

## Issue 232 (SSL bufferevent)

Tested via standalone reproducer only (not in `combined`).
2.1.5-beta cannot compile SSL against OpenSSL 3.0 (opaque BIO struct),
so this test is SKIP on that version. The bug was fixed before 2.1.11.

## Raw Data

```jsonl
{"test":"issue_237_filter","runtime":"libevent-2.1.5-beta","outcome":"HANG","elapsed_ms":15000}
{"test":"issue_237_filter","runtime":"libevent-2.1.11-stable","outcome":"PASS","elapsed_ms":0}
{"test":"issue_237_filter","runtime":"libevent-2.1.12-stable","outcome":"PASS","elapsed_ms":0}
{"test":"issue_984_phantom","runtime":"libevent-2.1.5-beta","outcome":"HANG","elapsed_ms":15000}
{"test":"issue_984_phantom","runtime":"libevent-2.1.11-stable","outcome":"HANG","elapsed_ms":15000}
{"test":"issue_984_phantom","runtime":"libevent-2.1.12-stable","outcome":"PASS","elapsed_ms":201}
{"test":"issue_232_ssl","runtime":"libevent-2.1.5-beta","outcome":"SKIP","elapsed_ms":0}
{"test":"issue_232_ssl","runtime":"libevent-2.1.11-stable","outcome":"PASS","elapsed_ms":21}
{"test":"issue_232_ssl","runtime":"libevent-2.1.12-stable","outcome":"PASS","elapsed_ms":21}
{"test":"issue_combined","runtime":"libevent-2.1.5-beta","outcome":"HANG","elapsed_ms":15000}
{"test":"issue_combined","runtime":"libevent-2.1.11-stable","outcome":"HANG","elapsed_ms":15000}
{"test":"issue_combined","runtime":"libevent-2.1.12-stable","outcome":"PASS","elapsed_ms":3031}
```
