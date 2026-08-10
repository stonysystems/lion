# Requirements: environment, dependencies, and resource budget

What a machine needs to build the artifact, verify the proofs, and run the
experiments — and what the reference dataset was collected on. For what each
step *prints*, see [`EXPECTED_OUTPUT.md`](EXPECTED_OUTPUT.md); for how to run an
individual experiment, see its own `README.md` under `lion-benchmark/`.

## 1. The environment behind the reference dataset

Both reference batches (`ref-result/`, `ref-2/`) were collected on the same two
hosts; each experiment's `PROVENANCE.txt` repeats the subset relevant to it.

| | Server / anchor (`zoo-002`) | Load generator (`zoo-004`) |
|---|---|---|
| CPU | AMD EPYC 7702P — 64 cores / 128 threads, 1 socket | not recorded |
| NUMA | 1 node | — |
| Kernel | `5.15.0-185-generic` | — |
| cpufreq governor | `schedutil` | — |
| Runs | rumqtt broker, pingora proxy, axum file server, IronRSL replicas | `wrk`, `mqtt-benchmark`, IronRSL client |

**Link.** 1 Gbps Ethernet between the two hosts; RTT 0.216 ms (ironfleet),
0.284 ms (micro), 0.376 ms (axum) as recorded per experiment. The axum
cross-machine rows in `ref-result/` sit exactly on that ceiling — 27,835 req/s ×
4 KB, 1,788 × 64 KB and 7,109 × 16.4 KB all come to ~930 Mbps — which is why
they report σ ≈ 0 and exactly 100.0% parity.

**Not recorded:** installed memory and NIC model on either host, and the client's
CPU. None of the four experiments is memory-bound on a host of that class (§4
gives measured peaks), and the network ceiling that does bind the axum cross rows
is pinned by the throughput arithmetic above rather than by the part number.

**Toolchain versions are pinned, so they are not environment-dependent:** Rust
1.91.0, Verus 0.2025.11.15.db81a74 (bundling Z3 4.12.5), Dafny 3.4.0, .NET SDK
6.0.

Absolute performance numbers depend on the machine. See the README's "compare
conclusions, not absolute numbers" for what is expected to reproduce.

## 2. What your machine needs

| | |
|---|---|
| OS | Linux x86_64 or macOS arm64/x86_64 (`setup.sh` aborts on anything else). The experiments were only ever run on Linux. |
| Memory | **≥ 16 GB.** Every step but one peaks below 2 GB; the micro benchmark's timer panels reach ~10 GB in a single process — see §4. |
| Disk | ~10 GB all told — see §4. |
| Cores | No minimum. Measurement wall time is set by the protocol, not by core count (§4), so more cores buy build time only. The micro benchmark's multi-thread panels use at most 4 runtime threads. |
| Network | Only for the cross-machine rows: a second host reachable over SSH, on a link whose capacity you know. The paper's rows are 1 GbE; a faster link moves the axum cross-machine ceiling and those rows will no longer be link-bound. |
| Privileges | `sudo` for the system packages in §3 (apt/dnf/pacman; brew on macOS). Everything else installs under `$HOME` or into the repo. |

For a **cross-machine** run, `lion-benchmark/setup.sh` must be run **on the
client host too** — it needs `wrk` locally, and `SETUP_IRONFLEET=1` there as well
for the IronRSL client, which is a .NET app. Nothing else is needed on the
client: the benchmarks ship the scripts and binaries it needs and assume no
shared filesystem.

## 3. Dependencies

All of it is installed by the two `setup.sh` scripts; the list is here so you can
see what will land on the machine before you run them.

**`./setup.sh`** (top level — needed to verify the proofs)

| Component | Version | Installed to |
|---|---|---|
| rustup | latest | `~/.rustup`, `~/.cargo` (only if absent) |
| Rust toolchain | 1.91.0 (pinned by Verus) | `~/.rustup` |
| Verus, bundling Z3 4.12.5 | 0.2025.11.15.db81a74 | `verus-toolchain/` in the repo |

Expects `curl` and `unzip` to already be present; writes `verus.config`.

**`lion-benchmark/setup.sh`** (needed to run the experiments)

| Component | Purpose | Installed to |
|---|---|---|
| `cmake` | native dependencies of the real-world apps (pingora's zlib-ng) | system package manager |
| `wrk` | HTTP load generator (pingora, axum) | system package; if none, built from source into `~/.local/bin` |
| OpenSSL headers (`libssl-dev` / `openssl-devel`) | building upstream libevent for the C differential tests, which enable SSL — the `openssl` binary alone is not enough | system package manager |
| `sshpass` | non-interactive SSH to the client host | system package manager |
| `python3`, `python3-venv` | plotting (aborts if `python3` is missing) | system package manager |
| `matplotlib`, `numpy` | plotting | `lion-benchmark/micro/.venv`, version-bounded by `lion-benchmark/plotting-requirements.txt` |

**`SETUP_IRONFLEET=1 lion-benchmark/setup.sh`** (only for the IronFleet experiment)

| Component | Version | Installed to |
|---|---|---|
| Dafny | 3.4.0 — must be exactly 3.4, not 3.13+ | `~/.dafny/dafny-3.4.0` |
| .NET SDK | 6.0 | `~/.dotnet` |
| scons | latest | `~/.local/bin` (pip `--user`; falls back to a private venv) |

Rust crate dependencies are resolved by cargo from the checked-in `Cargo.lock`
files. The system-package steps warn rather than abort when a package cannot be
installed, so read the tail of `setup.sh`'s output rather than only its exit
code.

**Undoing it.** Both `setup.sh` scripts append a line to `.setup-manifest` for
each thing they actually install, and skip anything already on the machine — so
the manifest is a record of what this artifact added, and nothing else.
`./uninstall.sh` replays it in reverse:

```bash
./uninstall.sh              # dry run: print exactly what would be removed
./uninstall.sh --yes        # remove it
./uninstall.sh --keep-results --yes   # keep experiment output directories
```

It also removes build artifacts (`/tmp/$USER-lion-bench`, per-crate `target/`)
and experiment output directories, which no step "installs" but which are what
cleaning up means in practice. The shipped reference data (`ref-result/`,
`ref-2/`) is never touched, and neither is anything the machine had before
`setup.sh` ran. Run it before deleting the clone.

## 4. Time, disk, and memory

### Wall time

`STAGES="realworld micro stress ironfleet" ./collect_paper_data.sh` takes **~4 h**,
of which **~3.5 h is measurement time fixed by the protocol** — 30 s × 10 runs
per real-world cell, 10 s × 10 runs across the micro benchmark's 48 cells. A
faster machine shortens the builds, not the measurement. To shorten a run, lower
`DURATION` / `RUNS`; that is a different (noisier) measurement, not the paper's.

| Step | Measurement time | Notes |
|---|---|---|
| `setup.sh` (both, with `SETUP_IRONFLEET=1`) | 5–15 min | dominated by downloads (Verus, Dafny, .NET SDK) |
| `./ci.sh` — verify every crate | 1–2 min | 75 s measured; SMT-bound, so it scales with core speed |
| `correctness-stress` | ~4 min | 226 s measured, including five cold cargo builds. 9 of the 30 cells are expected hangs and each costs the full 15 s timeout. |
| `micro` | **~82 min** | 4,948 s measured for 480 runs; the protocol predicts 4,800 s |
| `real-world` — rumqtt | ~42 min | each client invocation runs 4 workloads back to back (the paper reports 3 of them), × 2 runtimes × 10 runs, plus a broker restart per pair |
| `real-world` — pingora | ~34 min | 2,049 s measured (3 cells × 2 runtimes × 30 s × 10 runs, plus a cold pingora build) |
| `real-world` — axum | ~60 min | 3 workloads × 2 deployments × 2 runtimes × 30 s × 10 runs |
| `ironfleet` | ~15 min | 4 cells × 3 reps × 30 s, plus the Dafny/scons build and cert generation |

`ci.sh`, `correctness-stress`, `micro` and `pingora` above are measured
end-to-end; the `rumqtt`, `axum` and `ironfleet` figures are computed from each
runner's protocol constants and calibrated against short runs of the same
scripts. Where both are available they agree closely — the micro benchmark's
protocol predicts 4,800 s against 4,948 s measured.

### Disk

| | |
|---|---|
| Fresh clone | **93 MB** (64 MB worktree + 29 MB `.git`) |
| `verus-toolchain/` (in the repo, from `./setup.sh`) | 95 MB |
| `lion-benchmark/micro/.venv` | 168 MB |
| `~/.rustup` + `~/.cargo` | ~4.1 GB |
| `~/.dafny` + `~/.dotnet` (only with `SETUP_IRONFLEET=1`) | ~0.7 GB |
| Build artifacts, `/tmp/$USER-lion-bench` | 4.8 GB after every experiment has been built |
| **Total** | **~10 GB** |

Build artifacts go under `/tmp` by design (building inside an NFS home is far
slower and collides when several machines share one checkout); override the root
with `BENCH_TARGET_ROOT`.

### Memory

Measured as peak resident set of the single largest process, and as the peak
increase in system-wide memory in use, on a 6-core/12-thread desktop:

| Step | Peak RSS (largest process) | Peak system-wide increase |
|---|---|---|
| `./ci.sh` | 1.10 GB | 1.79 GB |
| `correctness-stress` | 493 MB | 1.18 GB |
| **`micro`** | **14.3 GB** | 15.1 GB |
| `real-world` — pingora | 691 MB | 1.14 GB |
| `real-world` — rumqtt | 1.40 GB | 1.29 GB |
| `real-world` — axum | 457 MB | 496 MB |
| `ironfleet` | 432 MB | 89 MB |

**The micro benchmark's timer panels are the reason for the 16 GB
recommendation.** At the panel (d)/(a) configuration — 10,000 concurrent timers,
6.3 M timer operations per second — Lion's resident set grows linearly with the
length of the run, at ~0.95 GB/s (1.9 GB at 2 s, 4.9 GB at 5 s, 9.5 GB at 10 s;
~152 bytes retained per timer operation). Tokio at the same configuration stays
at 9 MB. This is the memory cost of Lion's monotonic resource-id allocator: the
free-list reuse path is disabled, so the id window grows with the number of
registrations — the code says so at `lion-reactor/src/alloc_verified.rs:10`.
The paper's 10 s runs are unaffected in throughput terms, but a longer
`DURATION` on the timer panels will grow memory in proportion, and a machine
with less than 16 GB may not survive them.
