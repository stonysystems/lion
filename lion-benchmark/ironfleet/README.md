# IronFleet IronRSL (Multi-Paxos) — Lion async I/O

Improving a verified system with Lion's async I/O. We keep IronFleet's
Dafny-verified IronRSL Paxos core's **protocol logic unmodified** (two scheduling
constants are adjusted, identically for both configurations — see Measurement
notes) and replace its C# `IoScheduler` with a Lion-based async I/O layer, loaded
into the C# process as a Rust `cdylib` via P/Invoke. The Paxos protocol is
identical in both configurations; only the I/O layer differs.

## Layout

- `lion-io/` — the Lion async I/O `cdylib`.
  - One background OS thread owns a Lion current-thread runtime.
  - The accept loop, per-connection reader/writer tasks, and peer dialing all run
    as async tasks on that runtime (`lion::net` + `lion::spawn` + `lion::time`,
    read/write via tokio's `AsyncRead/Write` ext traits that Lion's stream halves
    implement).
  - The C# thread and the runtime thread exchange packets over thread-safe `flume`
    channels: reader tasks push inbound packets that `lion_io_receive` drains;
    `lion_io_send` pushes outbound messages that writer tasks drain.
  - FFI surface (unchanged from the C# P/Invoke contract):
    `lion_io_create / _destroy / _my_key_hash / _receive / _send / _free_buffer`.
- `ironrsl-app/` — the C# IronRSL app (Dafny-generated Paxos core, unmodified),
  self-contained (`SConstruct`, builds with scons + Dafny 3.4.0 + .NET 6.0). The
  I/O selection lives in `src/Dafny/Distributed/Common/Native/`: `LionIoScheduler.cs`
  (P/Invoke wrapper; imports `ironfleet_io_lion`, i.e. our `libironfleet_io_lion.so`),
  `IoNative.cs` (`CreateWithLion` vs the C# `IoScheduler`), RSL `Program.cs` (the
  `lion=true` server flag), `IoFramework.cs` (C# baseline + TCP_NODELAY fix).
- `run.sh` — build both, run the 3-replica cluster + client, parse throughput/
  latency/peak-CPU. Knobs: `RUNTIME=lion|csharp`, `CONFIG=unpin|1core`,
  `SERVER_HOST`/`CLIENT_HOST`, `NTHREADS`, `DURATION`.
- `tcp_nodelay_fix.md` — the C# baseline runs with TCP_NODELAY (Nagle disabled),
  matching the Lion side.

## Performance

In the unpinned regime the C# Dafny Paxos busy loop occupies ~100% of one core
in both arms; the Lion async I/O tasks add the rest (and the Lion layer's
idle-aware receive lets the host loop yield when the inbound queue is empty —
part of the I/O-layer replacement, see the paper's mechanism paragraph). The
reference batches (`ref-result*/table.md`) measure: ~3.2–3.3K req/s, ~140%
leader CPU, ~2.0× (unpinned) / ~5.8–6.1× (1core) over the C# `IoScheduler`.
`../collect_paper_data.sh` (STAGES=ironfleet) writes one
`.reqlog` + `.cpulog` per {runtime}×{config}×rep under `results/<stamp>-paper/`;
`./export_table.py <results-dir>` recomputes the paper table (trim-2 over reps,
`--format latex` for the tex body) from those raw files. `ref-result/` holds
the reference dataset from the paper topology (replicas on the EPYC anchor,
client remote), with its exported `table.md`.

Measurement notes (both runtimes identically, so ratios are unaffected):

- Throughput is total completed requests / `DURATION`, but the client's worker
  threads sleep 3 s before the first request *inside* that window, so absolute
  req/s is conservative by ~`DURATION/(DURATION-3)` (~10% at the default 30 s).
- "Peak server CPU" is a leader proxy: the max across replicas of per-second
  `ps -o %cpu` samples (process-lifetime average, not instantaneous), sampled
  for the run's duration.
- The Paxos protocol constants differ from upstream IronFleet in two places,
  applied identically to both configurations: `max_batch_size` 32→1 (the
  paper's "no request batching") and `max_log_length` 7→1000
  (`src/Dafny/Distributed/Impl/RSL/ParametersState.i.dfy`). The client is a
  lightweight single-threaded `Socket.Poll` RSL client (`LightRSLClient.cs`),
  shared by both configurations, replacing the upstream 6+-thread client I/O
  so the client is never the bottleneck.

## Setup & run

```bash
# one-time toolchain (Dafny 3.4.0 + .NET 6.0 + scons); cdylib needs only cargo:
SETUP_IRONFLEET=1 ../setup.sh

# localhost, Lion async I/O, unpinned:
./run.sh
# C# IoScheduler baseline:           RUNTIME=csharp ./run.sh
# pin each replica to one core:      CONFIG=1core ./run.sh
# two-host example:                  SERVER_HOST=<server-ip> CLIENT_HOST=<client-ip> \
#                                    SSH_USER=<user> SSH_PASS=... ./run.sh
```

`run.sh` builds the cdylib, builds the C# app (`scons --no-verify`), copies the
`.so` next to the .NET binaries (P/Invoke resolves `ironfleet_io_lion`), generates
certs, starts 3 replicas (with `lion=true`/`false`, optional `taskset`), runs the
client, and parses throughput / latency / peak server CPU. The paper's grid is the
{lion, csharp} × {unpin, 1core} matrix at NTHREADS=2, DURATION=30.
