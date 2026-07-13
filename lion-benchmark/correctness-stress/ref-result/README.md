# correctness-stress reference dataset (post-remediation)

The repository's reference matrix (historically the third collection batch), collected on zoo-002 from a **fresh GitHub clone** at
commit `72c44640` — the first stress batch on the reworked Lion facade
(`MultiRuntime` workers park on a `lion::sync::oneshot` shutdown receiver
instead of busy-spinning a self-waking future). Verdicts are identical to
the pruned batches #1 and #2 (recorded in the evaluation-audit report):

| runtime | current | multi |
|---|---|---|
| tokio 1.21.0 | **3/3 HANG** (issue #5020) | 0/3 PASS |
| tokio 1.42.0 | 0/3 PASS | **3/3 HANG** (issue #7209) |
| tokio 1.44.0 | 0/3 PASS | **3/3 HANG** (issue #7209) |
| tokio 1.52.3 (fixed-version negative control) | 0/3 PASS | 0/3 PASS |
| lion | 0/3 PASS | 0/3 PASS |

Lion holding 0/3 in both configs with PARKED idle workers is the
lost-wakeup regression check for the facade rework: a broken cross-thread
wake path would surface here as hangs.

C ports (same pipeline: `build_deps.sh` + `make` + `run.sh` in each dir),
also identical to the committed `summary.md` matrices:

- `libevent-results.jsonl`: 2.1.5-beta HANG 3/3 on 237/984/combined
  (232_ssl SKIP — OpenSSL 3 incompat, disclosed), 2.1.11-stable HANG 3/3 on
  984/combined, 2.1.12-stable all PASS.
- `libuv-results.jsonl`: v1.43.0 HANG 3/3 on both, v1.44.2 all PASS.

Contents: `results.jsonl` (Rust matrix, per-run rows), `events.tsv` +
`stress_heatmap.pdf` (lion current-run heatmap), the two C-port jsonl files,
and `PROVENANCE.txt`.
