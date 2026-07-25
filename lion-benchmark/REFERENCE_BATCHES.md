# Reference batches

Two independently collected reference datasets ship with this repository, both
from a fresh GitHub clone on the same host (zoo-002, AMD EPYC 7702P, 128
threads, kernel 5.15.0-185, governor schedutil; client zoo-004 where the
topology is cross-machine). Per-experiment `PROVENANCE.txt` files carry the
exact commit, topology and protocol for each pool.

| batch | directory | collected at commit |
|---|---|---|
| 1 | `<experiment>/ref-result/` | `72c44640` (pingora cell: `404b61c`) |
| 2 | `<experiment>/ref-2/` | `fd78fc3` |

Batch 1 keeps the historical directory name `ref-result` because the
evaluation-audit reports refer to it by that name; treat it as "ref-1".

Covered experiments: `micro/`, `real-world/`, `ironfleet/`,
`correctness-stress/`.

## Agreement between the two batches

**micro** — 48 cells compared (trim-2 mean of ops/s per runtime x load).
Worst deviation **2.3%**; all but that one cell agree within ~1%. The
single-machine micro measurement is highly reproducible.

**correctness-stress** — verdicts are *identical*, 30/30 rows:
tokio-1.21 hangs 3/3 on `current` (#5020); tokio-1.42 and tokio-1.44 hang 3/3
on `multi` (#7209); tokio-latest, and Lion in both configs, pass 3/3.

**ironfleet**

| Metric | ref-result | ref-2 |
|---|---|---|
| Lion unpin (req/s) | 3273 | 3330 |
| Lion 1core (req/s) | 2005 | 2005 |
| C# unpin (req/s) | 1646 | 1635 |
| C# 1core (req/s) | 334 | 329 |
| Lion/C# unpin | 1.99x | 2.04x |
| Lion/C# 1core | 6.00x | 6.09x |

**real-world** — parity verdicts agree, but per-cell winners inside the parity
band move between batches, as `real-world/README.md` already notes. The
envelope is `91.1%-122.1%` (batch 1) and `94.9%-118.9%` (batch 2).

`rumqtt P2P` is the one high-variance cell and accounts for both lower bounds.
In batch 2 its ten paired per-run ratios span **78%-118%** (sd 10.7 pp), with
run-to-run CV of 7.2% (tokio) and 8.2% (lion) — an order of magnitude noisier
than any other cell in the table. Its batch means (91.1%, 94.9%) are within
that spread of each other, so neither should be quoted as a point estimate
without the spread. Every other cell is stable to within a few points.
