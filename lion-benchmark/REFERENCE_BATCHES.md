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

**The paper's numbers come from batch 2 (`ref-2`).** The name `ref-result` reads
like the reference and has twice sent a reader to the wrong batch, so it is
worth stating plainly: `ref-2` is what the tables and figures were regenerated
from, and `ref-result` is the independent second measurement kept for the
batch-to-batch comparison below. Where the two disagree — `rumqtt P2P` most of
all — the disagreement is the point of shipping both, not an error in either.

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
envelope is `95.1%-122.1%` (batch 1) and `98.8%-118.9%` (batch 2).

Figures here are for rumqtt's **delivered** rate (`sub_mps`), which is what
`tools/export_paper_table.py` reports. An earlier revision of this file quoted
the publish rate; see that script's header for why the publish rate is a
client-side enqueue measure rather than a broker-side one.

`rumqtt P2P` is the widest-spread cell and accounts for both lower bounds. In
batch 2 its ten paired per-run ratios span **83%-107%** (sd 6.5 pp), against
**87%-103%** (sd 5.1 pp) in batch 1; run-to-run CV is 3.0% (tokio) and 5.8%
(lion). Its batch means (95.1%, 98.8%) sit within that spread of each other, so
neither should be quoted as a point estimate without the spread.

P2P is the noisiest cell in the table but not by a wide margin — `Pingora
conns200` reaches CV 4.2-4.8%, and three further cells exceed 3%. (A previous
revision called P2P "an order of magnitude noisier than any other cell"; that
was wrong on the publish rate too, where the gap was ~1.7x.) Treat roughly a
third of the table as unable to resolve differences of a few percent: within
each batch, 15 of 34 comparable cells have a Lion-Tokio gap smaller than the
larger of the two run-to-run standard deviations, and 3 of those reverse sign
between batches. What reproduces across both batches is the parity verdict, not
the per-cell ordering inside the parity band.
