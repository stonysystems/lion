# ref-result — correctness-stress reference results

Collected with REPS=3, TIMEOUT=15 s, on two machines; regenerate with:

    cd lion-benchmark/correctness-stress && ./run.sh    # HEATMAP=1 by default

| runtime | current | multi |
|---|---|---|
| tokio 1.21.0  | **3/3 HANG** (issue #5020) | 0/3 PASS |
| tokio 1.42.0  | 0/3 PASS | **3/3 HANG** (issue #7209) |
| tokio 1.44.0  | 0/3 PASS | **3/3 HANG** (issue #7209) |
| tokio 1.52.3 (fixed-version negative control) | 0/3 PASS | 0/3 PASS |
| lion | 0/3 PASS | 0/3 PASS |

Identical matrices on both machines: `results-zoo002.jsonl` (EPYC 7702P) and
`results-zoo004.jsonl` (Xeon E5-2683 v4 — the machine on which the
`Connect::poll` glue hang was originally caught; see HANG_FIXING_STORY.md at
the repo root). The bug-carrying versions hang deterministically under this
workload; the fixed-version control and Lion pass everywhere.

`events.tsv` is the captured event log of one lion "current" run (~19 K
events over the 3 s deadline) and `stress_heatmap.pdf` its rendering by
`plot.py` — both produced by the `HEATMAP=1` path of `run.sh`, so the figure
is regenerable end-to-end.
