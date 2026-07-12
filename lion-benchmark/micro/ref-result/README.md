# ref-result — micro reference dataset (paper protocol)

Collected on the paper anchor machine; regenerate with:

    cd lion-benchmark && STAGES=micro ./collect_paper_data.sh
    cd micro && .venv/bin/python plot.py --data results/<stamp>-batch1

| | |
|---|---|
| Machine | zoo-002, AMD EPYC 7702P (128 t, 1 NUMA), kernel 5.15.0-185, governor schedutil |
| Protocol | DURATION=10 s × RUNS=10 per configuration; trim-2 mean ± std (plot.py) |
| Code | commit c6736367 (post timer-optimization freeze c9cb87e2 + Connect::poll fix) |

Files: the five per-run raw CSVs (no averaging-away), `PROVENANCE.txt` captured
at collection time, and the rendered `micro_bench.{pdf,png}`.

Note: this batch was collected with the extended thread sweep
(`MT_THREADS="1 2 3 4 6 8"`); the paper's panel (d) uses threads 1–3 — the
extra rows are a superset and can simply be filtered. The collector's default
is now the paper-aligned `1 2 3`. See ../README.md ("the 5.0 M ops/s Tokio
plateau") before interpreting the multi-thread timer numbers.
