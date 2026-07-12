# ref-result — cross-machine reference dataset (paper protocol)

Collected with the hardened protocol; every number regenerable via:

    cd lion-benchmark && STAGES=realworld ./collect_paper_data.sh
    # (topology in real-world/hosts.env — copy hosts.env.example)

| | |
|---|---|
| Server | zoo-002, AMD EPYC 7702P (128 t, 1 NUMA), kernel 5.15.0-185, governor schedutil |
| Client | zoo-004 (Xeon E5-2683 v4), wrk 4.2.0 / mqtt-benchmark, RTT ~0.3–0.5 ms |
| Protocol | interleaved A-B (run outer, runtime inner, server restart per cell), 30 s × 10 runs |
| Statistic | trim-2 mean ± std (drop 2 lowest + 2 highest of 10) — same as micro/plot.py |
| Code | commit c6736367 (post timer-optimization freeze c9cb87e2 + Connect::poll fix) |

`table.{md,tex,csv}` is the exported paper table (regenerate with
`tools/export_paper_table.py .`). Per-app subdirectories hold the per-run raw CSV (no averaging-away), the
trim-2 summary, and the machine/protocol PROVENANCE captured at collection
time. Known deviation from the old paper text: the pingora sweep is
conns={50,200} (no 10 KB payload workload — tracked as a paper-revision item);
the link RTT is ~0.4 ms, not the 2.4 ms stated in the old setup line.

Axum local-deployment rows (`axum/axum_local_{raw,summary}.csv`) were
backfilled later — batch #1 predated the dual-deployment runner; same
host, protocol, and topology (see `axum/PROVENANCE.txt`). With them the table
is 11/11 rows, envelope 94.0–117.9%, matching `../ref-result-2`.
