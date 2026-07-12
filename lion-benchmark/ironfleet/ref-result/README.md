# ironfleet reference dataset (paper topology)

Collected by `../../collect_paper_data.sh` (STAGES=ironfleet) on the
paper anchor: 3 replicas on zoo-002 (AMD EPYC 7702P), client on zoo-004
(0.26 ms RTT), 3 reps per cell, 30 s each, cells {lion,csharp}×{unpin,1core}.
See `PROVENANCE.txt` for commit/host details.

- `{runtime}_{config}.rN.reqlog` — raw client stdout (one `#req tid seq lat_ms`
  line per completed request); `.cpulog` — per-second `ps -o %cpu` samples of
  the three server processes.
- `table.md` / `table.tex` — exported by `../export_table.py ref-result`
  (trim-2 across reps; with 3 reps that is the per-cell median).

| Metric | Lion unpin | Lion 1core | C# unpin | C# 1core |
|---|---|---|---|---|
| Throughput (req/s) | 3275 | 1970 | 1661 | 342 |
| Avg latency (ms) | 0.51 | 0.87 | 1.03 | 5.09 |
| Peak server CPU (%) | 139 | 87 | 512 | 102 |

Lion/C# throughput: **1.97× unpinned, 5.76× single-core** (paper's original
batch: 1.46× / 4.74×). Same regime as the paper's `tab:ironfleet` — Lion is
faster at a fraction of the CPU (139% vs 512% unpinned), and the gap widens
under a one-core budget — with the C# `IoScheduler` baseline landing lower on
this machine/batch than in the paper's run, so the ratios here are larger.
