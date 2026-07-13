# real-world reference dataset (post-remediation)

The repository's reference batch (historically the third collection batch), collected on zoo-002 (client zoo-004) from a **fresh
GitHub clone** at commit `72c44640` — the first batch on the code that includes
the evaluation-audit remediation (park-friendly Lion worker shutdown in the
pingora fork, lion-axum without a direct tokio dependency, hardened harnesses).
The pingora rows were re-collected afterwards under pingora's canonical LOCAL
topology (single host, conns 50/200 plus the payload10k workload; see
`pingora/PROVENANCE.txt`), replacing the original cross-machine pingora cells.
One-command pipeline:

```bash
STAGES=realworld ./collect_paper_data.sh
```

Purpose: (a) confirm the remediation caused no performance regression,
(b) re-validate that the whole pipeline runs end-to-end from a clean clone.

## Consistency with the earlier batches

Envelope 91.1%–122.1% of Tokio (12/12 rows incl. the local pingora cells) vs 94.0%–117.9% (batch #1)
and 95.9%–118.6% (batch #2; both pruned batches survive in the
evaluation-audit report). Per-row agreement is within each cell's
historical noise:

- **Pingora** (the app most affected by the worker-shutdown change; now the
  local-topology batch): 99.9% / 97.6% / 101.0% of Tokio (conns50 / conns200 /
  payload10k). The superseded cross-machine cells measured 101.5% / 100.1%
  (this batch) and 97.0% / 101.9% (batch #2) — same parity verdict in both
  topologies; a cross-machine control of the payload10k cell gives 100.6%.
- **Axum cross** rows remain link-saturated (both runtimes within 0.1% — see
  the dual-deployment note in `../README.md`); **Axum local** rows remain the
  runtime-bound evidence: 122.1% / 108.0% / 110.5% vs 118.6% / 107.8% / 112.1%
  in batch #2.
- **rumqtt P2P** is this batch's envelope low end (91.1%); that cell carries
  the suite's largest variance in every batch (batch #1: ±45.2K/±33.0K;
  batch #2: ±31.6K/±40.5K; here the Tokio arm happened to land a
  low-variance high mean).

Layout: per-app `*_raw.csv` (per-run rows, no
averaging-away) + `*_summary.csv` (trim-2 mean ± std, recomputable from the
raw rows) + `PROVENANCE.txt` (commit, host, kernel, governor, RTT, protocol),
plus the exported paper table (`table.md` / `table.tex` / `table.csv`).
