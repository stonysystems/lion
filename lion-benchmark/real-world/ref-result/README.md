# real-world reference dataset #3 (post-remediation validation run)

Third reference batch, collected on zoo-002 (client zoo-004) from a **fresh
GitHub clone** at commit `72c44640` — the first batch on the code that includes
the evaluation-audit remediation (park-friendly Lion worker shutdown in the
pingora fork, lion-axum without a direct tokio dependency, hardened harnesses).
Same one-command pipeline as `../ref-result-2`:

```bash
STAGES=realworld ./collect_paper_data.sh
```

Purpose: (a) confirm the remediation caused no performance regression,
(b) re-validate that the whole pipeline runs end-to-end from a clean clone.

## Consistency with the earlier batches

Envelope 91.1%–122.1% of Tokio (11/11 rows) vs 94.0%–117.9% (`../ref-result`)
and 95.9%–118.6% (`../ref-result-2`). Per-row agreement is within each cell's
historical noise:

- **Pingora** (the app most affected by the worker-shutdown change):
  101.5% / 100.1% of Tokio vs 97.0% / 101.9% in batch #2 — no regression at
  saturation; Lion is marginally faster than in batch #2.
- **Axum cross** rows remain link-saturated (both runtimes within 0.1% — see
  the dual-deployment note in `../README.md`); **Axum local** rows remain the
  runtime-bound evidence: 122.1% / 108.0% / 110.5% vs 118.6% / 107.8% / 112.1%
  in batch #2.
- **rumqtt P2P** is this batch's envelope low end (91.1%); that cell carries
  the suite's largest variance in every batch (batch #1: ±45.2K/±33.0K;
  batch #2: ±31.6K/±40.5K; here the Tokio arm happened to land a
  low-variance high mean).

Layout matches `../ref-result-2`: per-app `*_raw.csv` (per-run rows, no
averaging-away) + `*_summary.csv` (trim-2 mean ± std, recomputable from the
raw rows) + `PROVENANCE.txt` (commit, host, kernel, governor, RTT, protocol),
plus the exported paper table (`table.md` / `table.tex` / `table.csv`).
