# real-world reference dataset #2 (clean-clone validation run)

Second reference batch, collected by the full one-command pipeline
from a **fresh GitHub clone** (commit `ede47094`, see per-app `PROVENANCE.txt`)
in the paper topology: servers on zoo-002 (EPYC 7702P), load generator on
zoo-004, 30 s x 10 runs, interleaved A-B. Produced end-to-end by
`../../collect_paper_data.sh` with zero manual steps besides writing
`hosts.env` — this batch exists to validate that the documented flow
reproduces the paper's numbers from scratch.

Same layout as `../ref-result`: per-app raw + summary CSVs, and the exported
`table.{md,tex,csv}`. Envelope this batch: cross-machine rows 95.9–102.5% of
Tokio (paper's ±5% claim), axum local rows 107.8–118.6% (Lion ahead), fully
consistent with `../ref-result` — plus the axum local deployment rows that
batch #1 lacked.
