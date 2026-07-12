# micro reference dataset #2 (clean-clone validation run)

Second reference batch, collected from a **fresh GitHub clone**
(commit `ede47094`, `PROVENANCE.txt`) on zoo-002 (EPYC 7702P) by
`../../collect_paper_data.sh` (STAGES includes micro; paper protocol,
10 s x 10 runs, MICRO_BATCHES=1). Raw per-run CSVs plus the auto-rendered
figure (`micro_bench.pdf/png`). Compare against `../ref-result` (batch #1 on
the same anchor machine): same regime — Lion ahead at 1K/5K timer loads,
~93% at 10K, and the tokio-part 5.0 M ops/s plateau (see `../README.md`)
reproduces.
