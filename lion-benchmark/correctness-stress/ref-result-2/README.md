# correctness-stress reference dataset #2 (clean-clone validation run)

Second reference matrix, collected on zoo-002 from a **fresh GitHub
clone** (commit `ede47094`) by `./run.sh` (REPS=3, HEATMAP=1) with zero manual
steps. Identical verdicts to `../ref-result`: tokio 1.21 current-thread
3/3 HANG (issue #5020), tokio 1.42/1.44 multi-thread 3/3 HANG (issue #7209),
lion and the fixed-version control (tokio 1.52.3) 0/3 everywhere. The C-port
matrices (libevent/libuv, run in the same pipeline) also reproduced their
`summary.md` verdicts: bug versions hang 3/3 deterministically, fixed versions
pass. `events.tsv` + `stress_heatmap.pdf` are this run's regenerable heatmap
chain.
