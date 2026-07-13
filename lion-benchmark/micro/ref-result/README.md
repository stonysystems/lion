# micro reference dataset #3 (post-remediation validation run)

Third reference batch, collected on the paper anchor machine (zoo-002, AMD
EPYC 7702P) from a **fresh GitHub clone** at commit `72c44640` — the first
batch on the code that includes the evaluation-audit remediation (the Lion
facade's `MultiRuntime` workers now park instead of busy-spinning; the
multi-thread timer benchmark drives that exact code via `MultiHandle::spawn`).
Same pipeline as the earlier batches:

```bash
STAGES=micro ./collect_paper_data.sh
```

## Consistency with the earlier batches

Trim-2 means agree with `../ref-result-2` per-cell across every primitive:

| file | cells | ref3/ref2 range |
|---|---|---|
| timer_st_raw.csv | 9 | 100.0% – 103.2% |
| timer_mt_raw.csv | 9 | 97.4% – 104.4% |
| tcp_st_raw.csv | 12 | 99.6% – 100.2% |
| fs_raw.csv | 3 | 98.2% – 100.5% |

(`timer_mt` — the cells that exercise the reworked `MultiRuntime` — sit inside
the same batch-to-batch noise band as the untouched primitives.)

Contents: per-run raw CSVs (`run` column preserved), `PROVENANCE.txt`
(commit, host, kernel, governor, protocol: 10 s × 10 runs, MT_THREADS=1 2 3),
and the figure rendered from these raws by `../plot.py`.
