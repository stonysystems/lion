# ironfleet reference dataset (post-remediation)

The repository's reference batch (historically the third collection batch), collected on the paper topology (3 replicas on zoo-002,
client on zoo-004) from a **fresh GitHub clone** at commit `72c44640`,
including a from-scratch C#/Dafny build, via:

```bash
STAGES=ironfleet ./collect_paper_data.sh
```

First batch collected with the hardened harness: `run.sh` now aborts on a
non-ready replica, and every run archives a per-replica `.arm` file recording
which I/O scheduler actually ran (all `lion_*.arm` files here carry
"Using Lion async IO scheduler" from all three replicas; `csharp_*.arm`
record the marker's absence — the C# `IoScheduler` arm).

## Consistency with the earlier batches

| Metric | batch #1 (pruned) | batch #2 (pruned) | this batch (`ref-result/`) |
|---|---|---|---|
| Lion unpin req/s | 3275 | 3244 | 3273 |
| Lion 1core req/s | 1970 | 1985 | 2005 |
| Peak leader CPU (Lion unpin) | 139% | 142% | 140% |
| Lion/C# throughput (unpin) | 1.97× | 1.98× | 1.99× |
| Lion/C# throughput (1core) | 5.76× | 6.09× | 6.00× |

Contents: one `.reqlog` + `.cpulog` + `.arm` per {runtime}×{config}×rep,
`PROVENANCE.txt`, and `table.md` exported by `../export_table.py` (trim-2 over
reps) from these raw files.
