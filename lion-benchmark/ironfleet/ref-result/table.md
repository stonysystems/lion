| Metric | Lion unpin | Lion 1core | C# unpin | C# 1core |
|---|---|---|---|---|
| Throughput (req/s) | 3275 | 1970 | 1661 | 342 |
| Avg latency (ms) | 0.51 | 0.87 | 1.03 | 5.09 |
| Peak server CPU (%) | 139 | 87 | 512 | 102 |

Lion/C# throughput (unpin): 1.97x

Lion/C# throughput (1core): 5.76x
reps per cell: {('csharp', '1core'): 3, ('csharp', 'unpin'): 3, ('lion', '1core'): 3, ('lion', 'unpin'): 3}
