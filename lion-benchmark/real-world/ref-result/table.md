| Workload            |        Tokio |         Lion | Lion/Tokio |
|---------------------|--------------|--------------|------------|
| rumqtt Fanout       |      777±3/s |      799±1/s |     102.8% |
| rumqtt Fanin        |   516.0±5.5K |   505.9±4.3K |      98.0% |
| rumqtt P2P          |   520.4±4.8K |  474.2±22.3K |      91.1% |
| Pingora Low-conc    |    71.3±1.2K |    71.3±1.1K |      99.9% |
| Pingora High-conc   |    68.7±1.7K |    67.1±2.4K |      97.6% |
| Pingora Large-10KB  |    12.7±0.0K |    12.8±0.1K |     101.0% |
| Axum (cross) API    |    27.8±0.0K |    27.8±0.0K |     100.0% |
| Axum (cross) Static |     1788±0/s |     1788±0/s |     100.0% |
| Axum (cross) Mixed  |    7116±31/s |    7116±14/s |     100.0% |
| Axum (local) API    |    45.7±1.5K |    55.8±0.4K |     122.1% |
| Axum (local) Static |    23.0±0.2K |    24.9±0.3K |     108.0% |
| Axum (local) Mixed  |    40.0±1.1K |    44.1±1.3K |     110.5% |

envelope: 91.1% – 122.1% of Tokio (12/12 rows with data)
