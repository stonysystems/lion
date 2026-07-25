| Workload            |        Tokio |         Lion | Lion/Tokio |
|---------------------|--------------|--------------|------------|
| rumqtt Fanout       |      775±3/s |     801±11/s |     103.3% |
| rumqtt Fanin        |   521.8±8.8K |   519.6±2.3K |      99.6% |
| rumqtt P2P          |  520.1±11.7K |  493.4±28.6K |      94.9% |
| Pingora Low-conc    |    69.2±1.3K |    69.0±2.3K |      99.8% |
| Pingora High-conc   |    64.3±1.2K |    66.1±1.8K |     102.8% |
| Pingora Large-10KB  |    12.6±0.1K |    12.9±0.0K |     102.0% |
| Axum (cross) API    |    27.8±0.0K |    27.8±0.0K |     100.0% |
| Axum (cross) Static |     1788±0/s |     1788±0/s |     100.0% |
| Axum (cross) Mixed  |    7108±10/s |    7128±11/s |     100.3% |
| Axum (local) API    |    46.2±0.9K |    54.9±1.2K |     118.9% |
| Axum (local) Static |    22.9±0.3K |    24.5±0.4K |     106.6% |
| Axum (local) Mixed  |    39.7±0.7K |    43.0±0.8K |     108.2% |

envelope: 94.9% – 118.9% of Tokio (12/12 rows with data)
