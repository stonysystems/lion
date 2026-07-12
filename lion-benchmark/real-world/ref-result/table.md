| Workload            |        Tokio |         Lion | Lion/Tokio |
|---------------------|--------------|--------------|------------|
| rumqtt Fanout       |      778±1/s |      798±4/s |     102.5% |
| rumqtt Fanin        |   528.0±2.8K |   505.2±5.5K |      95.7% |
| rumqtt P2P          |  489.7±45.2K |  482.6±33.0K |      98.5% |
| Pingora Low-conc    |    74.1±2.7K |    71.3±2.9K |      96.1% |
| Pingora High-conc   |    71.8±1.5K |    67.4±3.8K |      94.0% |
| Axum (cross) API    |    27.8±0.0K |    27.8±0.0K |     100.0% |
| Axum (cross) Static |     1788±0/s |     1788±0/s |     100.0% |
| Axum (cross) Mixed  |    7098±25/s |    7103±27/s |     100.1% |
| Axum (local) API    |    46.7±0.9K |    55.0±1.7K |     117.9% |
| Axum (local) Static |    22.8±0.2K |    24.7±0.3K |     108.5% |
| Axum (local) Mixed  |    41.3±1.3K |    44.5±0.7K |     107.9% |

envelope: 94.0% – 117.9% of Tokio (11/11 rows with data)
