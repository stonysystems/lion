| Workload            |        Tokio |         Lion | Lion/Tokio |
|---------------------|--------------|--------------|------------|
| rumqtt Fanout       |      774±3/s |      793±2/s |     102.5% |
| rumqtt Fanin        |   522.6±3.2K |  501.3±14.7K |      95.9% |
| rumqtt P2P          |  495.5±31.6K |  485.6±40.5K |      98.0% |
| Pingora Low-conc    |    73.1±1.0K |    71.0±1.2K |      97.0% |
| Pingora High-conc   |    67.8±1.4K |    69.0±4.5K |     101.9% |
| Axum (cross) API    |    27.8±0.0K |    27.8±0.0K |     100.0% |
| Axum (cross) Static |     1787±0/s |     1787±0/s |     100.0% |
| Axum (cross) Mixed  |    7114±14/s |    7121±32/s |     100.1% |
| Axum (local) API    |    45.5±0.3K |    54.0±1.6K |     118.6% |
| Axum (local) Static |    23.2±0.5K |    25.0±0.3K |     107.8% |
| Axum (local) Mixed  |    39.7±0.3K |    44.5±1.1K |     112.1% |

envelope: 95.9% – 118.6% of Tokio (11/11 rows with data)
