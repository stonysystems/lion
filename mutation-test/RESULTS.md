| mutant | build | verify | first failure |
|---|---|---|---|
| C1-tls-taker-empty | OK | SURVIVED | - |
| C2-ghost-log-event-dropped | OK | CAUGHT | src/reactor/park.rs:985 |
| C3-mio-register-noop | OK | SURVIVED | - |
| M01-elapsed-not-updated | OK | CAUGHT | src/wheel.rs:2827 |
| M02-cascade-skipped | OK | CAUGHT | src/wheel.rs:2249 |
| M03-no-invalidate-min | OK | CAUGHT | src/wheel.rs:771 |
| M04-scan-skip-upper-levels | OK | CAUGHT | src/wheel.rs:4056 |
| M05-poll-loop-early-return | OK | CAUGHT | src/executor/tick.rs:225 |
| M06-next-task-none | OK | CAUGHT | src/executor/next_task.rs:34 |
| M07-drain-drops-kept | OK | CAUGHT | src/executor/ext.rs:359 |
| M08-pop-not-enqueued | OK | CAUGHT | src/executor/tick.rs:95 |
| M09-poll-wrong-tid | OK | CAUGHT | src/executor/tick.rs:379 |
| M10-ledger-not-marked | OK | CAUGHT | src/executor/ext.rs:237 |
