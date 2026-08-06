| mutant | build | pass | hang | err | median pass ms |
|---|---|---|---|---|---|
| baseline | OK | 3 | 0 | 0 | 3056 |
| C1-tls-taker-empty | OK | 0 | 3 | 0 | - |
| C2-ghost-log-event-dropped | OK | 3 | 0 | 0 | 3056 |
| C3-mio-register-noop | OK | 0 | 3 | 0 | - |
| M01-elapsed-not-updated | OK | 3 | 0 | 0 | 3058 |
| M02-cascade-skipped | OK | 3 | 0 | 0 | 3059 |
| M03-no-invalidate-min | OK | 3 | 0 | 0 | 3057 |
| M04-scan-skip-upper-levels | OK | 3 | 0 | 0 | 3057 |
| M05-poll-loop-early-return | OK | 0 | 3 | 0 | - |
| M06-next-task-none | OK | 0 | 3 | 0 | - |
| M07-drain-drops-kept | OK | 0 | 3 | 0 | - |
| M08-pop-not-enqueued | OK | 0 | 3 | 0 | - |
| M09-poll-wrong-tid | OK | 0 | 3 | 0 | - |
| M10-ledger-not-marked | OK | 0 | 3 | 0 | - |
