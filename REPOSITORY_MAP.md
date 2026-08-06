# What is in this repository

Component by component: what each part is, and where it appears in the paper.
The verified runtime is split into crates that each carry their own `verify.sh`;
`ci.sh` runs all of them in dependency order. The README's opening sections
describe the two most interesting ones — `lion-executor` and `lion-reactor` —
and the proof that composes them.

| Component | What it is | Where it appears in the paper |
|---|---|---|
| `lion-executor` | Task scheduling, wakers, the blocking pool — one half of the runtime core, with its executable code mapped onto L2S state and a family of invariants verified over it | the executor half of the runtime-core case study |
| `lion-reactor` | I/O readiness, timer registration and resource-id allocation — the other half of the core | the reactor half of the same case study |
| `lion-liveness` | The composing layer: per-module **Async Contracts** and the glue proof that chains them into the top-level theorem, *"once a task is spawned it is driven to completion"* | the end-to-end liveness theorem |
| `lion-slab`, `lion-timer-wheel` | The leaf data structures the core builds on, verified independently | the leaf-structure layer of the module stack |
| `lion-utility` (contains `lion-utility-spec`) | The verified utilities layer above the core (channels, synchronisation) | the utilities layer |
| `lion-framework-spec`, `lion-executor-spec`, `lion-reactor-spec` | Shared specification crates: the event vocabulary and invariant definitions consumed by *both* the liveness proof and the impl-verified crates, so both sides quantify over the same definitions | the model↔implementation correspondence argument |
| `lion` | The user-facing runtime facade — re-exports `spawn`, `Runtime`, the `#[lion::main]` macro; this is what an application depends on | the drop-in-replacement claim |
| `lion-macro` | The `#[lion::main]` attribute macro | — |
| `lion-benchmark` | Every experiment, each with its own `README.md`, `run.sh` and shipped `ref-result/` + `ref-2/` reference data | the evaluation section |
| `mutation-test` | Proof-sensitivity experiment: does the verifier *reject* liveness-breaking mutants, and do trusted-region controls map the declared TCB boundary | the mutation-testing subsection |
| `TCB_and_limitations.md` | Per-item inventory of everything trusted rather than verified | the trusted-computing-base discussion |
| `HANG_FIXING_STORY.md` | Two liveness incidents hit during development, both outside the verified region | the residual-risk discussion |

Supporting material: `tools/` (audit scripts), `assets/` (figures and the
downloaded upstream issue reports behind the bug study), `count_all.py` (the
line-count table), `verus-toolchain/` (installed by `setup.sh`).

Two further documents cover running the artifact rather than reading it:
[`REQUIREMENTS.md`](REQUIREMENTS.md) (environment, dependencies, resource
budget) and [`EXPECTED_OUTPUT.md`](EXPECTED_OUTPUT.md) (what each step prints).
