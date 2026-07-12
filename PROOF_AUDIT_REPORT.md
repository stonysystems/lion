# Proof Audit Report

Executed against PROOF_AUDIT_CHECKLIST.md (English revision, rlimit items removed) over
all 9 verified crates. Method: §0 mechanical gate run in full (ci.sh, forced per-crate
re-verification, mutation regression, all inventories); §1–§3 audited semantically by
three independent reviewers; §4/§4b/§5 checked against the current docs.

**Bottom line: no soundness finding. All checklist items PASS. The only open items are
the §4b packaging steps (executed by the fresh-initial-commit release protocol) and
one low-severity observation (§3.1). Standing disclosed idealizations are unchanged
and listed at the end.**

---

## §0. Mechanical gate — ALL GREEN (1 known FLAG)

| Check | Result |
|---|---|
| `./ci.sh` all 9 crates | PASS — exit 0, 0 errors everywhere |
| Forced per-crate re-verify (touch + verify.sh) | framework-spec 8 / executor-spec 12 / slab 5 / timer-wheel 123 / reactor-spec 57 / reactor 206 / executor 99 / utility 90 / liveness 556 — **1156 verified, 0 errors** |
| `assume(` / `admit(` / `assume(false)` | 0 hits across all 9 crates (direct grep + audit_scan.sh) |
| `Ghost::assume_new` | 0 hits |
| `requires false` | 0 hits |
| `external_body` inventory | 109 attribute lines (reactor 46 / executor 48 / timer-wheel 11 / slab 4 / utility 0), consistent with TCB_and_limitations.md's authoritative count of **126 items** (macro expansion accounts for the difference); README says 126 — three-way consistent |
| `#[verifier::external]` | exactly 1 (lion-slab/src/slab.rs:213 `get_mut`), matches TCB doc |
| `external_fn_specification` / `assume_specification` | 0 hits |
| `verus::trusted` files | 27, matching the checklist's expected count |
| `exec_allows_no_decreases_clause` | 1 site (lion-executor/src/executor/tick.rs:20 `pop_injection`); termination-argument comment present and cross-references TCB §2 |
| unsafe inventory | reactor 1 / executor 15 / utility 31, matching the disclosed distribution |
| Plain-build warning budget | 0 warnings in all 8 buildable crates; lion-liveness plain `cargo build` fails on the known ghost re-export — **disclosed in README** |
| Baseline three-way consistency | README/TCB do not hard-code per-crate verified counts (only the external_body count, which matches the code inventory) |
| Mutation regression | **exact baseline match**: M01–M10 all CAUGHT, C1/C3 SURVIVED (inside declared trust boundary), C2 CAUGHT |
| audit_scan.sh | 1 FLAG: an untracked per-user operational config in the working directory — a §4b packaging item (excluded at packaging time), see below |

---

## §1. Spec definitions (mis-specification) — PASS

**1.1 Top-level theorem.** PASS. The theorem lives in
`lion-liveness/src/composed/proof/assumption_satisfiable.rs` (spec
`end_to_end_liveness_env_N_trace` :3042, proven by
`end_to_end_liveness_env_N_trace_holds` :3134; the paper's mapping table points there).
Literal reading: for every well-formed state where tid has arrived but not yet been
popped, under □env_N along the trace, there exists a budget n such that EVERY n-step
env-good continuation satisfies `end_to_end_response` (∃ log position with poll→Ready
for tid) — quantifier directions correct (∀ continuations = the strong unavoidability
form; ∃ over log positions inside the response). The bound is concrete and
non-circular: `ete_reaches_goal_explicit_bound` (:3147) spells out
n = chunk + cap·chunk with chunk = K + B + C + cap + 2, all env constants + the
premise-supplied cap; nothing in the bound references the goal. The paper states the
theorem word for word, defines chunk with the same formula and a non-circularity
remark (main.tex "Bounded and unavoidable" bullet), lists the corollary in its mapping
table (tab:mapping), and states the head-of-schedule restriction of the arrival
premise inline in the acceptance gloss (the depth-k variant lifts it).

**1.2 Names vs bodies.** PASS. `has_active_timer_with_waker` explanatory comment
present (utilities/spec/log.rs:132–137); `has_active_wakeup_source` is the 4-way OR
(:152–157); `reactor_wake_arrival` is timer-OR-io. The four boundary probe lemmas
exist and verify (log.rs:166–272: `probe_empty_log`, `probe_small_log`,
`probe_dereg_boundary`, `probe_no_poll_begin`), pinning i=0 / i=len−1 / empty-log /
no-poll-begin behavior on concrete logs.

**1.3 Timer/io dereg asymmetry.** PASS. Intent comment at log.rs:38–43 (any-result
dereg counts; asymmetry with reactor-side `is_succ_deregister_*` explicitly
intentional); paper proof sketch states the same split.

**1.4 Vacuous-definition probes, triggers, opaque boundary.** PASS. True/false-side
satisfiability covered by the satisfiability lemmas + probes; no never-matching trigger
found; opaque and closed specs all have live reveal sites, bodies spot-checked against
their comments.

**1.5 Accessors & recommends.** PASS. lion-reactor-spec accessors return `arbitrary()`
on non-matching event types (lion-reactor-spec/src/events.rs, accessor section — same
convention as executor-spec): an unspecified value can never be proven equal to
anything, so a wrong-typed event cannot spuriously satisfy a guard like
`get_*_rid(l[j]) == rid` even though rid 0 is a valid nat. All consumers additionally
guard with the matching `is_*_at` in the same clause. All main-chain `recommends`
respected at call sites (17 hits inventoried).

**Cross-crate spec consistency.** PASS (1 disclosed note).
- The shared-crate extraction is clean: liveness's framework/executor/reactor spec
  modules are thin `pub use` re-export shims with no shadow bodies.
  `timestamps_strictly_increasing` has a single definition
  (lion-reactor-spec/src/log.rs:468), re-exported by lion-liveness
  (composed/spec/assumptions.rs:23, where the clock-granularity disclosure comment
  lives), so the env core and the reactor-side proofs provably use the same spec fn.
- **Note (disclosed, unmechanized)**: `executor_inv`/`reactor_inv` exist both
  model-side and impl-side; impl-side is a strict superset (safe direction), but
  nothing machine-checks impl-inv ⇒ model-inv — rides on the disclosed informal
  correspondence. Acceptable as long as the disclosure stays (it does: README, TCB
  doc, and main.tex all state it).

---

## §2. Assumptions (circularity & over-assumption) — PASS

**2.1 Inventory + classification.** PASS. Full table produced (assumptions.rs specs,
env_N clauses, composed_progress modeled clauses, contract assumption fields). Every
(S)-tagged item — the three `*_drain_step` fair-drain membership clauses and the
composition-framework alignment clauses — carries a written why-not-derivable
justification (progress.rs headers, wake_queues.rs headers, TCB §2). Every (E)/(U)
assumption is bounded (K/B/C env constants, cap, n tick-ends); the retired predicates
(`wake_delivers_here` etc.) have 0 code hits, matching the "RETIRED" claim.

**2.2 Circularity.** PASS. Drain OCCURRENCE is derived
(`single_progress_has_drain_{reactor_wake,task_wake,deferred}` in
executor/proof/bounded_drain_poll.rs — real proofs), drain MEMBERSHIP is the disclosed
modeled residue; the taskwake chain was traced end-to-end confirming the split
(occurrence from the proven lemma, membership from the assumption, Drain→FIFO→poll
derived). No assumption consequent asserts the conclusion except
`bounded_poll_count_here_with_bound` — the standard user-completion shape, firing only
under `count ≥ cap`, where accumulating cap polls is itself derived. Bound
non-circular.

**2.3 Over-strength.** PASS. `timer_resources_remain_active` is the weakened
current-poll-owned form. `timestamps_strictly_increasing` is the known disclosed
clock-granularity idealization (open by decision: disclose, don't weaken) —
disclosure comments confirmed at the definition site, the re-export site, and TCB
§2. Realistic-trace exclusions examined (io cancellation, cleanup, rid reuse,
never-ready io, mid-await abort, same-millisecond reads): each either in-domain via its
guard or disclosed as domain pruning.

**2.3b Call-site audit.** PASS. Every live env clause is consumed only on the
external-arrival / user-behavior side; `queue_length_bounded` feeds the derived FIFO
drainage lemma (bounds the wait, never substitutes for drain/poll derivation).

**2.4 Joint satisfiability.** PASS. `env_N_satisfiable` + all four wake-path witnesses
prove `ete_reachable_N` with the FULL env_N filter at every trace state — the whole
assumption set is jointly satisfied on real multi-step pending→wake→poll→Ready traces.
TCB axiom pairs spot-checked for contradiction (ghost-log frame axioms are per-call
disjoint; the clock clamp is verified code, and its non-strictness vs env strictness is
the disclosed idealization, a subset relation, not a contradiction).

**Assumption minimality.** PASS. Every env-core conjunct except one is consumed by a
derivation lemma (`env_holds_at_state_core`, assumption_satisfiable.rs:235). The one
exception, `tid_unique`, is retained deliberately and carries an explicit
DOCUMENTATION CONJUNCT annotation at the definition site: it mirrors the
ledger-enforced pop-uniqueness the implementation proves, keeps the executor
contracts' `assumption_fn` meaningful, excludes no real trace, and is discharged by
every witness. The five executor-spec AsyncContract objects are annotated in
`lion-executor-spec/src/contracts/mod.rs` as paper-facing packaging of each contract's
trigger/response/assumption triple — the liveness derivations consume the component
spec fns directly, and no proof attests the records themselves.

---

## §3. Proof rigor & vacuity — PASS, 1 observation

**3.1 Inhabitation witnesses.** PASS. All four exist and are non-trivial 3-state traces
with ~15-event concrete executor logs (pending→drain→FIFO→poll→Ready), two-sided
(trigger/response proven false at s0): `b_domain_inhabited`
(inhabitation_goal_wake.rs), `bio_` (io), `d_` (defer), `t_` (taskwake); plus the
stuttering family `b_domain_inhabited_at_any_n` (inhabitation_budget.rs, covers every
n ≥ 2, and the proof-instantiated n* ≥ 2 always) and the immediate-completion witness
`depth_domain_inhabited` (inhabitation_depth.rs). Witness requires match TCB §2's
disclosure word for word (`get_max_queue_length ≥ 1`; timer path additionally
`gap ≥ 3`); not silently strengthened. The not-ready branch (the load-bearing one) is
inhabited via `arrival_witness`; `taskwake_arrival_within` retains its standalone
non-vacuous discharge.

- **Observation (low severity, no action forced)**: the top theorem's defensive
  already-ready branch (`response ∧ ¬trigger ∧ wf`) is plausibly empty-domained (a
  poll→Ready without a prior pop is likely excluded by well-formedness). Harmless — the
  branch is trivially discharged and not load-bearing — but the honest answer to a
  reviewer is "defensive, likely uninhabited".

**3.2 requires-false / orphans / RID apparatus.** PASS. 0 `requires false`. Orphan scan
over the proof fns in composed/proof/: every uncalled proof fn is an intentional,
annotated root — the four wake-path witness roots, the satisfiability roots, the
theorem entry points, the explicit-bound corollary, and `composed_progress_witness`
(inhabitation.rs:661), which carries an INTENTIONAL UNCALLED ROOT comment identifying
it as the minimal anti-vacuity witness for the transition relation itself (a bare idle
tick from the empty state, independent of the four wake paths). Zero unexplained
orphans. RID-reuse apparatus: 18 `[RID-REUSE DISABLED]` markers across 6 files;
`free_rids.pop()`/all `push` sites commented out; `free_rids` provably empty;
`free_rids_wf` retained LIVE over the empty list (in `alloc_resource_id`'s contract,
preservation lemmas actively called) — matching both the checklist's description and
the TCB doc verbatim.

**3.3 Case-split completeness / choose discipline.** PASS. The wakeup cascade's final
`else` asserts `has_pass_waker_in_current_poll` backed by `has_active_wakeup_source`
(the exact 4-way OR of the guards), derived from `pending_poll_inv` + the utilities
wakeup_guarantee invariant — not from an env assumption. All `choose` sites swept
(150): every exists is either derived or traces to one of the three disclosed (E)
arrival/readiness assumptions (io readiness, timer fire, taskwake membership) — nothing
undisclosed.

**3.4 SMT soundness signals.** PASS. 5+ `assert ... by` blocks in the composed chain
checked: opaques properly revealed before assertion; the empty-domain foralls in the
witnesses are intentional (proving trigger/response absence on empty logs). Zero
`broadcast`/`broadcast_forall` in the proof crates (only the vstd hash-axioms group in
timer-wheel). No decreases obligation bypassed via `external`.

**3.5 Toolchain pin.** PASS. Verus pinned to `0.2025.11.15.db81a74` (setup.sh),
installed binary matches, verus.config points at it; README documents the flow and
names the bundled solver version explicitly (Z3 4.12.5) in the trust section.

---

## §4. TCB & honesty — PASS

- TCB inventory: TCB_and_limitations.md is the authoritative source (126 items, four
  trust kinds, per-item postcondition tables); README lists the trusted base including
  toolchain+solver and the single `#[verifier::external]` item. Consistent with the
  code inventories above.
- Informal model↔impl correspondence: stated in README, the TCB doc, AND main.tex
  ("Scope of Trust"). PASS.
- Known limitations disclosed: RID no-reuse ⟹ unbounded slab growth + generational-id
  plan (TCB §2); clock-granularity idealization (TCB §2); drain membership modeled
  (TCB §2); witness conditionality on env-constant lower bounds (TCB §2);
  `pop_injection` termination exemption (TCB §2 + code comment). The io-side
  anchor question is closed: `io_remains_active_assumption` anchors before-waker
  (reuse-tolerant, not leftmost); the only residual leftmost anchor is
  `timer_remains_active_assumption`, which is off the live env path.
- Theorem↔code mapping table: main.tex tab:mapping present and complete — it covers
  the top theorem, the depth variant, the explicit step bound
  (`ete_reaches_goal_explicit_bound`), preservation, joint satisfiability, all five
  non-vacuity witnesses, the cross-task arrival non-vacuity witness, and the derived
  drain-occurrence lemmas.

## §4b. Release hygiene

- **Packaging protocol (standing decision)**: the public repository is
  published from a fresh initial commit; untracked per-user operational files
  in the working directory (the benchmark scripts read a gitignored local
  configuration) are excluded at packaging time.
- LICENSE: present — LICENSE-APACHE + LICENSE-MIT at the repo root, matching
  Cargo.toml's `MIT OR Apache-2.0`.
- Junk sweep: `cl/` is gone; remaining in working dir: `__pycache__/`
  (gitignored), `count_all.py`, `count_lines.py`, `HANG_FIXING_STORY.md` —
  decide keep/drop at packaging time.
- Paper micro figures (a)(d): regeneration from the current reference
  batches pending on the paper side.

## §5. Reproducibility — PASS

One-command verification (`./ci.sh` / per-crate `./verify.sh`) with README-documented
prerequisites and expected time ("a few minutes"); Verus pinned to an exact release
(0.2025.11.15.db81a74, Z3 4.12.5) via setup.sh + verus.config; CI workflow present
(.github/workflows/verify.yml); doc builds standalone (lion-liveness/doc/build.sh,
PDF rebuilt and in sync with the code); plain-build caveat for lion-liveness
prominently documented in the README.

---

## Open items

1. **Packaging (standing protocol)**: publish from a fresh initial commit,
   excluding untracked per-user operational files. Paper micro figures (a)(d)
   regeneration from the current reference batches pending on the paper side.
2. **Observation (low severity)**: the top theorem's defensive already-ready branch is
   plausibly empty-domained; not load-bearing, no witness claimed for it. [§3.1]

Standing open-by-decision items (disclosed): clock-granularity idealization; modeled
drain membership; witness env-constant conditionality; RID no-reuse interim cost
(generational-id plan on file).
