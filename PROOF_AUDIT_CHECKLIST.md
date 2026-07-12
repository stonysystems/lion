# Pre-Open-Sourcing Audit Checklist — all verified crates

> Scope: all 9 crates covered by `ci.sh` (6 implementation/proof crates + 3 top-level
> shared spec crates; the 4th shared spec crate, lion-utility-spec, is nested under
> lion-utility and verified with it). The mechanical scans in §0 and the TCB inventory
> in §4 must run over ALL crates, not just liveness+reactor.
> The per-crate external_body counts have TCB_and_limitations.md's header as their
> single source of truth; this file does not hard-code the numbers. The definitions of
> the four trust categories (semantic/ghost-log/raw/view) and the item-by-item
> inventory are in that file's §3.

> Purpose: before publishing the formal proof code, systematically flush out the
> problems reviewers are most likely to pounce on. A formal proof "passing" does not
> mean it is "correct" — the three most dangerous classes of problems all survive under
> a green verifier: **(A) mis-specification** (proving the wrong proposition),
> **(B) vacuity** (false premises / empty domain — "any proposition" holds), and
> **(C) circularity** (the assumptions directly or transitively imply the conclusion).
> This checklist is organized along the three dimensions you requested; each item gives
> "why it matters" + "how to check (command/file)".
>
> How to use: every audit starts by running the §0 mechanical gate, then works through
> §1–§3 item by item, and finishes with §4 (honesty of claims) and §5 (reproducibility).

---

## §0. Mechanical gate (first step of every audit; must be all green)

- [ ] `./ci.sh` — all 9 crates at `0 errors`. This is the only authoritative gate
      (lion-liveness's plain `cargo build` has a known ghost re-export failure — before
      open-sourcing this **must be fixed or prominently documented in the README**,
      because it is the first command an external user runs after cloning).
- [ ] `grep -rn "assume(" src/` returns empty. **Any** `assume` is an unproven
      obligation; must be 0 before publishing.
- [ ] `grep -rn "admit(" src/` returns empty. `admit()` outright abandons the proof.
- [ ] `grep -rn "assume(false)" src/` returns empty. This is the #1 source of empty proofs.
- [ ] Inventory `#[verifier::external_body]`: note that grep hits and entry counts are
      **no longer 1:1** (the ghost-log family is macro-generated; one attribute inside
      the macro body covers all expansions) — the authoritative inventory and counting
      convention are in TCB_and_limitations.md's header and §3. Manually check, item by
      item, that each postcondition matches the implementation's semantics.
- [ ] Inventory `#[verifier::external]` / `#[verifier::external_fn_specification]` /
      `assume_specification`: the parts that bypass verification entirely.
- [ ] Inventory **file-level `verus::trusted` markers** (`grep -rln "verus::trusted"`,
      currently 27 files): confirm one by one that each file's content really belongs
      to its declared trust category (utility whole-module glue / type wrappers / OS
      boundary), that it contains **no verus!{} proof code counted as verified**, and
      no undisclosed executable logic.
- [ ] Inventory `#[verifier::exec_allows_no_decreases_clause]` (currently 1 site: the
      drain loop in executor's `pop_injection`): an exec loop is allowed to skip its
      termination proof — for a liveness project this is a sensitive point. Every site
      must have a comment stating its termination argument (this one relies on the
      injection queue being finite / the injection schedule, an implicit assumption
      that must be written down both in the comment and in TCB_and_limitations.md).
- [ ] `grep -rn "Ghost::assume_new"` returns empty (ghost values must be legitimately
      constructed via Ghost(..)).
- [ ] Full unsafe inventory (not just slab): `grep -rn "unsafe" <crate>/src` — currently
      executor 15 sites / utility 31 sites (waker vtable and glue), reactor 1 site.
      Confirm each site is within a disclosed trust category; TCB_and_limitations.md
      should summarize the distribution of these unsafe blocks.
- [ ] **Plain-build warning budget**: `cargo build` warning count (currently 219 for
      reactor). Before open-sourcing, drive it to zero or single digits — a wall of
      warnings is the #1 source of the "sloppy mistakes" impression.
- [ ] Baseline numbers agree three ways: verify output vs TCB_and_limitations.md vs
      README. Mismatched numbers mean someone changed something without updating the docs.
- [ ] **Mutation regression**: `cd mutation-test && ./run.sh` — expected: M01–M10 all
      CAUGHT, C1/C3 SURVIVED, C2 CAUGHT (see the baseline in
      mutation-test/results/matrix.md). Any deviation = some refactor weakened an
      invariant or moved a trust boundary; investigate immediately.

---

## §1. Rigor and soundness of spec definitions (against mis-specification)

> Core risk: the verifier proves a proposition that is **syntactically fine but
> semantically not what you meant**. A definition named `liveness` may in fact be
> trivially true. This is where reviewers most love to poke.

### 1.1 The top-level theorem "reads as intended"
- [ ] Translate the top-level liveness theorem's statement into natural language
      word by word and compare against the paper's claim. **Word by word** — not from
      memory. Ask: if this sentence is true, is it exactly what the paper promises?
      Has anything been quietly weakened (e.g. "eventually polled" weakened to
      "eventually appears in some log")?
- [ ] Is the theorem's conclusion **bounded** liveness? Liveness must come with a
      **concrete step bound**, otherwise "eventually" is a fairness assumption in
      disguise. Check every `bounded_*` contract's bound expression and confirm the
      bound **does not depend on the goal being proven** (otherwise it is a circular
      bound).
- [ ] Are the quantifiers in the conclusion pointing the right way: is it
      `exists trace-suffix. polled` (correct) or accidentally flipped?

### 1.2 Every spec fn lives up to its name
- [ ] For every `spec fn` that enters the top-level theorem, check **name vs body**.
      Known pitfall: `has_active_timer_with_waker` has "with_waker" in its name but the
      body does **not** check the waker (see the comment at
      `utilities/spec/log.rs:130-135` — timer registrations always carry a waker).
      Such name/meaning mismatches must either be renamed or clearly explained in a
      comment, otherwise reviewers will distrust the entire naming scheme.
- [ ] Quantifier-direction audit: any property of the form "at least one source will
      wake" must be an `exists`/disjunction, never a `forall`/conjunction. Re-check in
      particular `has_active_wakeup_source` (four-way OR) and `reactor_wake_arrival`
      (timer OR io). Writing it as `forall` would make the theorem **false** (after a
      timer fires, the io registration is deregistered — not every source can fire).
- [ ] Boundaries / off-by-one: for every spec over log indices (`current_poll_start`,
      `in_current_poll_cycle`, the `0 <= j < i` vs `<= i` in `*_before`), does it
      evaluate as expected at `i = 0`, `i = len-1`, and on the empty log? Write a
      `proof fn` asserting these specs' values on a few small concrete logs, to guard
      against "trivially true/false at the boundary".

### 1.3 Consistency of deregistration/liveness-of-resource criteria (known sensitive point)
- [ ] Re-check that the **semantic asymmetry** between timer and io deregistration
      detection is intentional and documented: timer uses "must re-register in the
      current poll" (`has_timer_registered_in_current_poll`); io uses "no
      deregistration in the whole prefix + waker set in the current poll"
      (`is_io_active`'s `is_io_deregistered_before` scans `0<=j<i`). Confirm the Proof
      Sketch section of `lion-liveness/doc/main.tex` matches the code.
- [ ] The semantic comment on `is_*_deregistered_before` (`log.rs:38-42`: a deregister
      counts for **any** outcome, including failed deregisters) and the asymmetry with
      the reactor-side `is_succ_deregister_*` are **intentional** and commented.

### 1.4 Detecting trivially-true/false specs (vacuous definitions)
- [ ] For every key `spec fn`, ask: does there exist a log that makes it `true`? One
      that makes it `false`? Both must be constructible. A "well-formedness" predicate
      that is **always true** makes the theorem spuriously strong; a premise that is
      **always false** makes the theorem vacuous. Cover the key predicates with
      anti-vacuity witnesses (see §3.1).
- [ ] Trigger sanity: for quantifier-dense specs (`forall|j| ... #![trigger l[j]]`),
      confirm the trigger can actually be instantiated — a **trigger that never
      matches** makes the `forall` unusable (it becomes "free truth" inside proofs).
      For suspicious sites, write a positive witness lemma that forces one instantiation.
- [ ] `open` vs `closed`/`#[verifier::opaque]` boundary: for every opaque spec, confirm
      no proof silently depends on its unfolded form outside of a reveal; also confirm
      the definition body hidden behind the opacity is itself correct (opacity makes a
      wrong definition harder to notice).

### 1.5 Accessors and recommends
- [ ] What do partial accessors (`get_resource_id`, `get_set_waker_interest`, etc.)
      return when the event type does not match? Confirm specs do not become
      accidentally trivially-true on those `None`/default branches.
- [ ] `recommends` is **not enforced by the verifier**. Any spec fn called outside its
      `recommends` premise may return garbage. Search for `recommends` and confirm the
      call sites of key specs satisfy them (or that the spec's value outside its
      recommends is harmless).

---

## §2. Are the assumptions excessive? (against circularity & over-assumption)

> Core risk: assumptions too strong = smuggling in the conclusion (circular), or
> assumptions false = everything vacuous. This is the **primary battleground** where
> reviewers attack credibility. Principle: assumptions may only constrain the
> **external world** and **user task behavior**, never **behavior of the system itself
> that ought to be proven**.

### 2.1 Full inventory of assumptions + classification
- [ ] Enumerate **all** sources of assumptions into one table, each with a one-sentence
      justification:
  - every `pub open spec fn` in `src/composed/spec/assumptions.rs`;
  - the `ensures` of every `#[verifier::external_body]` (they are implicit assumptions);
  - the `assumption` fields of the reactor/executor contracts.
- [ ] Tag every assumption with **one of three** labels:
  - **(E) environment assumption** (timers eventually fire, io eventually becomes
    ready, the outside world eventually spawns / cross-task wakes) — **legitimate**;
  - **(U) user-task-behavior assumption** (a task completes within a bounded number of
    polls, a pending task always arranges a wakeup source) — **legitimate but must be
    bounded**;
  - **(S) assumption about the system's own behavior** — **highly suspect**; these
    should be **proven invariants or contracts**, not assumptions. Every (S) needs an
    explanation of "why it cannot be derived", otherwise delete it.
- [ ] For every (E)/(U): confirm it is **bounded**. An unbounded "eventually" offloads
      the liveness obligation onto the assumption. Focus: the bounds of
      `taskwake_arrival_within`, the injection schedule, `get_max_timer_deadline_gap`, etc.

### 2.2 Circularity — the most fatal
- [ ] For every assumption, ask: does it **directly or transitively imply the
      theorem's conclusion**? Be especially wary of assumptions whose wording comes
      close to the conclusion — "task eventually polled / eventually runnable /
      eventually on waiting list" and the like.
- [ ] Draw a dependency graph: assumption → contract → invariant → theorem. Confirm
      there are **no back-edges** (a property used by the theorem being directly
      assumed true by some assumption).
- [ ] Specifically re-check fairness-style assumptions ("the queue is drained
      infinitely often"): the occurrence of a drain must be **derived**
      (fire→drain→FIFO→poll), never assumed. Confirm the documented claim (TCB doc) that "on the
      delivery side only the external arrivals are assumptions, everything else is
      derived" matches the code (the `*_drain_step` clauses in `wake_queues.rs`).

### 2.3 Assumption strength (over-strong)
- [ ] For every assumption ask: "could it be weaker?" A known positive example:
      `timer_resources_remain_active` was weakened from "EVERY registration must remain
      active" (wrong — it excluded reuse/dereg) to "only current-poll-owned"
      (see its comment in `composed/spec/assumptions.rs`). Reviewers specifically hunt for assumptions that are
      **so strong they exclude real traces** — those make the theorem true but
      inapplicable to real executions.
- [ ] The reverse trap: an **over-strong** assumption can also make the **domain
      empty** (§3). So §2.3 and §3.1 must be checked together: every time an
      assumption is strengthened, re-confirm the §3.1 inhabitation witnesses still
      satisfy it.

### 2.3b Call-site audit of assumptions
- [ ] For every environment/user assumption, grep **all of its call sites**: confirm it
      is only used to discharge obligations about external arrivals / user behavior,
      and is never borrowed to waive an internal system obligation that should have
      been derived (that would be a disguised (S)).

### 2.4 Joint satisfiability (the root of vacuity prevention)
- [ ] Are all assumptions **jointly** satisfiable? Does at least one real trace satisfy
      all assumptions + well_formed simultaneously? This is exactly what the §3.1
      inhabitation witness guarantees. If the assumptions contradict each other, the
      theorem holds over the empty set = fully vacuous.
- [ ] **Joint consistency of the TCB axioms**: contradictory external_body ensures ⟹
      the whole system can prove false (worse than vacuity). For pairs of axioms
      touching the same state (e.g. multiple frame/effect declarations over the same
      field), manually check joint satisfiability; prioritize the strongest-shaped
      ensures (exact-effect style).

---

## §3. Proof rigor & empty-proof prevention (against vacuity)

> Core risk: the theorem is true but holds **over an empty domain**, or a premise is
> always false. The verifier **does not complain** about vacuous proofs.

### 3.1 Anti-vacuity / inhabitation witnesses (most important)
- [ ] The ∀-quantified trace domain of the top-level theorem **must have a nonempty
      witness**: a **concretely constructed real trace** that satisfies all premises
      (well_formed + all assumptions) and actually walks pending→wake→poll→Ready.
      This project already has `b_domain_inhabited` (`inhabitation_goal_wake.rs`,
      timer-wake path). Confirm it **still compiles** and **still satisfies all current
      assumptions** (§2.3: every assumption change must regress this witness).
- [ ] Coverage: do the witnesses cover **every wake path**? the repo documents "all four
      wake witnesses done" (injection / defer / reactor-wake / task-wake). Confirm each
      of the four witnesses exists, compiles, and is non-trivial.
      `grep -rn "domain_inhabited\|inhabited" src/`.
- [ ] **Dischargeability of the witnesses' premises**: the four domain_inhabited
      witnesses are conditional on lower bounds for the `arbitrary()` environment
      constants (e.g. queue capacity ≥ 1), and **no caller can discharge them** —
      confirm this conditionality is explicitly disclosed in TCB_and_limitations.md,
      and that the witnesses' requires have not been silently strengthened.
- [ ] **Proof sensitivity** (structural defense line): the 13-mutation baseline in
      mutation-test/ (see the mutation-regression item in §0).
- [ ] For every key lemma with premises (`H ⟹ G`), at least mentally walk through:
      "is H satisfiable?" For every lemma with strong `requires`, confirm some call
      site can satisfy it with a **genuinely reachable** state; otherwise the lemma is
      green but dead/vacuous.

### 3.2 Premise satisfiability & dead code
- [ ] `grep -rn "requires false\|requires .*false" src/`: any `requires false` lemma is
      vacuous; confirm it is **either deleted or explicitly marked unreachable and off
      the main line**.
- [ ] **Routine cascade sweep after deletions** (rule of thumb): after every batch
      deletion of lemmas, run an uncalled scan over the same files and **iterate to a
      fixpoint** — helpers of dead lemmas become new orphans; piles of orphaned lemmas
      are usually tombstones of past deletions done without a cascade sweep.
- [ ] The disabled RID-reuse apparatus: the reuse branches (`free_rids.pop`/`push`)
      are commented out behind `[RID-REUSE DISABLED]` markers and `free_rids` is
      provably empty, while the `free_rids_wf_*` apparatus is **retained LIVE**
      (in `alloc_resource_id`'s contract and actively-called preservation lemmas,
      maintained over the provably-empty list — it constrains nothing today and is
      ready for the generational-id restoration). Confirm this state and that it
      **does not participate** in current soundness.
      `grep -rn "RID-REUSE DISABLED\|free_rids" ../lion-reactor/src`. Reviewers who see
      swaths of commented-out recycling logic will ask "is this hiding something" — the
      README must proactively explain (see §4).

### 3.3 Case-split completeness
- [ ] The wakeup-source cascade `if timer / else if io / else if defer / else
      pass_waker` (`assumption_satisfiable.rs:1027-1090`): confirm the final `else`
      branch is **guaranteed nonempty by the invariant** (`has_active_wakeup_source`
      minus timer/io/defer necessarily leaves pass_waker). The
      `assert(has_pass_waker_in_current_poll(...))` inside the `else` is the receipt
      for this completeness; confirm it is present.
- [ ] Every `choose |x| P(x)`: confirm `exists |x| P(x)` **has been proven** before the
      `choose` (not taken for free from an assumption). An `exists` taken from an
      assumption sends you back to §2 to check whether that assumption is excessive.

### 3.4 SMT soundness signals
- [ ] `grep -rn "assert(.*) by" src/`: spot-check several `assert ... by { ... }` and
      confirm the `by` block does not pass "by accident" thanks to some opaque spec
      never being revealed.
- [ ] `broadcast` / `broadcast_forall` (if any): confirm they introduce no trigger
      loops or overly broad automatic facts that make downstream proofs "too easy".
- [ ] All spec-recursion `decreases` clauses are present (Verus enforces this, but
      confirm termination is not bypassed via `#[verifier::external]`).

### 3.5 Regression stability
- [ ] Run `./verify.sh` from scratch on a clean checkout (no incremental caches);
      confirm it is genuinely all green.
- [ ] Record the **exact version** of the Verus toolchain (commit/tag). Verus moves
      fast; a version bump can break proofs or **let proofs pass that should fail**.
      Version pinning is a prerequisite for reproducibility (see §5).

---

## §4. TCB & honesty of claims (what reviewers care about most: "are you hiding anything")

> A formal proof's credibility = a clean line between "machine-checked" and
> "trusted by humans". Honest disclosure is more credible than feigned perfection.

- [ ] Explicitly list the **Trusted Computing Base** in the public README:
  - every `external_body` axiom (§0 inventory), each with the postcondition being trusted;
  - the Verus toolchain itself + the SMT solver (Z3 version);
  - the parts ignored via `#[verifier::external]`.
- [ ] Explicitly state that the **model↔impl correspondence is informal**, not a
      mechanized refinement. The TCB doc already says "informal model↔impl
      correspondence, not a mechanized refinement" — this sentence **must appear in the
      paper/README**, otherwise reviewers who discover it will conclude the claim was
      oversold.
- [ ] Proactively disclose **known limitations**:
  - the RID no-reuse downgrade ⟹ `ResourceSlab` grows unboundedly on long runs
    (memory `liveness-rid-no-reuse-genids`);
  - the pre-existing `external_body` items on the reactor side (count per
    TCB_and_limitations.md header);
  - (RESOLVED: `io_remains_active_assumption` was de-leftmosted — t5b anchors
    it before-waker, reuse-tolerant; the only residual leftmost anchor is
    `timer_remains_active_assumption`, which is off the live env path.)
- [ ] A **mapping table** from every theorem in the paper to the lemma name in the code
      (reviewers must be able to locate it in one hop). The contract table +
      theorem↔`proof fn` mapping table (tab:mapping) in `lion-liveness/doc/main.tex`
      are in place; keep them in sync with the code.

---

## §4b. Hard hygiene for open-sourcing ("sloppy mistakes" hotspot; one last pass before packaging)

- [ ] **Credentials and sensitive files**: **untracked files in the working directory
      also end up in packaged artifacts** — the benchmark scripts read per-user
      gitignored configuration (see `hosts.env.example`); sweep the working tree for
      any untracked operational/credential files and exclude them before packaging
      (`tools/audit_scan.sh` has a secrets grep). **Standing release protocol: the
      public repository is published from a fresh initial commit** (squashed from the
      current state; the development repo's history is not rewritten). Rotate any
      operational credential that was ever used during development before release.
- [ ] **LICENSE files** present (LICENSE-APACHE + LICENSE-MIT, matching Cargo.toml's
      `MIT OR Apache-2.0`) and included in the packaged artifact.
- [ ] Clean up junk directories/files unrelated to the project (`cl/`, `__pycache__/`,
      personal scripts); double-check .gitignore; check the git history for internal
      records that need squashing.
- [ ] Paper consistency: the micro figures (a)(d) must be regenerated on the cluster
      with the current code before publishing (the old numbers were inflated by the
      since-fixed scan bug; see baselines/tcb-reduction/05-final/).

---

## §5. Reproducibility (let external reviewers recompute independently)

- [ ] One command reproduces all verification: `./verify.sh`; the README states the
      prerequisites (Verus version, Z3 version, install steps).
- [ ] Pin the Verus toolchain to an exact commit; CI runs `verify.sh` to keep main green.
- [ ] Provide from-zero clean-build instructions, with expected time & resources.
- [ ] `lion-liveness/doc/main.tex` builds standalone (`lion-liveness/doc/build.sh`);
      the PDF stays in sync with the code.

---

## One-shot quick self-check script

The mechanical-layer scan is codified as `tools/audit_scan.sh` (covers all crates,
macro-aware counting, and the greppable items of §0/§4b above). The semantic layer
(the per-spec review of §1–§3) still requires a human.

```bash
./tools/audit_scan.sh   # every FLAG line must be dealt with
```
