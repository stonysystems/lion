#!/bin/bash
# Mechanical audit scan (PROOF_AUDIT_CHECKLIST §0 + §4b greppable items), all crates.
# Any line starting with FLAG requires action before open-sourcing.
set -uo pipefail
cd "$(dirname "$0")/.."
CRATES="lion-framework-spec lion-executor-spec lion-reactor-spec lion-slab lion-timer-wheel lion-reactor lion-executor lion-utility lion-liveness"
flag() { echo "FLAG: $*"; FLAGS=$((FLAGS+1)); }
FLAGS=0

echo "== assume/admit (expect none) =="
for c in $CRATES; do
  hits=$(grep -rEn "assume\(|admit\(" $c/src 2>/dev/null | grep -vE "//|assume_specification" || true)
  [ -n "$hits" ] && flag "$c has assume/admit:" && echo "$hits"
done

echo "== Ghost::assume_new (expect none) =="
hits=$(grep -rn "Ghost::assume_new" --include="*.rs" */src 2>/dev/null || true)
[ -n "$hits" ] && flag "Ghost::assume_new present:" && echo "$hits"

echo "== rlimit > 50 inventory (policy: <=50 for new proofs; legacy corpus must be justified in TCB_and_limitations.md) =="
hi=$(grep -rn "verifier::rlimit" --include="*.rs" */src 2>/dev/null | grep -vE "rlimit\((50|[1-4]?[0-9])\)" | grep -v "^\s*//" || true)
n=$(echo "$hi" | grep -c . || true)
max=$(echo "$hi" | grep -oE "rlimit\([0-9]+\)" | grep -oE "[0-9]+" | sort -n | tail -1)
echo "  $n items > 50 (max: rlimit($max)); per-file histogram:"
echo "$hi" | sed "s/:.*//" | sort | uniq -c | sort -rn | head -8 | sed "s/^/  /"
# Disposition executed (user decision: high rlimit values acceptable;
# blanket rationale in TCB_and_limitations.md §2) — inventory stays informational.
echo "  (rlimit debt justified in TCB_and_limitations.md §2; not a FLAG)"

echo "== exec_allows_no_decreases_clause (each needs a termination-argument comment) =="
grep -rn "exec_allows_no_decreases" --include="*.rs" */src 2>/dev/null || echo "  none"

echo "== verus::trusted file inventory =="
n=$(grep -rln "verus::trusted" --include="*.rs" */src 2>/dev/null | wc -l)
echo "  $n files (audit list against TCB_and_limitations.md trust categories)"

echo "== unsafe inventory =="
for c in $CRATES; do
  n=$(grep -rn "unsafe" $c/src --include="*.rs" 2>/dev/null | grep -vE "//" | wc -l)
  [ "$n" != "0" ] && echo "  $c: $n"
done

echo "== external_body attribute lines (grep-aux; authoritative counts in TCB_and_limitations.md) =="
for c in lion-reactor lion-executor lion-timer-wheel lion-slab lion-utility; do
  n=$(grep -rn "verifier::external_body" $c/src 2>/dev/null | grep -v "^\s*//" | wc -l)
  echo "  $c: $n attribute lines"
done

echo "== requires false (expect none) =="
hits=$(grep -rn "requires false" --include="*.rs" */src 2>/dev/null || true)
[ -n "$hits" ] && flag "requires false present:" && echo "$hits"

echo "== inhabitation witnesses present =="
grep -rln "domain_inhabited" lion-liveness/src | sed 's/^/  /'

echo "== secrets sweep (working dir incl. untracked; expect none) =="
hits=$(grep -rinE "password|passwd|BEGIN (RSA|OPENSSH)" --include="*.txt" --include="*.sh" --include="*.toml" . 2>/dev/null | grep -vE "audit_scan|AUDIT_CHECKLIST|\.venv|real-world/|CHANGELOG" || true)
[ -n "$hits" ] && flag "possible secrets:" && echo "$hits" | head -5

echo "== LICENSE =="
[ -f LICENSE ] || [ -f LICENSE.md ] || flag "LICENSE file missing"

echo "== plain-build warning budget =="
for c in lion-reactor lion-executor; do
  w=$(cd $c && cargo build --release 2>&1 | grep -c "^warning" || true)
  [ "$w" -gt 10 ] && flag "$c: $w build warnings (budget: <10)" || echo "  $c: $w warnings"
done

echo ""
echo "=== $FLAGS FLAG(s). Semantic-layer review (checklist §1-§3) is separate. ==="
exit $([ "$FLAGS" -eq 0 ] && echo 0 || echo 1)
