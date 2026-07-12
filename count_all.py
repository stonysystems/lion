#!/usr/bin/env python3
import count_lines as cl

DIRS = [
    ("lion-slab", False),
    ("lion-timer-wheel", False),
    ("lion-reactor", False),
    ("lion-executor", False),
    ("lion-utility", False),
    ("lion-liveness", True),   # spec-only: pure proof project
]

total_exec = 0
total_spec = 0
total_trust = 0
total_adapt = 0
total_wrap = 0

print(f"{'Module':<24} {'Exec':>6} {'Spec':>6} {'Trust':>6} {'Adapt':>6} {'Wrap':>6}")
print(f"{'─'*24} {'─'*6} {'─'*6} {'─'*6} {'─'*6} {'─'*6}")

for d, spec_only in DIRS:
    s = cl.scan_directory(d, spec_only=spec_only)
    print(f"{d:<24} {s.exec_lines:>6} {s.spec_proof_lines:>6} {s.trusted_lines:>6} {s.adapter_lines:>6} {s.wrapper_lines:>6}")
    total_exec += s.exec_lines
    total_spec += s.spec_proof_lines
    total_trust += s.trusted_lines
    total_adapt += s.adapter_lines
    total_wrap += s.wrapper_lines

print(f"{'─'*24} {'─'*6} {'─'*6} {'─'*6} {'─'*6} {'─'*6}")
print(f"{'TOTAL':<24} {total_exec:>6} {total_spec:>6} {total_trust:>6} {total_adapt:>6} {total_wrap:>6}")

grand = total_exec + total_spec + total_trust + total_adapt + total_wrap
if grand > 0:
    print(f"\nExec: {total_exec/grand*100:.1f}%  "
          f"Spec: {total_spec/grand*100:.1f}%  "
          f"Trusted: {total_trust/grand*100:.1f}%  "
          f"Adapter: {total_adapt/grand*100:.1f}%  "
          f"Wrapper: {total_wrap/grand*100:.1f}%")
