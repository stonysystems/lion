#!/usr/bin/env python3
"""Compare two micro-benchmark OUTDIRs (baseline vs candidate).

Usage: compare.py <baseline_dir> <candidate_dir>

For every *_raw.csv present in both dirs, groups rows by (runtime, threads,
load), computes the trimmed mean of ops_per_sec (drop min & max when >=4 runs,
plain mean otherwise) per group, and reports candidate/baseline delta for the
lion rows. tokio/monoio rows are printed as machine-noise controls.

Gate (TCB-reduction campaign protocol): lion regression > 5% -> INVESTIGATE,
> 10% -> BLOCK. Controls drifting comparably indicate machine noise, not a
real regression.
"""
import csv, sys, os
from collections import defaultdict

def load(d):
  groups = defaultdict(list)
  for fn in sorted(os.listdir(d)):
    if not fn.endswith('_raw.csv'):
      continue
    with open(os.path.join(d, fn)) as f:
      for row in csv.DictReader(f):
        try:
          ops = float(row['ops_per_sec'])
        except (KeyError, ValueError):
          continue
        key = (fn, row['runtime'], row.get('threads', ''), row.get('load', ''))
        groups[key].append(ops)
  return groups

def tmean(xs):
  xs = sorted(xs)
  if len(xs) >= 4:
    xs = xs[1:-1]
  return sum(xs) / len(xs)

def main():
  base, cand = load(sys.argv[1]), load(sys.argv[2])
  worst = 0.0
  print(f"{'benchmark':<22}{'runtime':<12}{'thr':<5}{'load':<7}"
        f"{'base':>12}{'cand':>12}{'delta':>9}")
  for key in sorted(base):
    if key not in cand:
      print(f"{key[0]:<22}{key[1]:<12}{key[2]:<5}{key[3]:<7}  MISSING in candidate")
      continue
    b, c = tmean(base[key]), tmean(cand[key])
    delta = (c - b) / b * 100 if b else 0.0
    mark = ''
    if key[1] == 'lion':
      if delta < -10: mark = '  << BLOCK (>10%)'
      elif delta < -5: mark = '  <- INVESTIGATE (>5%)'
      worst = min(worst, delta)
    print(f"{key[0]:<22}{key[1]:<12}{key[2]:<5}{key[3]:<7}"
          f"{b:>12.0f}{c:>12.0f}{delta:>+8.1f}%{mark}")
  print(f"\nworst lion delta: {worst:+.1f}%")
  sys.exit(1 if worst < -10 else 0)

if __name__ == '__main__':
  main()
