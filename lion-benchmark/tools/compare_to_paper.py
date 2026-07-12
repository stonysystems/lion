#!/usr/bin/env python3
"""Compare freshly collected benchmark summaries against the paper's printed
claims (tab:real-world + the micro timer narrative).

Usage:
  tools/compare_to_paper.py <realworld-outdir-suffix>
    e.g. tools/compare_to_paper.py <UTC-stamp>-xmachine

Reads real-world/{rumqtt,pingora,axum}/results/<suffix>/*_summary.csv and the
newest micro results dir, prints a claim-by-claim table. Paper values are the
ones printed in sections/lion_evaluation.tex (audit inventory).
"""
import csv, sys, glob, os

HERE = os.path.dirname(os.path.abspath(__file__))
RW = os.path.join(HERE, "..", "real-world")

# tab:real-world as printed in the paper (tokio_mean, lion_mean, ratio_pct)
PAPER = {
  ("rumqttd", "W-Fanout"):  (793, 789, 99.4),
  ("rumqttd", "W-Fanin"):   (413, 433, 105.0),
  ("rumqttd", "W-P2P"):     (410, 402, 98.1),
  ("pingora", "conns50"):   (None, None, None),   # paper used 10/500/10KB — protocol drift, ratio-only compare
  ("pingora", "conns200"):  (None, None, None),
  ("axum",    "small"):     (69.5, 74.9, 107.7),  # paper 'api' ~= small (4KB)
  ("axum",    "large"):     (30.1, 29.3, 97.5),   # paper 'static' ~= large (64KB)
  ("axum",    "mixed"):     (51.8, 57.2, 110.5),
}
PAPER_PINGORA_CLAIM = "within 1% of Tokio across all three workloads (:155)"

def load_summary(app, suffix):
    path_glob = os.path.join(RW, app, "results", suffix, "*_summary.csv")
    rows = {}
    for p in glob.glob(path_glob):
        with open(p) as f:
            for r in csv.DictReader(f):
                rows[(r["system"], r["runtime"], r["workload"])] = (
                    float(r["mean"]), float(r["stddev"]))
    return rows

def main():
    if len(sys.argv) < 2:
        print(__doc__); sys.exit(1)
    suffix = sys.argv[1]
    print(f"== real-world vs paper (suffix={suffix}) ==")
    print(f"{'app/workload':<24} {'tokio':>12} {'lion':>12} {'ratio':>8}  paper_ratio  verdict")
    for app in ("rumqtt", "pingora", "axum"):
        rows = load_summary(app, suffix)
        systems = sorted({k[0] for k in rows})
        for system in systems:
            wls = sorted({k[2] for k in rows if k[0] == system})
            for wl in wls:
                t = rows.get((system, "tokio", wl))
                l = rows.get((system, "lion", wl))
                if not t or not l:
                    continue
                ratio = 100.0 * l[0] / t[0] if t[0] else 0
                paper = PAPER.get((system, wl))
                pr = f"{paper[2]:.1f}%" if paper and paper[2] else "n/a"
                verdict = ""
                if paper and paper[2]:
                    verdict = "OK" if abs(ratio - paper[2]) <= 5 else "DRIFT"
                print(f"{system+'/'+wl:<24} {t[0]:>12.1f} {l[0]:>12.1f} {ratio:>7.1f}%  {pr:>10}  {verdict}")
    print(f"\npingora paper claim: {PAPER_PINGORA_CLAIM}")
    print("timer narrative reference (EPYC quick tests, commit c9cb87e2):")
    print("  1K 1.48x lion | 5K lion +46% | 10K lion -6.6% (paper: 2x / tokio+10% / tokio+10%)")

if __name__ == "__main__":
    main()
