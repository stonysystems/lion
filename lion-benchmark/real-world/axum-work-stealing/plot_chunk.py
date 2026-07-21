#!/usr/bin/env python3
"""Does the thread-per-core-idiomatic fix (yield-chunking) close Lion's gap?

Three lines, CV=5.3:
  Lion inline    (from the main sweep)     -- today's behaviour
  Lion chunked   (from the chunk sweep)    -- yield every N iters
  Tokio inline   (from the chunk sweep)    -- the work-stealing baseline to catch

Prediction under test: chunking converges Lion toward Tokio at low/mid load
(head-of-line blocking removed), but a gap remains at high load (per-core
capacity deficit that only cross-core stealing can fill).

Usage: plot_chunk.py --inline results/sweep --chunk results/sweep_chunk
"""
import argparse, csv, statistics
from collections import defaultdict
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({"font.size":13,"font.family":"serif","axes.titlesize":13,
                     "legend.fontsize":10,"figure.dpi":140})

def load(path, cv="8"):
    g=defaultdict(list)
    for r in csv.DictReader(open(path+"/work_stealing_raw.csv")):
        if r["cv_nominal"]==cv: g[(r["rho_target"],r["runtime"])].append(r)
    return g

def series(g, rt):
    xs,ys,los,his=[],[],[],[]
    for rho in ["0.2","0.35","0.5","0.65","0.8","0.9"]:
        k=(rho,rt)
        if k not in g: continue
        v=sorted(float(x["p99_ms"]) for x in g[k])
        xs.append(statistics.median(float(x["util_measured"]) for x in g[k]))
        ys.append(statistics.median(v)); los.append(v[0]); his.append(v[-1])
    return xs,ys,los,his

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--inline",required=True); ap.add_argument("--chunk",required=True)
    a=ap.parse_args()
    gi,gc=load(a.inline),load(a.chunk)
    fig,ax=plt.subplots(figsize=(7.6,5))
    def draw(g,rt,c,mk,ls,lab,alpha=1.0,lw=2.0):
        x,y,lo,hi=series(g,rt)
        if not x: return
        ax.errorbar(x,y,yerr=[np.subtract(y,lo),np.subtract(hi,y)],color=c,marker=mk,
                    ls=ls,lw=lw,ms=6,capsize=2,alpha=alpha,label=lab)
    draw(gi,"lion","#9aa5b1","o","-","Lion, inline (today)",alpha=.8,lw=1.4)
    draw(gc,"lion","#1b6ca8","o","-","Lion, yield-chunked")
    draw(gc,"tokio","#e07b39","s","--","Tokio, inline (work-stealing)")
    ax.set_yscale("log"); ax.grid(alpha=.3,which="both")
    ax.set_xlabel("measured CPU utilisation"); ax.set_ylabel("p99 latency (ms)")
    ax.set_title("CV=5.3: does yield-chunking close Lion's gap?")
    ax.legend(loc="upper left")
    fig.tight_layout()
    for e in ("pdf","png"): fig.savefig(f"{a.chunk}/chunk_compare.{e}",bbox_inches="tight")
    print(f"wrote chunk_compare.pdf/png -> {a.chunk}")
    print("\n  rho   | lion_inline  lion_chunk  tokio | chunk vs tokio | chunk vs inline")
    for rho in ["0.2","0.35","0.5","0.65","0.8","0.9"]:
        def m(g,rt):
            k=(rho,rt); return statistics.median(float(x["p99_ms"]) for x in g[k]) if k in g else float("nan")
        li,lc,tk=m(gi,"lion"),m(gc,"lion"),m(gc,"tokio")
        print(f"  {rho:<5} | {li:>8.0f} {lc:>11.0f} {tk:>7.0f} | {lc/tk:>6.2f}x       | {lc/li:>5.2f}x")

if __name__=="__main__": main()
