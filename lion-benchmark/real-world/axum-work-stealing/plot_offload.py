#!/usr/bin/env python3
"""Overlay inline vs spawn_blocking-offload for both runtimes (CV=5.3).

Tests the prediction that moving CPU work off the event loop collapses Lion onto
Tokio: with the heavy work on a shared blocking pool, both arms reduce to
"event loop + shared pool" and the head-of-line blocking that inline placement
causes on a single Lion core disappears.

Usage: plot_offload.py --inline results/sweep --offload results/sweep_offload
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
    rhos=["0.2","0.35","0.5","0.65","0.8","0.9"]
    xs,ys,los,his=[],[],[],[]
    for rho in rhos:
        k=(rho,rt)
        if k not in g: continue
        v=sorted(float(x["p99_ms"]) for x in g[k])
        xs.append(statistics.median(float(x["util_measured"]) for x in g[k]))
        ys.append(statistics.median(v)); los.append(v[0]); his.append(v[-1])
    return xs,ys,los,his

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--inline",required=True); ap.add_argument("--offload",required=True)
    a=ap.parse_args()
    gi,go=load(a.inline),load(a.offload)
    fig,ax=plt.subplots(figsize=(7.5,5))
    styles={("inline","lion"):("#1b6ca8","o","-","Lion, inline"),
            ("inline","tokio"):("#e07b39","s","-","Tokio, inline"),
            ("offload","lion"):("#1b6ca8","o",":","Lion, offload"),
            ("offload","tokio"):("#e07b39","s",":","Tokio, offload")}
    for (mode,rt),(c,mk,ls,lab) in styles.items():
        g=gi if mode=="inline" else go
        x,y,lo,hi=series(g,rt)
        if not x: continue
        alpha=0.45 if mode=="inline" else 1.0
        ax.errorbar(x,y,yerr=[np.subtract(y,lo),np.subtract(hi,y)],color=c,marker=mk,
                    ls=ls,lw=2 if mode=="offload" else 1.4,ms=6,capsize=2,alpha=alpha,label=lab)
    ax.set_yscale("log"); ax.grid(alpha=.3,which="both")
    ax.set_xlabel("measured CPU utilisation"); ax.set_ylabel("p99 latency (ms)")
    ax.set_title("CV=5.3: inline (faded) vs spawn_blocking offload (bold)")
    ax.legend(ncol=2,fontsize=9)
    fig.tight_layout()
    for ext in ("pdf","png"): fig.savefig(f"{a.offload}/offload_compare.{ext}",bbox_inches="tight")
    print(f"wrote offload_compare.pdf/png -> {a.offload}")
    # numeric summary
    print("\n  rho   | inline: lion/tokio | offload: lion/tokio | offload L/T ratio")
    for rho in ["0.2","0.35","0.5","0.65","0.8","0.9"]:
        def m(g,rt): 
            k=(rho,rt); return statistics.median(float(x["p99_ms"]) for x in g[k]) if k in g else float("nan")
        il,it,ol,ot=m(gi,"lion"),m(gi,"tokio"),m(go,"lion"),m(go,"tokio")
        print(f"  {rho:<5} | {il:>6.0f} {it:>6.0f}       | {ol:>6.0f} {ot:>6.0f}        | {ol/ot:>5.2f}")

if __name__=="__main__": main()
