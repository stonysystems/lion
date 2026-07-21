#!/usr/bin/env python3
"""Single-column paper figure: head-of-line vs capacity (CV=5.3).

Three lines, p99 normalised to the peak p99 so the y-axis is dimensionless:
  Tokio, inline        -- work-stealing baseline
  Lion, inline         -- head-of-line blocking, no mitigation
  Lion, yield-chunked  -- cooperative-yield mitigation

Reads inline + chunk sweeps (each RUNS>=3); points are per-cell medians, whiskers
min/max over runs. Tokio-inline is taken from --inline; Lion-chunked from --chunk.

Usage: plot_paper.py --inline results/sweep10 --chunk results/sweep10_chunk
"""
import argparse, csv, statistics
from collections import defaultdict
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import LogLocator, FuncFormatter, NullFormatter

plt.rcParams.update({
    "font.size":9,"font.family":"serif","axes.labelsize":9,"axes.titlesize":9,
    "xtick.labelsize":8,"ytick.labelsize":8,"legend.fontsize":7.6,
    "lines.linewidth":1.4,"figure.dpi":300,"legend.frameon":True,
    "legend.handlelength":1.8,"legend.borderpad":0.3,"legend.labelspacing":0.25,
})
TOKC,LIOC,CHUNKC="#e07b39","#9aa5b1","#1b6ca8"
RHOS=["0.2","0.35","0.5","0.65","0.8","0.9"]

def load(p):
    g=defaultdict(list)
    for r in csv.DictReader(open(p+"/work_stealing_raw.csv")):
        if r["cv_nominal"]=="8": g[(r["rho_target"],r["runtime"])].append(r)
    return g

def pctl(v, p):
    """Linear-interpolated percentile of a sorted list."""
    if len(v) == 1:
        return v[0]
    i = p / 100.0 * (len(v) - 1)
    lo = int(i); frac = i - lo
    return v[lo] if lo + 1 >= len(v) else v[lo] * (1 - frac) + v[lo + 1] * frac

def raw(g,rt):
    # Whiskers are the interquartile range (25th-75th pct) of the per-run p99,
    # not min/max: with 10 runs min/max just tracks the single worst outlier and
    # widens with sample count, which is the opposite of showing precision. IQR
    # is the robust run-to-run spread of the p99 measurement itself.
    xs,med,lo,hi=[],[],[],[]
    for r in RHOS:
        k=(r,rt)
        if k not in g: continue
        v=sorted(float(x["p99_ms"]) for x in g[k])
        xs.append(statistics.median(float(x["util_measured"]) for x in g[k]))
        med.append(statistics.median(v)); lo.append(pctl(v,25)); hi.append(pctl(v,75))
    return xs,med,lo,hi

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--inline",required=True); ap.add_argument("--chunk",required=True)
    ap.add_argument("--out",default=None)
    a=ap.parse_args()
    gi,gc=load(a.inline),load(a.chunk)
    sers={"ti":raw(gi,"tokio"),"li":raw(gi,"lion"),"lc":raw(gc,"lion")}
    NORM=max(max(s[3]) for s in sers.values())

    def band(ax,S_,c,mk,ls,lab,lw=1.4,al=1.0,z=2):
        x,m,lo,hi=S_; m=np.array(m)/NORM; lo=np.array(lo)/NORM; hi=np.array(hi)/NORM
        ax.errorbar(x,m,yerr=[m-lo,hi-m],color=c,marker=mk,ls=ls,lw=lw,ms=3.8,
                    capsize=1.6,elinewidth=0.9,alpha=al,label=lab,zorder=z)

    fig,ax=plt.subplots(figsize=(3.45,2.05))
    band(ax,sers["ti"],TOKC,"s","--","Tokio, inline",z=3)
    band(ax,sers["li"],LIOC,"o","-","Lion, inline",lw=1.1,al=.9,z=2)
    band(ax,sers["lc"],CHUNKC,"o","-","Lion, yield-chunked",z=4)
    ax.set_yscale("log"); ax.grid(alpha=.3,which="both",lw=0.4)
    ax.set_xlabel("measured CPU utilisation")
    ax.set_ylabel("p99 latency (Norm.)")
    ax.legend(loc="upper left")
    ax.set_xlim(0.25,0.9); ax.set_ylim(0.14,1.08)
    ax.yaxis.set_major_locator(LogLocator(base=10,subs=[2,3,5,10]))
    ax.yaxis.set_major_formatter(FuncFormatter(lambda v,_: f"{v:g}"))
    ax.yaxis.set_minor_formatter(NullFormatter())
    fig.tight_layout(pad=0.3)
    out=a.out or (a.chunk+"/chunk_paper")
    fig.savefig(out+".pdf",bbox_inches="tight")
    fig.savefig(out+".png",bbox_inches="tight",dpi=300)
    print(f"peak p99 (norm ref) = {NORM:.0f} ms  ->  {out}.pdf")
    # runs-per-cell + throughput sanity, for the caption
    n=min(len(gi[(RHOS[0],'tokio')]), len(gc[(RHOS[0],'lion')]))
    print(f"runs/cell = {n}")

if __name__=="__main__": main()
