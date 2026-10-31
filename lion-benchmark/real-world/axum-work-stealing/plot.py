#!/usr/bin/env python3
"""Figures for the work-stealing benchmark.

Reads work_stealing_raw.csv (one row per cell) and writes:

  work_stealing.pdf/png   (a) p99 latency vs measured utilisation, both runtimes
                          (b) Lion/Tokio p99 ratio vs measured utilisation
  work_stealing_mech.pdf  per-core utilisation spread -- the mechanism: a
                          thread-per-core runtime leaves cores idle while others
                          are backlogged; work stealing keeps them uniform
  work_stealing_slo.pdf   goodput admissible under a p99 SLO, per CV

The x-axis is the MEASURED utilisation, never the requested rho: on this host
the cores clock from 1.5 to 3.3 GHz depending on load, so the achieved
utilisation departs from the target and only the measurement is trustworthy.

Ratios pair Lion and Tokio within the same (cv, rho, run) cell -- both replay an
identical pre-generated request stream, so the pairing is exact.

Usage:  ./plot.py --data results/<dir>
"""

import argparse
import csv
import os
import statistics
from collections import defaultdict

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({
    "font.size": 16,
    "font.family": "serif",
    "axes.labelsize": 16,
    "axes.titlesize": 17,
    "xtick.labelsize": 13,
    "ytick.labelsize": 13,
    "legend.fontsize": 12,
    "figure.dpi": 130,
})

CV_COLORS = ["#1b6ca8", "#e07b39", "#8e44ad", "#2d8659"]
RT_STYLE = {"lion": dict(marker="o", ls="-"), "tokio": dict(marker="s", ls="--")}


def load(path):
    rows = []
    with open(path) as fh:
        for r in csv.DictReader(fh):
            try:
                r["util"] = float(r["util_measured"])
                r["p99"] = float(r["p99_ms"])
                r["p50"] = float(r["p50_ms"])
                r["cv"] = float(r["cv_realized"])
                r["rho"] = float(r["rho_target"])
                r["sd"] = float(r["percore_util_sd"])
                r["khz"] = float(r["cpu_khz"])
                r["rate"] = float(r["rate_achieved"])
                r["non2xx"] = int(r["non_2xx"])
            except (ValueError, KeyError):
                continue
            if r["p99"] != r["p99"]:          # NaN -> the cell failed
                continue
            rows.append(r)
    return rows


def agg(vals):
    """Median plus min/max whiskers. With 3 repetitions a trimmed mean would
    keep a single value and report a zero stdev, which would be misleading."""
    v = sorted(vals)
    return statistics.median(v), v[0], v[-1]


def by_cell(rows, key):
    """(cv, rho, runtime) -> aggregated key, carrying the measured utilisation."""
    g = defaultdict(list)
    for r in rows:
        g[(r["cv"], r["rho"], r["runtime"])].append(r)
    out = {}
    for k, rs in g.items():
        med, lo, hi = agg([r[key] for r in rs])
        out[k] = dict(val=med, lo=lo, hi=hi,
                      util=statistics.median([r["util"] for r in rs]))
    return out


def fig_main(rows, outdir):
    cells = by_cell(rows, "p99")
    cvs = sorted({r["cv"] for r in rows})
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.5, 5.2))

    for i, cv in enumerate(cvs):
        c = CV_COLORS[i % len(CV_COLORS)]
        for rt in ("tokio", "lion"):
            pts = sorted([(v["util"], v["val"], v["lo"], v["hi"])
                          for (kcv, _, krt), v in cells.items()
                          if kcv == cv and krt == rt])
            if not pts:
                continue
            x, y, lo, hi = zip(*pts)
            ax1.errorbar(x, y, yerr=[np.subtract(y, lo), np.subtract(hi, y)],
                         color=c, capsize=2, lw=1.6, ms=5,
                         label=f"{rt}, CV={cv:.1f}", **RT_STYLE[rt])
    ax1.set_yscale("log")
    ax1.set_xlabel("measured CPU utilisation")
    ax1.set_ylabel("p99 latency (ms)")
    ax1.set_title("(a) tail latency")
    ax1.grid(alpha=0.3, which="both")
    ax1.legend(ncol=2, fontsize=10)

    # (b) paired ratio: same cv/rho/run, identical replayed request stream.
    per_run = defaultdict(dict)
    for r in rows:
        per_run[(r["cv"], r["rho"], r["run"])][r["runtime"]] = r
    ratio = defaultdict(list)
    for (cv, rho, _), d in per_run.items():
        if "lion" in d and "tokio" in d and d["tokio"]["p99"] > 0:
            ratio[(cv, rho)].append((d["lion"]["p99"] / d["tokio"]["p99"],
                                     (d["lion"]["util"] + d["tokio"]["util"]) / 2))
    for i, cv in enumerate(cvs):
        pts = []
        for (kcv, _), vs in ratio.items():
            if kcv != cv:
                continue
            med, lo, hi = agg([v[0] for v in vs])
            pts.append((statistics.median([v[1] for v in vs]), med, lo, hi))
        pts.sort()
        if not pts:
            continue
        x, y, lo, hi = zip(*pts)
        ax2.errorbar(x, y, yerr=[np.subtract(y, lo), np.subtract(hi, y)],
                     color=CV_COLORS[i % len(CV_COLORS)], marker="o", lw=1.8,
                     capsize=2, ms=5, label=f"CV={cv:.1f}")
    ax2.axhline(1.0, color="k", lw=1, ls=":")
    ax2.text(0.02, 1.02, "Lion faster below this line", transform=ax2.get_yaxis_transform(),
             fontsize=10, va="bottom")
    ax2.set_xlabel("measured CPU utilisation")
    ax2.set_ylabel("p99 ratio  (Lion / Tokio)")
    ax2.set_title("(b) cost of not stealing")
    ax2.grid(alpha=0.3)
    ax2.legend()

    fig.tight_layout()
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(outdir, f"work_stealing.{ext}"), bbox_inches="tight")
    plt.close(fig)


def fig_clocknorm(rows, outdir, ref_khz):
    """Clock-normalised tail latency.

    The raw curves are non-monotonic in utilisation -- Tokio's p99 FALLS as load
    rises -- which no queueing model allows. The cause is DVFS: these cores run
    at ~2.2 GHz at 45% utilisation and ~3.1 GHz at 80%, so rising load makes each
    request cheaper faster than queueing makes it dearer.

    Since ~97% of E[S] is CPU-bound (119us of HTTP overhead against 4.3ms of
    SHA-256), scaling each measurement by its own measured clock removes most of
    that artifact:  t_norm = t * f_measured / f_reference.

    This is a DERIVED quantity, not a measurement. It is shown alongside the raw
    figure, never instead of it.
    """
    cvs = sorted({r["cv"] for r in rows})
    for r in rows:
        r["p99n"] = r["p99"] * r["khz"] / ref_khz
    cells = by_cell(rows, "p99n")
    fig, ax = plt.subplots(figsize=(7.2, 5))
    for i, cv in enumerate(cvs):
        for rt in ("tokio", "lion"):
            pts = sorted([(v["util"], v["val"]) for (kcv, _, krt), v in cells.items()
                          if kcv == cv and krt == rt])
            if not pts:
                continue
            x, y = zip(*pts)
            ax.plot(x, y, color=CV_COLORS[i % len(CV_COLORS)], lw=1.6, ms=5,
                    label=f"{rt}, CV={cv:.1f}", **RT_STYLE[rt])
    ax.set_yscale("log")
    ax.set_xlabel("measured CPU utilisation")
    ax.set_ylabel(f"p99 latency, normalised to {ref_khz/1e6:.2f} GHz (ms)")
    ax.set_title("tail latency with DVFS removed")
    ax.grid(alpha=0.3, which="both")
    ax.legend(fontsize=10, ncol=2)
    fig.tight_layout()
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(outdir, f"work_stealing_clocknorm.{ext}"), bbox_inches="tight")
    plt.close(fig)


def read_ref_khz(data_dir):
    """Reference clock = the one SEC_PER_ITER was calibrated at."""
    for cand in (os.path.join(data_dir, "..", "calibration.env"),
                 os.path.join(data_dir, "calibration.env")):
        if os.path.exists(cand):
            for line in open(cand):
                if line.startswith("CALIB_CLOCK_KHZ="):
                    return float(line.split("=", 1)[1])
    return None


def fig_mech(rows, outdir):
    """Per-core utilisation spread: the direct mechanistic evidence."""
    cells = by_cell(rows, "sd")
    cvs = sorted({r["cv"] for r in rows})
    fig, ax = plt.subplots(figsize=(7, 5))
    for i, cv in enumerate(cvs):
        for rt in ("tokio", "lion"):
            pts = sorted([(v["util"], v["val"]) for (kcv, _, krt), v in cells.items()
                          if kcv == cv and krt == rt])
            if not pts:
                continue
            x, y = zip(*pts)
            ax.plot(x, y, color=CV_COLORS[i % len(CV_COLORS)], lw=1.6, ms=5,
                    label=f"{rt}, CV={cv:.1f}", **RT_STYLE[rt])
    ax.set_xlabel("measured CPU utilisation")
    ax.set_ylabel("stdev of per-core utilisation")
    ax.set_title("load imbalance across cores")
    ax.grid(alpha=0.3)
    ax.legend(fontsize=10)
    fig.tight_layout()
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(outdir, f"work_stealing_mech.{ext}"), bbox_inches="tight")
    plt.close(fig)


def fig_slo(rows, outdir, slos=(50, 100, 200)):
    """Goodput admissible under a p99 SLO -- the latency result as throughput.

    For each runtime and CV, the highest achieved rate whose p99 stayed under the
    SLO. Reported as a rate, not interpolated: with a 6-point rho grid the value
    is the best MEASURED operating point, so it understates both arms equally.
    """
    cells = by_cell(rows, "p99")
    rates = by_cell(rows, "rate")
    cvs = sorted({r["cv"] for r in rows})
    fig, axes = plt.subplots(1, len(slos), figsize=(4.6 * len(slos), 4.6), sharey=True)
    if len(slos) == 1:
        axes = [axes]
    width = 0.36
    for ax, slo in zip(axes, slos):
        for j, rt in enumerate(("tokio", "lion")):
            vals = []
            for cv in cvs:
                ok = [rates[(cv, rho, rt)]["val"]
                      for (kcv, rho, krt), v in cells.items()
                      if kcv == cv and krt == rt and v["val"] <= slo]
                vals.append(max(ok) if ok else 0.0)
            ax.bar(np.arange(len(cvs)) + (j - 0.5) * width, vals, width,
                   label=rt, color=("#e07b39" if rt == "tokio" else "#1b6ca8"))
        ax.set_xticks(range(len(cvs)))
        ax.set_xticklabels([f"{c:.1f}" for c in cvs])
        ax.set_xlabel("realized CV")
        ax.set_title(f"p99 $\\leq$ {slo} ms")
        ax.grid(alpha=0.3, axis="y")
    axes[0].set_ylabel("admissible rate (req/s)")
    axes[0].legend()
    fig.tight_layout()
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(outdir, f"work_stealing_slo.{ext}"), bbox_inches="tight")
    plt.close(fig)


def sanity(rows):
    """Report the things that would invalidate the comparison, rather than
    letting them pass silently into a figure."""
    print("\n== sanity ==")
    bad = [r for r in rows if r["non2xx"] > 0]
    print(f"  cells with non-2xx responses : {len(bad)} / {len(rows)}")
    for r in bad[:5]:
        print(f"    {r['runtime']} cv={r['cv']} rho={r['rho']}: {r['non2xx']} non-2xx")

    # Clock parity between the arms is the assumption the ratio metric rests on.
    per = defaultdict(dict)
    for r in rows:
        per[(r["cv"], r["rho"], r["run"])][r["runtime"]] = r
    dl = [(d["lion"]["khz"] / d["tokio"]["khz"])
          for d in per.values() if "lion" in d and "tokio" in d and d["tokio"]["khz"] > 0]
    if dl:
        print(f"  clock ratio lion/tokio       : median {statistics.median(dl):.3f} "
              f"(min {min(dl):.3f}, max {max(dl):.3f})")
        if max(abs(x - 1) for x in dl) > 0.05:
            print("    WARNING: >5% clock difference between arms — the ratio metric is")
            print("             partly measuring frequency, not scheduling. Report this.")

    # Did the load generator actually deliver the requested rate?
    miss = [r for r in rows if r["rate"] > 0 and
            abs(r["rate"] - float(r["rate_target"])) / float(r["rate_target"]) > 0.05]
    print(f"  cells >5% off target rate    : {len(miss)} / {len(rows)}")
    for r in miss[:5]:
        print(f"    {r['runtime']} cv={r['cv']} rho={r['rho']}: "
              f"asked {r['rate_target']}, got {r['rate']:.0f}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", required=True, help="results dir with work_stealing_raw.csv")
    a = ap.parse_args()
    raw = os.path.join(a.data, "work_stealing_raw.csv")
    rows = load(raw)
    if not rows:
        raise SystemExit(f"no usable rows in {raw}")
    print(f"loaded {len(rows)} cells from {raw}")
    sanity(rows)
    fig_main(rows, a.data)
    fig_mech(rows, a.data)
    fig_slo(rows, a.data)
    ref = read_ref_khz(a.data)
    if ref:
        fig_clocknorm(rows, a.data, ref)
        print(f"\nwrote work_stealing{{,_mech,_slo,_clocknorm}}.pdf/png -> {a.data}")
    else:
        print("\n  (no calibration.env found — skipping the clock-normalised figure)")
        print(f"wrote work_stealing{{,_mech,_slo}}.pdf/png -> {a.data}")


if __name__ == "__main__":
    main()
