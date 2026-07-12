#!/usr/bin/env python3
"""Reproduce the paper's micro benchmark figure from raw per-run CSV data.

Layout: two groups side-by-side, matching the paper.
  Group 1 (Single-Thread): (a) Timer Cancel, (b) TCP Echo, (c) Filesystem I/O
  Group 2 (Multi-Thread):  (d) Timer Scaling, (e) TCP Scaling

Reads the five raw CSVs produced by run.sh (timer_st_raw.csv, timer_mt_raw.csv,
tcp_st_raw.csv, tcp_mt_raw.csv, fs_raw.csv). Bars/points are trimmed means over
the runs (drop 2 highest + 2 lowest); error bars are the trimmed-set stdev.

Usage:
  ./plot.py --data results/<stamp>-batch1   # read a collected batch, write its micro_bench.{pdf,png}
  ./plot.py --data results/full      # plot a run's dir, write the figure into it
  ./plot.py --out /tmp/fig.pdf       # custom output path (.png written alongside)
"""

import os
import csv
import argparse
import statistics
from collections import defaultdict

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import matplotlib.lines as mlines
from matplotlib.legend_handler import HandlerTuple
import matplotlib.gridspec as gridspec
import numpy as np

plt.rcParams.update({
    'font.size': 22,
    'font.family': 'serif',
    'axes.labelsize': 22,
    'axes.titlesize': 24,
    'xtick.labelsize': 18,
    'ytick.labelsize': 18,
    'legend.fontsize': 16,
    'figure.dpi': 300,
    'lines.linewidth': 2.5,
    'lines.markersize': 8,
})

COLORS = {
    'Tokio': '#4C72B0',
    'Tokio-Steal': '#2B5D9E',
    'Tokio-Part': '#55A868',
    'Lion': '#C44E52',
    'Lion-Part': '#D4756A',
    'Monoio': '#8172B2',
}


def load_csv(path):
    with open(path) as f:
        return list(csv.DictReader(f))


def group_ops(rows, key_fn):
    groups = defaultdict(list)
    for row in rows:
        ops = row.get('ops_per_sec', '').strip()
        if not ops.isdigit():
            continue
        groups[key_fn(row)].append(float(ops))
    return groups


def autoscale_y(ax):
    """Data-driven y-limits: 0 baseline, 12% headroom above the tallest
    artist. Hardcoded limits tuned to one machine silently clip data from
    another (an EPYC fs panel rendered empty under a 40-180K window)."""
    ax.relim()
    ax.autoscale(axis='y')
    lo, hi = ax.get_ylim()
    ax.set_ylim(0, hi * 1.12)


def trimmed_stats(vals, trim=2):
    if not vals:
        return 0.0, 0.0
    if len(vals) <= 2 * trim:
        return statistics.mean(vals), (statistics.stdev(vals) if len(vals) > 1 else 0.0)
    s = sorted(vals)
    t = s[trim:-trim]
    return statistics.mean(t), statistics.stdev(t)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description='Reproduce the paper micro benchmark figure.')
    ap.add_argument('--data', required=True,
                    help='directory containing the five *_raw.csv files (e.g. results/<stamp>-batch1)')
    ap.add_argument('--out', default=None,
                    help='output PDF path (a .png is written alongside). '
                         'Default: micro_bench.pdf inside the --data directory.')
    args = ap.parse_args()
    if args.out is None:
        args.out = os.path.join(args.data, 'micro_bench.pdf')

    d = args.data
    timer_st = load_csv(os.path.join(d, 'timer_st_raw.csv'))
    timer_mt = load_csv(os.path.join(d, 'timer_mt_raw.csv'))
    tcp_st = load_csv(os.path.join(d, 'tcp_st_raw.csv'))
    tcp_mt = load_csv(os.path.join(d, 'tcp_mt_raw.csv'))
    fs_data = load_csv(os.path.join(d, 'fs_raw.csv'))

    fig = plt.figure(figsize=(22, 5.2))
    outer = gridspec.GridSpec(1, 2, figure=fig, width_ratios=[3, 2], wspace=0.18)

    gs_left = gridspec.GridSpecFromSubplotSpec(1, 3, subplot_spec=outer[0], wspace=0.40)
    gs_right = gridspec.GridSpecFromSubplotSpec(1, 2, subplot_spec=outer[1], wspace=0.45)

    ax_a = fig.add_subplot(gs_left[0])
    ax_b = fig.add_subplot(gs_left[1])
    ax_c = fig.add_subplot(gs_left[2])
    ax_d = fig.add_subplot(gs_right[0])
    ax_e = fig.add_subplot(gs_right[1])

    fig.subplots_adjust(left=0.05, right=0.98, bottom=0.28, top=0.78)

    pad_x = 0.022
    pad_bot = 0.02
    pad_top = 0.10
    for gs, title in [(outer[0], 'Single-Thread'), (outer[1], 'Multi-Thread Scaling')]:
        pos = gs.get_position(fig)
        rect = mpatches.FancyBboxPatch(
            (pos.x0 - pad_x, pos.y0 - pad_bot - 0.20),
            pos.width + 2 * pad_x,
            pos.height + pad_bot + pad_top + 0.20,
            boxstyle='round,pad=0.012', linewidth=1.2,
            edgecolor='#888888', facecolor='none', transform=fig.transFigure,
            clip_on=False)
        fig.patches.append(rect)
        fig.text(pos.x0 + pos.width / 2, 0.91, title,
                 ha='center', fontsize=20, fontweight='bold')

    # ═══════════════════════════════════════════
    # (a) Timer Cancel — single-thread
    # ═══════════════════════════════════════════
    ax = ax_a
    g = group_ops(timer_st, lambda r: (r['runtime'], r['load']))
    loads = ['1000', '5000', '10000']
    load_labels = ['1K', '5K', '10K']

    for rt_name, color in [('tokio', COLORS['Tokio']), ('lion', COLORS['Lion']), ('monoio', COLORS['Monoio'])]:
        means, stds = [], []
        for load in loads:
            m, s = trimmed_stats(g[(rt_name, load)])
            means.append(m / 1e6)
            stds.append(s / 1e6)
        x = np.arange(len(loads))
        w = 0.25
        offset = {'tokio': -w, 'lion': 0, 'monoio': w}[rt_name]
        ax.bar(x + offset, means, w, yerr=stds, color=color, capsize=2, error_kw={'linewidth': 0.8})

    ax.set_xticks(np.arange(len(loads)))
    ax.set_xticklabels(load_labels)
    ax.set_xlabel('Concurrent Timers')
    ax.set_ylabel('M ops/s')
    ax.set_title('(a) Timer Cancel')
    autoscale_y(ax)

    # ═══════════════════════════════════════════
    # (b) TCP Echo — single-thread
    # ═══════════════════════════════════════════
    ax = ax_b
    g = group_ops(tcp_st, lambda r: (r['runtime'], r['load']))
    tcp_loads = ['10', '50', '100', '500']

    for rt_name, color in [('tokio', COLORS['Tokio']), ('lion', COLORS['Lion']), ('monoio', COLORS['Monoio'])]:
        means, stds = [], []
        for load in tcp_loads:
            m, s = trimmed_stats(g[(rt_name, load)])
            means.append(m / 1e3)
            stds.append(s / 1e3)
        x = np.arange(len(tcp_loads))
        w = 0.25
        offset = {'tokio': -w, 'lion': 0, 'monoio': w}[rt_name]
        ax.bar(x + offset, means, w, yerr=stds, color=color, capsize=2, error_kw={'linewidth': 0.8})

    ax.set_xticks(np.arange(len(tcp_loads)))
    ax.set_xticklabels(tcp_loads)
    ax.set_xlabel('Concurrent Connections')
    ax.set_ylabel('K req/s')
    ax.set_title('(b) TCP Echo')
    autoscale_y(ax)

    # ═══════════════════════════════════════════
    # (c) Filesystem — blocking pool scaling
    # ═══════════════════════════════════════════
    ax = ax_c
    g = group_ops(fs_data, lambda r: (r['runtime'], r['blocking_threads']))
    bts = ['1', '2', '4', '8']
    bts_int = [1, 2, 4, 8]

    for rt_name, color, marker in [('tokio', COLORS['Tokio'], 'D'), ('lion', COLORS['Lion'], 'p')]:
        means, stds = [], []
        for bt in bts:
            m, s = trimmed_stats(g[(rt_name, bt)])
            means.append(m / 1e3)
            stds.append(s / 1e3)
        ms = 6 if marker == 'D' else 7
        ax.errorbar(bts_int, means, yerr=stds, fmt=f'{marker}-', color=color,
                    markersize=ms, capsize=3, capthick=1.2, elinewidth=1.0)

    monoio_vals = g[('monoio', '1')]
    monoio_m, _ = trimmed_stats(monoio_vals)
    ax.axhline(y=monoio_m / 1e3, color=COLORS['Monoio'], linestyle='--', linewidth=1.5, alpha=0.7)
    ax.text(6.5, monoio_m / 1e3 + 4, 'Monoio', fontsize=16, color=COLORS['Monoio'], ha='center')

    ax.set_xticks(bts_int)
    ax.set_xlabel('Blocking Threads')
    ax.set_ylabel('K ops/s')
    ax.set_title('(c) Filesystem I/O')
    autoscale_y(ax)

    # ═══════════════════════════════════════════
    # (d) Timer Scaling — multi-thread
    # ═══════════════════════════════════════════
    ax = ax_d
    g = group_ops(timer_mt, lambda r: (r['runtime'], r['threads']))
    threads = ['1', '2', '3']
    threads_int = [1, 2, 3]

    for rt_name, color, marker, ls in [
        ('tokio', COLORS['Tokio-Steal'], 'o', '-'),
        ('tokio-part', COLORS['Tokio-Part'], 's', '--'),
        ('lion', COLORS['Lion-Part'], '^', '-'),
    ]:
        means, stds = [], []
        for t in threads:
            m, s = trimmed_stats(g[(rt_name, t)])
            means.append(m / 1e6)
            stds.append(s / 1e6)
        ax.errorbar(threads_int, means, yerr=stds, fmt=f'{marker}{ls}', color=color,
                    markersize=10, capsize=3, capthick=1.2, elinewidth=1.0)

    ax.set_xticks(threads_int)
    ax.set_xlabel('Threads')
    ax.set_ylabel('M ops/s')
    ax.set_title('(d) Timer Scaling')
    autoscale_y(ax)

    # ═══════════════════════════════════════════
    # (e) TCP Scaling — multi-thread
    # ═══════════════════════════════════════════
    ax = ax_e
    g = group_ops(tcp_mt, lambda r: (r['runtime'], r['threads']))
    tcp_threads = ['1', '2', '4']
    tcp_threads_int = [1, 2, 4]

    for rt_name, color, marker, ls in [
        ('tokio', COLORS['Tokio-Steal'], 'o', '-'),
        ('tokio-part', COLORS['Tokio-Part'], 's', '--'),
        ('lion', COLORS['Lion-Part'], '^', '-'),
    ]:
        means, stds = [], []
        for t in tcp_threads:
            m, s = trimmed_stats(g[(rt_name, t)])
            means.append(m / 1e3)
            stds.append(s / 1e3)
        ax.errorbar(tcp_threads_int, means, yerr=stds, fmt=f'{marker}{ls}', color=color,
                    markersize=10, capsize=3, capthick=1.2, elinewidth=1.0)

    ax.set_xticks(tcp_threads_int)
    ax.set_xlabel('Threads')
    ax.set_ylabel('K req/s')
    ax.set_title('(e) TCP Scaling')
    autoscale_y(ax)

    # ═══════════════════════════════════════════
    # Group legends
    # ═══════════════════════════════════════════
    left_pos = outer[0].get_position(fig)
    left_handles = [
        (mpatches.Patch(color=COLORS['Tokio']),
         mlines.Line2D([], [], color=COLORS['Tokio'], marker='D', linestyle='-', markersize=9)),
        (mpatches.Patch(color=COLORS['Lion']),
         mlines.Line2D([], [], color=COLORS['Lion'], marker='p', linestyle='-', markersize=10)),
        mpatches.Patch(color=COLORS['Monoio']),
    ]
    left_labels = ['Tokio', 'Lion', 'Monoio']
    fig.legend(
        handles=left_handles, labels=left_labels,
        handler_map={tuple: HandlerTuple(ndivide=None, pad=0.3)},
        loc='lower center', ncol=3,
        frameon=True, framealpha=0.9, edgecolor='lightgray',
        bbox_to_anchor=(left_pos.x0 + left_pos.width / 2, 0.04),
    )

    right_pos = outer[1].get_position(fig)
    right_handles = [
        mlines.Line2D([], [], color=COLORS['Tokio-Steal'], marker='o', linestyle='-', markersize=10),
        mlines.Line2D([], [], color=COLORS['Tokio-Part'], marker='s', linestyle='--', markersize=10),
        mlines.Line2D([], [], color=COLORS['Lion-Part'], marker='^', linestyle='-', markersize=10),
    ]
    right_labels = ['Tokio (stealing)', 'Tokio (partition)', 'Lion (partition)']
    fig.legend(
        handles=right_handles, labels=right_labels,
        handler_map={tuple: HandlerTuple(ndivide=None, pad=0.3)},
        loc='lower center', ncol=3,
        frameon=True, framealpha=0.9, edgecolor='lightgray',
        bbox_to_anchor=(right_pos.x0 + right_pos.width / 2, 0.04),
    )

    out_pdf = args.out
    fig.savefig(out_pdf, bbox_inches='tight')
    print(f'Saved {out_pdf}')

    out_png = os.path.splitext(out_pdf)[0] + '.png'
    fig.savefig(out_png, bbox_inches='tight', dpi=300)
    print(f'Saved {out_png}')


if __name__ == '__main__':
    main()
