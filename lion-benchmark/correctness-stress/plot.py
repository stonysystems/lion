#!/usr/bin/env python3
"""
Heatmap visualization of runtime events over time.
Usage: python3 plot.py <events.tsv> [--title "..."] [-o output.pdf] [--bin-ms 50]
"""
import argparse
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors
import numpy as np
from collections import defaultdict

MERGED_GROUPS = [
    ('Task Lifecycle',         ['lifecycle']),
    ('Timer Ops',              ['timer']),
    ('Coop.',                  ['coop']),
    ('Heartbeat',              ['heartbeat']),
    ('Network I/O',            ['network']),
]

def parse_events(path):
    events = []
    with open(path) as f:
        f.readline()
        for line in f:
            parts = line.strip().split('\t')
            if len(parts) >= 2:
                events.append((int(parts[0]), parts[1]))
    return events

def plot_heatmap(events, title, output, bin_ms=50):
    plt.rcParams.update({
        'font.family': 'serif',
        'font.serif': ['Times New Roman', 'DejaVu Serif'],
        'font.size': 7,
    })

    all_events = set()
    for _, evt in events:
        all_events.add(evt)

    groups = []
    for label, evts in MERGED_GROUPS:
        present = [e for e in evts if e in all_events]
        if present:
            groups.append((label, present))

    if not groups:
        print("No events found")
        return

    max_ts = max(ts for ts, _ in events) / 1000.0
    n_bins = max(10, int(max_ts / bin_ms) + 1)
    bins = np.linspace(0, max_ts, n_bins + 1)

    by_type = defaultdict(list)
    for ts_us, evt in events:
        by_type[evt].append(ts_us / 1000.0)

    matrix = np.zeros((len(groups), n_bins))
    for i, (label, evts) in enumerate(groups):
        for evt in evts:
            if evt in by_type:
                counts, _ = np.histogram(by_type[evt], bins=bins)
                matrix[i, :] += counts

    log_matrix = np.log10(matrix + 1)

    fig, ax = plt.subplots(figsize=(3.6, 2.0))

    cmap = plt.cm.YlOrRd.copy()
    cmap.set_under('white')

    vmax = max(log_matrix.max(), 1)
    im = ax.imshow(log_matrix, aspect='auto', cmap=cmap,
                   vmin=0.01, vmax=vmax,
                   interpolation='nearest',
                   extent=[0, max_ts, len(groups) - 0.5, -0.5])

    ax.set_yticks(range(len(groups)))
    # Slanted labels: long category names eat horizontal space when flat;
    # 30-degree rotation with top-right anchoring keeps them close to the axis.
    ax.set_yticklabels([g[0] for g in groups], fontsize=5.5, rotation=30, ha='right', va='center', rotation_mode='anchor')

    ax.set_xlabel('Time (ms)', fontsize=6.5, labelpad=2)

    n_ticks = min(8, n_bins)
    tick_positions = np.linspace(0, max_ts, n_ticks + 1)
    ax.set_xticks(tick_positions)
    ax.set_xticklabels([f'{t:.0f}' for t in tick_positions], fontsize=5.5)
    ax.tick_params(axis='both', length=2, pad=1)

    cbar = plt.colorbar(im, ax=ax, pad=0.03, shrink=0.85, aspect=15)
    cbar.set_label('log10(count+1)', fontsize=5.5, labelpad=2)
    cbar.ax.tick_params(labelsize=5)

    total = sum(len(v) for v in by_type.values())

    for spine in ax.spines.values():
        spine.set_linewidth(0.4)

    plt.subplots_adjust(left=0.18, right=0.88, top=0.85, bottom=0.22)
    plt.savefig(output, dpi=300, bbox_inches='tight')
    print(f"Saved: {output} ({total:,} events, {n_bins} bins x {len(groups)} groups)")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('events')
    parser.add_argument('--title', default='Runtime Event Heatmap')
    parser.add_argument('-o', '--output', default='heatmap.pdf')
    parser.add_argument('--bin-ms', type=float, default=50)
    args = parser.parse_args()

    events = parse_events(args.events)
    print(f"Loaded {len(events)} events")
    plot_heatmap(events, args.title, args.output, args.bin_ms)

if __name__ == '__main__':
    main()
