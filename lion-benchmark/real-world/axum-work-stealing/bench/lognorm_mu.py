#!/usr/bin/env python3
"""Solve for the log-normal mu that gives a TRUNCATED distribution the target mean.

The load script (bench/work_cv.lua) samples per-request CPU cost n from a
log-normal with a nominal coefficient of variation CV, rejecting draws above
CAP*mean so a single request cannot occupy a core for seconds at a time.

Plain truncation lowers the mean by a CV-dependent amount (10.9% at CV=8,
CAP=100), which would confound the CV sweep with a load sweep. This solves for
the mu whose truncated distribution has mean exactly MEAN, and also reports the
REALIZED CV after truncation -- always below the nominal CV, and the number that
should label the plotted series.

Usage:  lognorm_mu.py <mean> <cv> <cap>
Prints: mu <value>
        realized_cv <value>
        discarded_mass <fraction of draws rejected>
"""
import sys
from math import log, sqrt, exp, erf


def Phi(x):
    return 0.5 * (1.0 + erf(x / sqrt(2.0)))


def truncated_moments(mu, s, c):
    """Mean and second moment of LogNormal(mu, s) conditioned on X <= c."""
    p = Phi((log(c) - mu) / s)
    if p <= 0.0:
        return 0.0, 0.0
    m1 = exp(mu + s * s / 2.0) * Phi((log(c) - mu - s * s) / s) / p
    m2 = exp(2.0 * mu + 2.0 * s * s) * Phi((log(c) - mu - 2.0 * s * s) / s) / p
    return m1, m2


def solve_mu(mean, cv, cap):
    s = sqrt(log(1.0 + cv * cv))
    c = cap * mean                      # cap is absolute, fixed by the TARGET mean
    lo, hi = log(mean) - 10.0 * s, log(mean) + 10.0 * s
    for _ in range(200):              # E[X|X<=c] is increasing in mu
        mid = 0.5 * (lo + hi)
        if truncated_moments(mid, s, c)[0] < mean:
            lo = mid
        else:
            hi = mid
    mu = 0.5 * (lo + hi)
    m1, m2 = truncated_moments(mu, s, c)
    var = max(m2 - m1 * m1, 0.0)
    realized_cv = sqrt(var) / m1 if m1 > 0 else 0.0
    discarded = 1.0 - Phi((log(c) - mu) / s)
    return mu, realized_cv, discarded


if __name__ == "__main__":
    mean, cv, cap = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    mu, rcv, disc = solve_mu(mean, cv, cap)
    print(f"mu {mu:.10f}")
    print(f"realized_cv {rcv:.4f}")
    print(f"discarded_mass {disc:.8f}")
