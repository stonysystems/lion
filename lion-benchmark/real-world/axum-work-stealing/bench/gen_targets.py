#!/usr/bin/env python3
"""Pre-generate the vegeta target list for one CV cell.

Per-request CPU cost n is drawn from a log-normal with a nominal CV, truncated
at CAP*MEAN and RENORMALISED so the truncated mean is exactly MEAN (see
lognorm_mu.py -- without this, truncation cuts offered load by a CV-dependent
amount, 10.9% at CV=8/CAP=100, and the CV sweep would confound variability with
load).

Writing the stream to a file rather than sampling it in the load generator is
deliberate: BOTH runtimes and every repetition replay the identical sequence of
request costs, so the Lion-vs-Tokio difference is a paired comparison rather
than two independent samples. That removes workload sampling noise from the
comparison entirely and is why 3 repetitions suffice here.

Usage:  gen_targets.py <url> <mean> <cv> <cap> <count> <seed> <outfile>
Prints: realized_cv <value>   (truncation lowers CV below nominal; this is the
                               number that should label the plotted series)
        realized_mean <value>
"""
import random
import sys
from math import exp, sqrt, log

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from lognorm_mu import solve_mu  # noqa: E402


def main():
    url, mean, cv, cap, count, seed, out = sys.argv[1:8]
    mean, cv, cap = float(mean), float(cv), float(cap)
    count, seed = int(count), int(seed)

    mu, analytic_cv, _ = solve_mu(mean, cv, cap)
    sigma = sqrt(log(1.0 + cv * cv))
    n_max = int(round(cap * mean))

    rng = random.Random(seed)
    total = 0
    sq = 0
    with open(out, "w") as fh:
        for _ in range(count):
            while True:                       # reject above the cap and resample
                n = int(round(exp(mu + sigma * rng.gauss(0.0, 1.0))))
                if n < 1:
                    n = 1
                if n <= n_max:
                    break
            total += n
            sq += n * n
            fh.write(f"GET {url}?n={n}\n")

    m = total / count
    var = max(sq / count - m * m, 0.0)
    print(f"realized_cv {sqrt(var) / m:.4f}")
    print(f"realized_mean {m:.1f}")
    print(f"analytic_cv {analytic_cv:.4f}")


if __name__ == "__main__":
    main()
