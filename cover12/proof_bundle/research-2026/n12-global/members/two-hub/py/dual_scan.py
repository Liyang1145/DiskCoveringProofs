"""dual_scan.py -- scan the hub domain with the k=10 dual LP.

Hub domain (necessary structure of a k=10 cover at radius r<=U, relaxed to
fixed radius U; see two-hub/REDUCTION.md):

  t1,t2 in [0,1-U),  delta in [0,pi],
  core covered:  (t1 + a <= U) or (t2 + a <= U) or (beta(t1)+beta(t2) >= 2pi-delta),
  a = 1-2U, beta(t) = pi if t+a<=U, 0 if |t-a|>=U, else acos((a^2+t^2-U^2)/(2at)).

For each sampled config we solve the dual LP of dual_lp.py and record m*.
Criterion: m* < 0.1 (then ten rings cannot cover the required sets).
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dual_lp as D  # noqa: E402

U = D.U
OUT = HERE.parent / "evidence"


def beta(t, a):
    if t <= 0:
        return math.pi
    if t + a <= U:
        return math.pi
    if abs(t - a) >= U:
        return 0.0
    return math.acos(max(-1.0, min(1.0, (t * t + a * a - U * U) / (2 * t * a))))


def in_domain(t1, t2, delta):
    a = 1 - 2 * U
    if t1 + a <= U or t2 + a <= U:
        return True
    return beta(t1, a) + beta(t2, a) >= 2 * math.pi - delta - 1e-12


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    n_rho = int(sys.argv[2]) if len(sys.argv) > 2 else 26
    n_phi = int(sys.argv[3]) if len(sys.argv) > 3 else 96
    tmax = 1.0 - U - 1e-6
    ts = [0.0, 0.02, 0.05, 0.083, 0.12, 0.16, 0.2, 0.2307, 0.27, 0.32, 0.38,
          0.45, 0.52, 0.58, 0.62, tmax]
    a = 1 - 2 * U
    rows = []
    t0 = time.time()
    for t1 in ts:
        for t2 in ts:
            if t2 < t1:
                continue
            b1, b2 = beta(t1, a), beta(t2, a)
            dmin = max(0.0, 2 * math.pi - b1 - b2)
            for delta in sorted(set([round(dmin, 6), round((dmin + math.pi) / 2, 6),
                                     round(math.pi, 6)])):
                if delta > math.pi + 1e-12:
                    continue
                if not in_domain(t1, t2, delta):
                    continue
                r = D.solve(t1, t2, delta, K=K, n_rho=n_rho, n_phi=n_phi)
                r.update(t1=t1, t2=t2, delta=delta, beta1=b1, beta2=b2, dmin=dmin)
                rows.append(r)
    ok = [r for r in rows if r["pass_criterion"]]
    bad = [r for r in rows if not r["pass_criterion"]]
    print("configs tested: %d   pass: %d   fail: %d   (%.1fs)"
          % (len(rows), len(ok), len(bad), time.time() - t0))
    if rows:
        ms = [r["m_star"] for r in rows if r["m_star"] is not None]
        print("m*: min=%.5f  max=%.5f  mean=%.5f   (threshold 0.1)"
              % (min(ms), max(ms), sum(ms) / len(ms)))
        worst = sorted(rows, key=lambda r: -(r["m_star"] or 0))[:8]
        print("worst configs (largest m*):")
        for r in worst:
            print("   t1=%.4f t2=%.4f delta=%.4f  m*=%.5f  d=%.4f b=%.4f"
                  % (r["t1"], r["t2"], r["delta"], r["m_star"], r["d"], r["b"]))
        if bad:
            print("FAILING configs:")
            for r in bad[:10]:
                print("   t1=%.4f t2=%.4f delta=%.4f  m*=%s  %s"
                      % (r["t1"], r["t2"], r["delta"], r["m_star"], r["status"]))
    json.dump(rows, open(OUT / ("dual_scan_K%d.json" % K), "w"), indent=1)


if __name__ == "__main__":
    main()
