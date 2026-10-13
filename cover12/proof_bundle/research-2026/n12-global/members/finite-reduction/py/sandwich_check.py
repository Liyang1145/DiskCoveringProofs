"""sandwich_check.py -- two-sided sound reading of R(C) on the awkward instances.

For each instance we report
  lower  = R_cand                       (attained on D, hence <= R(C) exactly)
  upper  = max over a lattice of f  +  h*sqrt(2)/2 + 1e-12
           (valid because f_C is 1-Lipschitz and the lattice of spacing h covers D
            with radius h*sqrt(2)/2; so R(C) <= upper up to float rounding)
  violation_grid / violation_random     (max f found on lattice / on 2e6 random
           points in D, minus R_cand).  A sustained POSITIVE violation is a hard
           counterexample to the candidate-completeness claim; it does not rely on
           any optimizer.
Usage: py -3 -B sandwich_check.py [outfile]
"""
from __future__ import annotations

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from candlib import sandwich                                      # noqa: E402
from run_battery import (battery, load_c182, regular,             # noqa: E402
                         circumcenter_on_bd_triple)
import numpy as np                                                # noqa: E402


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "evidence",
        "sandwich-check.json")
    cases = dict(battery())
    picks = ["all-zero-n12", "all-zero-n1", "single-origin", "single-0.5",
             "single-rational", "pair-anticlockwise", "pair-origin-0.9",
             "all-same-0.6-0.8", "ring+origin-m3-rho0.9", "ring+origin-m12-rho1.0",
             "ring-m12-rho1.0", "dup6x2+origin", "collinear-x12", "collinear-y+origin",
             "collinear-3+random", "cc-on-bd-triple", "cc-on-bd-triple+origin",
             "near-tangent-bis-1e-09", "tight-pair-1.0-0.999999",
             "ess-a-only-origin", "ess-b-single-center", "ess-c-two-centers",
             "ess-d-regular12-on-circle", "ess-d-regular6-on-circle",
             "ess-d-square-on-circle", "rand-disk-n12-3", "rand-circle-n12-0",
             "c182-n12-diagnostic"]
    rows = []
    for name in picks:
        if name not in cases:
            print(f"[skip] {name}")
            continue
        C = np.asarray(cases[name], float)
        r = sandwich(C, n_grid=2001, chunk=2_000_000)
        arg = r["R_cand_arg"]
        rows.append(dict(name=name, n=len(C), R_cand=r["R_cand"],
                         grid_max=r["grid_max"], upper=r["upper"], width=r["width"],
                         violation_grid=r["violation_grid"],
                         violation_random=r["violation_random"],
                         argmax_kind=arg["kind"], argmax_idx=list(arg["idx"]),
                         argmax_pos=[float(arg["pos"][0]), float(arg["pos"][1])]))
        print(f"{name:28s} n={len(C):2d} R_cand={r['R_cand']:.12f} "
              f"upper={r['upper']:.12f} width={r['width']:.2e} "
              f"vio_grid={r['violation_grid']:+.2e} vio_rand={r['violation_random']:+.2e} "
              f"kind={arg['kind']}")
    worst_v = max(r["violation_grid"] for r in rows) if rows else float("nan")
    worst_r = max(r["violation_random"] for r in rows) if rows else float("nan")
    summary = dict(n=len(rows), worst_violation_grid=worst_v,
                   worst_violation_random=worst_r,
                   max_width=max(r["width"] for r in rows) if rows else None,
                   counters=max(1, 2_000_000) * len(rows))
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(dict(summary=summary, rows=rows), fh, indent=1)
    print("\n== summary ==")
    print(json.dumps(summary, indent=1))
    print("log ->", out)


if __name__ == "__main__":
    main()
