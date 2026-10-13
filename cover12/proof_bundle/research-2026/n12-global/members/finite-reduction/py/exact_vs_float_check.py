"""exact_vs_float_check.py -- implementation audit of the exact quantifier-free
checker against the geometric candidate predicate (two code paths, different formulas).

exact side : py/exact_checker.py  (Fraction; sign-branch elimination; x = v/(2Δ))
float side : py/candlib.py        (candidate *points*; circumcentre by numpy solve)

For random rational configurations and rational radii we compare
    criterion(C, r)   vs   (R_cand(C) <= r)
skipping the float-borderline band |r - R_cand| <= 1e-9*max(1,R_cand).
Random configurations are drawn with small rational denominators and include
duplicates, collinear triples, boundary points and the origin, to exercise the guards.

Usage: py -3 -B exact_vs_float_check.py [outfile] [n_random]
"""
from __future__ import annotations

import itertools
import json
import os
import random
import sys
from fractions import Fraction as F

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from candlib import R_cand                                    # noqa: E402
from exact_checker import criterion                            # noqa: E402


def rand_center(rng, denom=10):
    return (F(rng.randint(-denom, denom), denom), F(rng.randint(-denom, denom), denom))


def make_cfg(rng, kind, n):
    D = []
    for _ in range(n):
        if kind == "disk":
            while True:
                c = rand_center(rng, 10)
                if c[0] * c[0] + c[1] * c[1] <= 1:
                    break
            D.append(c)
        elif kind == "circle":
            D.append((F(rng.choice([-10, -9, -8, -6, 0, 6, 8, 9, 10]), 10),
                      F(rng.choice([-6, -8, -10, 0, 6, 8, 10]), 10)))
        elif kind == "dupin":                    # duplicates + origin
            base = [rand_center(rng, 4), rand_center(rng, 4), (F(0), F(0))]
            D.append(base[rng.randrange(3)])
        elif kind == "collinear":                # collinear family + extras
            D.append((F(rng.randint(-10, 10), 10), F(0)))
        elif kind == "grid":                     # rational lattice in the disk
            D.append((F(rng.randint(-4, 4), 4), F(rng.randint(-4, 4), 4)))
    # keep only centres inside the closed unit disk (side condition of the theorem)
    return [c for c in D if c[0] * c[0] + c[1] * c[1] <= 1]


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "evidence",
        "exact-vs-float.json")
    n_random = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    rng = random.Random(20260926)
    kinds = ["disk", "circle", "dupin", "collinear", "grid"]
    rows, mism, skipped = [], [], 0
    for t in range(n_random):
        kind = kinds[t % len(kinds)]
        n = 1 + (t % 6)
        C = make_cfg(rng, kind, n)
        if not C:
            continue
        Cf = np.array([[float(x), float(y)] for x, y in C])
        if len({(x, y) for x, y in C}) == 0:
            continue
        Rc, _ = R_cand(Cf)
        for d in (0.001, 0.01, 0.2):
            for sgn in (1, -1):
                r = Rc * (1 + sgn * d)
                if r <= 0:
                    continue
                rf = F(round(r * 10 ** 12), 10 ** 12)
                if abs(float(rf) - Rc) <= 1e-9 * max(1.0, Rc):
                    skipped += 1
                    continue
                ok_exact, parts, diag = criterion(C, rf)
                ok_float = (Rc <= float(rf))
                rec = dict(t=t, kind=kind, n=len(C), r=str(rf), R_cand=Rc,
                           exact=ok_exact, geom=ok_float, agree=(ok_exact == ok_float),
                           parts=parts)
                rows.append(rec)
                if ok_exact != ok_float:
                    mism.append(rec)
    summary = dict(n_configs=n_random, n_decisive=len(rows), n_mismatch=len(mism),
                   n_borderline_skipped=skipped,
                   mismatches=[{k: m[k] for k in ("t", "kind", "n", "r", "R_cand",
                                                  "exact", "geom", "parts")}
                               for m in mism[:5]])
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(dict(summary=summary, rows=rows), fh, indent=1)
    print(json.dumps({k: v for k, v in summary.items() if k != "mismatches"}, indent=1))
    for m in summary["mismatches"]:
        print("  MISMATCH:", m)
    print("log ->", out)


if __name__ == "__main__":
    main()
