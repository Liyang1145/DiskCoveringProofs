#!/usr/bin/env python3
"""Search for exact Farkas certificates in beta/row LP sign regions.

The normalized alternative is

  y >= 0, z free, [A Aeq]^T (y,z) = 0, [b beq]^T (y,z) = -1.

A candidate is reported as CERTIFIED only after an exact Fraction recheck of
the equality, sign, and normalization.  Float LP output is only a candidate
generator.
"""
from fractions import Fraction as Q
import argparse
import hashlib
import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import audit_beta_lp_active_vertex as active
import recheck_next512_rows as common

OUT = HERE / "beta-lp-farkas.json"


def alternative(rec, weights, db, mask):
    _, Aeq, beq, Aub, bub, Aeqq, _ = active.build(rec, weights, db, mask)
    # active.build's exact data covers objective/sign rows only.  Add the
    # beta >= 0 and lam >= 0 bounds explicitly, which linprog supplies via
    # `bounds` and therefore does not include in Aub.
    exact_rows = [list(row) + [Q(0)] for row in active.build(
        rec, weights, db, mask)[6]]
    for j in range(106):
        row = [Q(0)] * 107
        row[j] = Q(-1)
        exact_rows.append(row + [Q(0)])
    exact_rows.append(list(Aeqq[0]) + [Q(1)])
    float_cols = np.array([[float(x) for x in row]
                           for row in exact_rows], dtype=float).T
    # Inequality multipliers are nonnegative; the final equality multiplier
    # is free.
    bounds = [(0, None)] * (len(exact_rows) - 1) + [(None, None)]
    lp = linprog(np.zeros(len(exact_rows)),
                 A_eq=float_cols, b_eq=np.zeros(108) + np.array(
                     [0.0] * 107 + [-1.0]),
                 bounds=bounds, method="highs")
    return lp, exact_rows


def verify(y, z, exact_rows):
    if any(v < 0 for v in y):
        return False, "negative inequality multiplier"
    total = [sum(y[i] * exact_rows[i][j] for i in range(len(y))) +
             z * exact_rows[-1][j] for j in range(107)]
    if any(total):
        return False, "nonzero alternative residual"
    rhs = sum(y[i] * exact_rows[i][-1] for i in range(len(y))) + \
        z * exact_rows[-1][-1]
    if rhs != -1:
        return False, "normalization failed"
    return True, "exact-normalized-Farkas"


def rationalize(x, den=10**18):
    return [Q(float(v)).limit_denominator(den) for v in x]


def rank(rows):
    a = [list(row) for row in rows]
    rank_value = 0
    for col in range(len(a[0]) if a else 0):
        pivot = next((i for i in range(rank_value, len(a))
                      if a[i][col]), None)
        if pivot is None:
            continue
        a[rank_value], a[pivot] = a[pivot], a[rank_value]
        pv = a[rank_value][col]
        a[rank_value] = [v / pv for v in a[rank_value]]
        for i in range(rank_value + 1, len(a)):
            if a[i][col]:
                f = a[i][col]
                a[i] = [u - f * v for u, v in zip(a[i], a[rank_value])]
        rank_value += 1
    return rank_value


def solve_square(a, b):
    a = [list(row) + [rhs] for row, rhs in zip(a, b)]
    n = len(a)
    for col in range(n):
        pivot = next((i for i in range(col, n) if a[i][col]), None)
        if pivot is None:
            return None
        a[col], a[pivot] = a[pivot], a[col]
        pv = a[col][col]
        a[col] = [v / pv for v in a[col]]
        for i in range(n):
            if i != col and a[i][col]:
                f = a[i][col]
                a[i] = [u - f * v for u, v in zip(a[i], a[col])]
    return [a[i][-1] for i in range(n)]


def affine_candidates(rows, support, float_vars):
    a = [[rows[i][j] for i in support] + [Q(0)] for j in range(107)]
    a.append([Q(0)] * len(support) + [Q(-1)])
    n = len(support)
    r = 0
    pivots = []
    for col in range(n):
        pivot = next((i for i in range(r, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        pv = a[r][col]
        a[r] = [v / pv for v in a[r]]
        for i in range(len(a)):
            if i != r and a[i][col]:
                f = a[i][col]
                a[i] = [u - f * v for u, v in zip(a[i], a[r])]
        pivots.append(col)
        r += 1
    if any(not any(row[:n]) and row[n] for row in a):
        return []
    free = [c for c in range(n) if c not in set(pivots)]
    particular = [Q(0)] * n
    for i, col in enumerate(pivots):
        particular[col] = a[i][n]
    basis = []
    for f in free:
        h = [Q(0)] * n
        h[f] = Q(1)
        for i, col in enumerate(pivots):
            h[col] = -a[i][f]
        basis.append(h)
    candidates = []
    if not basis:
        candidates.append(particular)
    else:
        # Project the float solution to each one-dimensional null direction.
        for h in basis:
            for i, (value, hv) in enumerate(zip(float_vars, h)):
                if hv:
                    t = (Q(str(float_vars[i])) - particular[i]) / hv
                    candidates.append([p + t * q for p, q in
                                       zip(particular, h)])
    # Also try the rounded free coordinates directly.
    for f in free:
        p = list(particular)
        p[f] = Q(str(float_vars[f])).limit_denominator(10**18)
        for k in range(len(pivots) - 1, -1, -1):
            col = pivots[k]
            p[col] = a[k][n] - sum(a[k][j] * p[j] for j in free)
        candidates.append(p)
    return candidates


def exact_support_certificate(rows, float_vars, tol=1e-10):
    """Reconstruct all multipliers on the float support exactly."""
    if abs(float_vars[-1] + 1.0) <= tol:
        support = [i for i, v in enumerate(float_vars[:-1]) if abs(v) > tol]
        equations = [[rows[i][j] for i in support] for j in range(107)]
        equations.append([rows[i][-1] for i in support])
        target = [rows[-1][j] for j in range(107)] + [rows[-1][-1] - 1]
        selected = []
        for j in range(108):
            if rank([equations[i] for i in selected + [j]]) > len(selected):
                selected.append(j)
        if len(selected) == len(support):
            values = solve_square([equations[j] for j in selected],
                                  [target[j] for j in selected])
            if values is not None:
                y = [Q(0)] * len(rows)
                for i, value in zip(support, values):
                    y[i] = value
                y[-1] = Q(-1)
                if (all(v >= 0 for v in y[:-1]) and
                        all(sum(y[i] * rows[i][j] for i in range(len(y)))
                            == 0 for j in range(107)) and
                        sum(y[i] * rows[i][-1]
                            for i in range(len(y))) == -1):
                    return y, "exact-normalized-Farkas"
    support = [i for i, v in enumerate(float_vars) if abs(v) > tol]
    for values in affine_candidates(rows, support, [float_vars[i]
                                                     for i in support]):
        y = [Q(0)] * len(rows)
        for i, value in zip(support, values):
            y[i] = value
        if any(v < 0 for v in y[:-1]):
            continue
        if any(sum(y[i] * rows[i][j] for i in range(len(y)))
               for j in range(107)):
            continue
        if sum(y[i] * rows[i][-1] for i in range(len(y))) != -1:
            continue
        return y, "exact-normalized-Farkas"
    return None, "no-exact-support-candidate"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", type=int, default=2356)
    ap.add_argument("--masks", default="0")
    ap.add_argument("--out", type=Path, default=OUT)
    args = ap.parse_args()
    doc = json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))
    weights = doc["weights"]
    rec = next(r for r in doc["records"] if r["id"] == args.id)
    db = common.parse_db(common.DBM.read_text(), args.id)
    records = []
    for mask in [int(x) for x in args.masks.split(",") if x]:
        lp, rows = alternative(rec, weights, db, mask)
        item = {"mask": mask, "float_success": bool(lp.success),
                "status": "float-infeasible-of-alternative"}
        if lp.success:
            y, why = exact_support_certificate(rows, lp.x)
            ok = y is not None
            item.update(status=why,
                        nonzero_inequalities=(sum(v != 0 for v in y[:-1])
                                              if ok else None),
                        equality_multiplier=(str(y[-1]) if ok else None))
            if ok:
                item["y"] = [str(v) for v in y]
        records.append(item)
        print(item["mask"], item["status"])
    report = {"scope": "exact normalized Farkas search for beta/row LP regions",
              "proposal_sha256": hashlib.sha256(
                  common.PROPOSAL.read_bytes()).hexdigest().upper(),
              "id": args.id, "records": records}
    args.out.write_text(json.dumps(report, indent=1) + "\n")


if __name__ == "__main__":
    main()
