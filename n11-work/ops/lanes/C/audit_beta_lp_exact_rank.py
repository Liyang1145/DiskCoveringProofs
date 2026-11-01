#!/usr/bin/env python3
"""Diagnose the exact rank/consistency of the 2356 corrected LP active set.

The earlier reconstruction accepted 107 float-linearly-independent rows and
then failed because those rows are dependent over Q.  This audit does not
pretend modular or float rank is exact: it performs Fraction Gauss-Jordan on
the selected rows and records the exact rank, free columns, and augmented-row
inconsistency.  Scope is an active-set diagnostic, not an infeasibility proof
or kernel credit.
"""
from fractions import Fraction as Q
import argparse, hashlib, json, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import audit_beta_lp_active_vertex as active
import recheck_next512_rows as common
import search_beta_row_lp as coefficients

OUT = HERE / "beta-lp-exact-rank.json"


def rref(rows):
    a = [list(row) + [rhs] for row, rhs in rows]
    ncols = 107
    pivots = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(a)) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        pv = a[r][c]
        a[r] = [v / pv for v in a[r]]
        for i in range(len(a)):
            if i == r or not a[i][c]:
                continue
            f = a[i][c]
            a[i] = [x - f * y for x, y in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
    inconsistent = any(not any(row[:ncols]) and row[ncols] for row in a)
    free = [c for c in range(ncols) if c not in set(pivots)]
    solution = None
    if not inconsistent and not free:
        solution = [Q(0)] * ncols
        for i, c in enumerate(pivots):
            solution[c] = a[i][ncols]
    return r, pivots, free, inconsistent, solution


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", type=int, default=2356)
    ap.add_argument("--mask", type=int, default=71)
    ap.add_argument("--tol", type=float, action="append")
    args = ap.parse_args()
    tols = args.tol or [2e-7, 1e-8, 1e-9, 1e-10, 1e-11, 1e-12]
    start = time.monotonic()
    doc = json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))
    weights = doc["weights"]
    rec = next(r for r in doc["records"] if r["id"] == args.id)
    db = common.parse_db(common.DBM.read_text(), args.id)
    lp, Aeq, beq, Aub, bub, Aeqq, Aubq = active.solve_region(
        rec, weights, db, args.mask)
    if not lp.success:
        raise RuntimeError(lp.message)
    attempts = []
    for tol in tols:
        selected, _ = active.active_system(
            lp, Aeq, beq, Aub, bub, Aeqq, Aubq, tol=tol)
        t0 = time.monotonic()
        rank, pivots, free, inconsistent, solution = rref(selected)
        attempt = {
            "tol": tol,
            "selected_rows": len(selected),
            "exact_rank": rank,
            "free_columns": free,
            "augmented_inconsistent": inconsistent,
            "elapsed_seconds": round(time.monotonic() - t0, 3),
        }
        if solution is not None:
            beta, lam, rmin = solution[:16], solution[16:106], solution[-1]
            ex = coefficients.exact_eval(rec, weights, beta, lam, rmin, db)
            attempt["exact"] = ex
            attempt["status"] = "PASS" if ex["pass"] else "exact-negative"
        else:
            attempt["status"] = ("inconsistent-active-set" if inconsistent
                                 else "underdetermined-active-set")
        attempts.append(attempt)
        print(json.dumps({k: v for k, v in attempt.items() if k != "exact"},
                         indent=1))
    report = {
        "scope": ("exact Fraction rank/consistency audit of one corrected "
                  "beta/row LP active set; no infeasibility proof and no "
                  "kernel credit"),
        "proposal_sha256": hashlib.sha256(
            common.PROPOSAL.read_bytes()).hexdigest().upper(),
        "id": args.id,
        "mask": args.mask,
        "float_fun": str(lp.fun),
        "attempts": attempts,
        "elapsed_seconds": round(time.monotonic() - start, 3),
    }
    OUT.write_text(json.dumps(report, indent=1) + "\n")
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
