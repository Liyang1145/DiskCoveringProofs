#!/usr/bin/env python3
"""Reconstruct the best corrected beta/row LP vertex over exact rationals.

The preceding sweep rounded every coordinate independently at 12-18 digits.
At the nearly tight 2356 branch that destroys feasibility.  Here the float LP
is used only to identify a sign region and its active equalities; the active
linear system is then solved at 100 decimal digits, rationalized, and the
result is checked with Fraction.  This remains a search diagnostic, not an
infeasibility proof or kernel credit.
"""
from fractions import Fraction as Q
import argparse, hashlib, json, sys, time
from decimal import Decimal, getcontext
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common
import search_beta_row_lp as coefficients

IDS = (1409, 2337, 2341, 2356, 2360, 2368, 2370)
OUT = HERE / "beta-lp-active-vertex.json"
C2 = Q(2 * Q(1150475603510479590494077, 2951479051793528258560000))


def vec(fracs):
    return np.array([float(x) for x in fracs], dtype=float)


def build(rec, weights, db, mask):
    clc, f0c, gc = coefficients.coeffs(rec, weights)
    signs = [1 if mask >> q & 1 else -1 for q in range(9)]
    cpos = bool(mask >> 9 & 1)
    cscale = C2 if cpos else common.LQ
    obj = np.zeros(107)
    for f in range(16):
        obj[f] = -(f0c[f] + cscale * clc[f])
    for k, (i, j) in enumerate(common.PAIRS):
        obj[16 + k] = db[i][j] / 4096
    obj[-1] = -1
    Aeqn, beqn, Aubn, bubn, Aeqq, Aubq = [], [], [], [], [], []
    eq = np.zeros(107); eq[:16] = 1
    Aeqn.append(eq); beqn.append(1.0)
    Aeqq.append([Q(1)] * 16 + [Q(0)] * 91)
    for q in range(9):
        row = np.zeros(107); row[-1] = 1
        exact = [Q(0)] * 16 + [Q(0)] * 90 + [Q(1)]
        scale = common.Dq if signs[q] > 0 else common.DQ
        for k in range(90):
            value = -common.row_a(*common.PAIRS[k], q)
            row[16 + k] = value
            exact[16 + k] = Q(value)
        for f in range(16):
            value = -scale * gc[q][f]
            row[f] = value
            exact[f] = Q(value)
        Aubn.append(row); bubn.append(0.0); Aubq.append(exact)
    row = np.zeros(107); exact = [Q(0)] * 107
    for f in range(16):
        value = -clc[f] if cpos else clc[f]
        row[f] = value; exact[f] = Q(value)
    Aubn.append(row); bubn.append(0.0); Aubq.append(exact)
    for q in range(9):
        row = np.zeros(107); exact = [Q(0)] * 107
        for f in range(16):
            value = -signs[q] * gc[q][f]
            row[f] = value; exact[f] = Q(value)
        Aubn.append(row); bubn.append(0.0); Aubq.append(exact)
    return obj, np.array(Aeqn), np.array(beqn), np.array(Aubn), np.array(bubn), Aeqq, Aubq


def solve_region(rec, weights, db, mask):
    obj, Aeq, beq, Aub, bub, Aeqq, Aubq = build(rec, weights, db, mask)
    lp = linprog(obj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                 bounds=[(0, None)] * 106 + [(None, None)], method="highs")
    return lp, Aeq, beq, Aub, bub, Aeqq, Aubq


def active_system(lp, Aeq, beq, Aub, bub, Aeqq, Aubq, tol=2e-7):
    rows = []
    for i in range(len(Aeq)):
        rows.append((Aeq[i].copy(), float(beq[i]), list(Aeqq[i]), Q(beq[i])))
    for i in range(len(Aub)):
        if abs(float(Aub[i] @ lp.x) - float(bub[i])) <= tol:
            rows.append((Aub[i].copy(), float(bub[i]), list(Aubq[i]), Q(bub[i])))
    for j in range(106):
        if abs(lp.x[j]) <= tol:
            row = np.zeros(107); row[j] = 1.0
            exact = [Q(0)] * 107; exact[j] = Q(1)
            rows.append((row, 0.0, exact, Q(0)))
    selected, M = [], np.empty((0, 107))
    for row, rhs, exact, exact_rhs in rows:
        if np.linalg.matrix_rank(np.vstack([M, row]), tol=1e-8) > len(M):
            selected.append((exact, exact_rhs)); M = np.vstack([M, row])
    return selected, M


def high_precision_solve(selected):
    getcontext().prec = 240
    n = len(selected)
    if n != 107:
        raise ValueError(f"active rank {n}, expected 107")
    A = [[Decimal(num) / Decimal(den) for num, den in
          ((q.numerator, q.denominator) for q in row)] for row, _ in selected]
    b = [Decimal(q.numerator) / Decimal(q.denominator) for _, q in selected]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(A[r][col]))
        if A[pivot][col] == 0:
            raise ValueError(f"singular exact active system at column {col}")
        if pivot != col:
            A[col], A[pivot] = A[pivot], A[col]
            b[col], b[pivot] = b[pivot], b[col]
        pv = A[col][col]
        for j in range(col, n):
            A[col][j] /= pv
        b[col] /= pv
        for r in range(n):
            if r == col:
                continue
            factor = A[r][col]
            if factor == 0:
                continue
            for j in range(col, n):
                A[r][j] -= factor * A[col][j]
            b[r] -= factor * b[col]
    return b


def rationalize(x):
    return [Q(v).limit_denominator(10**220) for v in x]


def exact_active_residual(selected, beta, lam, rmin):
    x = beta + lam + [rmin]
    worst = Q(0)
    for row, rhs in selected:
        lhs = sum(coef * val for coef, val in zip(row, x))
        worst = max(worst, abs(lhs - rhs))
    return worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", type=int, default=2356)
    ap.add_argument("--time-budget", type=float, default=80)
    args = ap.parse_args()
    start = time.monotonic()
    doc = json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))
    weights = doc["weights"]
    rec = next(r for r in doc["records"] if r["id"] == args.id)
    db = common.parse_db(common.DBM.read_text(), args.id)
    best = None
    for mask in range(512):
        if time.monotonic() - start > args.time_budget:
            raise TimeoutError(f"sign sweep stopped at mask {mask}")
        solved = solve_region(rec, weights, db, mask)
        lp = solved[0]
        if lp.success and (best is None or lp.fun < best[0].fun):
            best = (lp, mask, solved)
    lp, mask, solved = best
    _, Aeq, beq, Aub, bub, Aeqq, Aubq = solved
    selected, M = active_system(lp, Aeq, beq, Aub, bub, Aeqq, Aubq)
    status = {"id": args.id, "best_mask": mask, "best_float_fun": str(lp.fun),
              "active_rank": len(selected)}
    try:
        x = rationalize(high_precision_solve(selected))
        beta, lam, rmin = x[:16], x[16:106], x[-1]
        status["active_residual"] = str(exact_active_residual(selected, beta, lam, rmin))
        ex = coefficients.exact_eval(rec, weights, beta, lam, rmin, db)
        status.update(beta=[str(v) for v in beta],
                      lam_nonzero=[[list(common.PAIRS[k]), str(lam[k])]
                                   for k in range(90) if lam[k]],
                      exact=ex, status="PASS" if ex["pass"] else "exact-negative")
    except Exception as exc:
        status["status"] = "reconstruction-failed"
        status["error"] = f"{type(exc).__name__}: {exc}"
    report = {
        "scope": ("exact rational active-set reconstruction of one corrected "
                  "beta/row sign-region LP vertex; no infeasibility proof and "
                  "no kernel credit"),
        "proposal_sha256": hashlib.sha256(common.PROPOSAL.read_bytes()).hexdigest().upper(),
        "result": status,
    }
    OUT.write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps({k: status.get(k) for k in
                      ("id", "best_mask", "active_rank", "active_residual",
                       "status", "error")}, indent=1))
    if "exact" in status:
        print("gap", status["exact"]["gap"][:80], "reduced", status["exact"]["reduced"])


if __name__ == "__main__":
    main()
