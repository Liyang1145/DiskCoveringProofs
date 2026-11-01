#!/usr/bin/env python3
"""Exact threshold-Farkas audit for beta/row LP sign regions.

For each sign region, append the objective threshold ``lower <= T2`` to the
primal region.  The normalized alternative

  y >= 0, z free, [A Aeq]^T (y,z) = 0, [b beq]^T (y,z) = -1

is reconstructed over Q only after the float LP proposes a support.  A
reported certificate proves that this region contains no point with
``lower > T2``; it is not by itself a global statement for the id.
"""
from fractions import Fraction as Q
import argparse
import hashlib
import json
import sys
from pathlib import Path

import numpy as np
try:
    import flint
except ImportError:
    flint = None
from scipy.optimize import linprog
from scipy.linalg import qr

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import audit_beta_lp_active_vertex as active
import audit_beta_lp_farkas as farkas
import recheck_next512_rows as common
import search_beta_row_lp as coefficients

OUT = HERE / "beta-lp-threshold-farkas.json"
C2 = Q(2 * Q(1150475603510479590494077, 2951479051793528258560000))


def threshold_alternative(rec, weights, db, mask):
    clc, f0c, _ = coefficients.coeffs(rec, weights)
    signs = [1 if mask >> q & 1 else -1 for q in range(9)]
    cscale = C2 if mask >> 9 & 1 else common.LQ
    _, _, _, _, _, _, Aubq = active.build(rec, weights, db, mask)
    exact_rows = [list(row) + [Q(0)] for row in Aubq]
    objective = [Q(0)] * 107
    for f in range(16):
        objective[f] = -(f0c[f] + cscale * clc[f])
    for k, (i, j) in enumerate(common.PAIRS):
        objective[16 + k] = Q(db[i][j], 4096)
    objective[-1] = Q(-1)
    # lower = -objective^T x; this row excludes lower > T2.
    exact_rows.append(objective + [-common.T2])
    for j in range(106):
        row = [Q(0)] * 108
        row[j] = Q(-1)
        exact_rows.append(row)
    equality = [Q(1)] * 16 + [Q(0)] * 91
    exact_rows.append(equality + [Q(1)])
    float_cols = np.array([[float(x) for x in row]
                           for row in exact_rows], dtype=float).T
    bounds = [(0, None)] * (len(exact_rows) - 1) + [(None, None)]
    lp = linprog(np.zeros(len(exact_rows)), A_eq=float_cols,
                 b_eq=np.zeros(108) + np.array([0.0] * 107 + [-1.0]),
                 bounds=bounds, method="highs")
    return lp, exact_rows


def exact_l1_certificate(rows, tol=1e-10):
    """Find a vertex dual with an auxiliary L1 objective, then solve over Q."""
    nr = len(rows)
    equality = rows[-1]
    columns = [[row[j] for j in range(108)] for row in rows[:-1]]
    columns.append([equality[j] for j in range(107)] + [Q(1)])
    columns.append([-equality[j] for j in range(107)] + [Q(-1)])
    lhs = np.array([[float(x) for x in column] for column in columns],
                   dtype=float).T
    rhs = np.zeros(108)
    rhs[-1] = -1
    lp = linprog(np.ones(nr + 1), A_eq=lhs, b_eq=rhs,
                 bounds=[(0, None)] * (nr + 1), method="highs")
    if not lp.success:
        return None, "float-infeasible-of-l1-alternative"
    support = [i for i, value in enumerate(lp.x) if abs(value) > tol]
    _, _, pivots = qr(lhs[:, support].T, mode="economic", pivoting=True)
    selected = sorted(int(equation) for equation in pivots[:len(support)])
    if len(selected) != len(support):
        return None, "underdetermined-l1-support"
    values = None
    if flint is not None:
        try:
            system = flint.fmpq_mat(
                len(support), len(support),
                [flint.fmpq(columns[j][i].numerator,
                            columns[j][i].denominator)
                 for i in selected for j in support])
            target = flint.fmpq_mat(
                len(support), 1,
                [flint.fmpq(-1 if i == 107 else 0) for i in selected])
            solved = system.solve(target)
            values = [Q(int(value.p), int(value.q))
                      for value in solved.entries()]
        except (ImportError, ValueError, ZeroDivisionError):
            values = None
    if values is None:
        values = farkas.solve_square(
            [[columns[j][i] for j in support] for i in selected],
            [Q(-1) if i == 107 else Q(0) for i in selected])
    if values is None:
        return None, "singular-l1-support"
    u = [Q(0)] * (nr + 1)
    for i, value in zip(support, values):
        u[i] = value
    y = u[:nr - 1]
    y.append(u[nr - 1] - u[nr])
    if (not all(value >= 0 for value in y[:-1]) or
            any(sum(y[i] * rows[i][j] for i in range(nr))
                for j in range(107)) or
            sum(y[i] * rows[i][-1] for i in range(nr)) != -1):
        return None, "l1-candidate-failed-exact-recheck"
    return y, "exact-l1-normalized-Farkas"


def make_report(args, records):
    counts = {}
    for item in records:
        counts[item["status"]] = counts.get(item["status"], 0) + 1
    return {
        "scope": ("exact threshold-Farkas audit for one residual id's sign "
                  "regions; certificates are region-local and are not kernel "
                  "credit or a global arbitrary-centre proof"),
        "proposal_sha256": hashlib.sha256(
            common.PROPOSAL.read_bytes()).hexdigest().upper(),
        "id": args.id,
        "threshold_T2": str(common.T2),
        "status_counts": counts,
        "records": records,
    }


def write_report(path, report):
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(report, indent=1) + "\n")
    temporary.replace(path)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", type=int, default=2356)
    ap.add_argument("--masks", default="")
    ap.add_argument("--start-mask", type=int, default=0)
    ap.add_argument("--stop-mask", type=int, default=512)
    ap.add_argument("--out", type=Path, default=OUT)
    ap.add_argument("--resume", action="store_true",
                    help="preserve already checked masks in --out")
    ap.add_argument("--checkpoint-every", type=int, default=8,
                    help="atomically save after this many newly checked masks")
    args = ap.parse_args()
    if args.checkpoint_every < 1:
        raise SystemExit("--checkpoint-every must be positive")
    doc = json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))
    weights = doc["weights"]
    rec = next(r for r in doc["records"] if r["id"] == args.id)
    db = common.parse_db(common.DBM.read_text(), args.id)
    masks = ([int(x) for x in args.masks.split(",") if x]
             if args.masks else range(args.start_mask, min(args.stop_mask, 512)))
    by_mask = {}
    if args.resume and args.out.exists():
        previous = json.loads(args.out.read_text())
        expected = {
            "id": args.id,
            "proposal_sha256": hashlib.sha256(
                common.PROPOSAL.read_bytes()).hexdigest().upper(),
            "threshold_T2": str(common.T2),
        }
        for key, value in expected.items():
            if previous.get(key) != value:
                raise SystemExit(f"cannot resume: {key} mismatch")
        by_mask = {item["mask"]: item for item in previous["records"]}
    processed = 0
    for mask in masks:
        if mask in by_mask:
            print(mask, "already-checked", flush=True)
            continue
        if mask < 0 or mask >= 512:
            raise SystemExit(f"mask out of range: {mask}")
        lp, rows = threshold_alternative(rec, weights, db, mask)
        item = {"mask": mask, "float_success": bool(lp.success),
                "status": "float-infeasible-of-alternative"}
        if lp.success:
            y, why = exact_l1_certificate(rows)
            if y is None:
                y, why = farkas.exact_support_certificate(rows, lp.x)
            ok = y is not None
            item.update(status=why,
                        nonzero_inequalities=(sum(v != 0 for v in y[:-1])
                                              if ok else None),
                        equality_multiplier=(str(y[-1]) if ok else None))
            if ok:
                item["y"] = [str(v) for v in y]
        by_mask[mask] = item
        processed += 1
        print(item["mask"], item["status"], flush=True)
        if processed % args.checkpoint_every == 0:
            write_report(args.out, make_report(
                args, [by_mask[key] for key in sorted(by_mask)]))
    records = [by_mask[key] for key in sorted(by_mask)]
    report = make_report(args, records)
    write_report(args.out, report)
    print(json.dumps({k: report[k] for k in
                      ("id", "threshold_T2", "status_counts")}, indent=1))


if __name__ == "__main__":
    main()
