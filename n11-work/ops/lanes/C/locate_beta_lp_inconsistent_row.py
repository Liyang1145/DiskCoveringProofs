#!/usr/bin/env python3
"""Locate and repair the inconsistent exact active set at beta LP mask 71.

The float-selected 2356/mask-71 rows have exact rank 106 but inconsistent
augmented rank.  This script tracks the exact left-null certificate, identifies
which selected row must be removed, pins the free coordinate (using the float
point only as a selector of a point on the exact affine face), then checks all
original LP inequalities with Fraction arithmetic.
"""
from fractions import Fraction as Q
import argparse, hashlib, json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import audit_beta_lp_active_vertex as active
import audit_beta_lp_exact_rank as rankaudit
import recheck_next512_rows as common
import search_beta_row_lp as coefficients

OUT = HERE / "beta-lp-inconsistent-row.json"


def rref_tracked(selected):
    ncols = 107
    a = [list(row) + [rhs] for row, rhs in selected]
    tracks = [[Q(int(i == j)) for j in range(len(selected))]
              for i in range(len(selected))]
    pivots, r = [], 0
    for c in range(ncols):
        p = next((i for i in range(r, len(a)) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        tracks[r], tracks[p] = tracks[p], tracks[r]
        pv = a[r][c]
        a[r] = [v / pv for v in a[r]]
        tracks[r] = [v / pv for v in tracks[r]]
        for i in range(len(a)):
            if i == r or not a[i][c]:
                continue
            f = a[i][c]
            a[i] = [x - f * y for x, y in zip(a[i], a[r])]
            tracks[i] = [x - f * y for x, y in zip(tracks[i], tracks[r])]
        pivots.append(c)
        r += 1
    bad = next((i for i in range(len(a))
                if not any(a[i][:ncols]) and a[i][ncols]), None)
    support = ([] if bad is None else
               [j for j, v in enumerate(tracks[bad]) if v])
    return r, bad, support, tracks[bad] if bad is not None else []


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", type=int, default=2356)
    ap.add_argument("--mask", type=int, default=71)
    ap.add_argument("--tol", type=float, default=2e-7)
    args = ap.parse_args()
    doc = json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))
    weights, rec = doc["weights"], next(
        r for r in doc["records"] if r["id"] == args.id)
    db = common.parse_db(common.DBM.read_text(), args.id)
    lp, Aeq, beq, Aub, bub, Aeqq, Aubq = active.solve_region(
        rec, weights, db, args.mask)
    selected, _ = active.active_system(
        lp, Aeq, beq, Aub, bub, Aeqq, Aubq, tol=args.tol)
    exact_rank, bad_row, support, certificate = rref_tracked(selected)

    repairs = []
    for j in support:
        rows = selected[:j] + selected[j + 1:]
        rank, _, free, inconsistent, _ = rankaudit.rref(rows)
        repairs.append({"removed_row": j, "rank_without_row": rank,
                        "free_columns": free,
                        "augmented_inconsistent": inconsistent,
                        "consistent": not inconsistent})
    consistent = [r for r in repairs if r["consistent"]]
    result = {
        "scope": ("exact rational location/repair of one spurious float-active "
                  "LP row; no infeasibility proof and no kernel credit"),
        "id": args.id, "mask": args.mask, "tol": args.tol,
        "selected_rows": len(selected), "exact_rank": exact_rank,
        "inconsistent_reduced_row": bad_row,
        "certificate_support": support,
        "certificate": [str(v) for v in certificate],
        "removal_trials": repairs,
        "status": ("exact-consistent-no-repair-needed" if bad_row is None else ("repaired" if consistent else "no-single-row-repair")),
    }
    if len(consistent) == 1:
        repair = consistent[0]
        j = repair["removed_row"]
        rows = selected[:j] + selected[j + 1:]
        # Any value on the exact affine face is valid; the float optimum only
        # chooses a representative.  Pinning all free coordinates gives a
        # square exact system.
        for c in repair["free_columns"]:
            row = [Q(0)] * 107
            row[c] = Q(1)
            rows.append((row, Q(str(float(lp.x[c])))))
        rank, _, free, inconsistent, solution = rankaudit.rref(rows)
        repair.update(pinned_exact_rank=rank, pinned_free_columns=free,
                      pinned_inconsistent=inconsistent)
        if solution is not None:
            x = solution
            beta, lam, rmin = x[:16], x[16:106], x[-1]
            ub_violations = []
            for i, (row, rhs) in enumerate(zip(Aubq, bub)):
                lhs = sum(c * v for c, v in zip(row, x))
                if lhs > rhs:
                    ub_violations.append([i, str(lhs - rhs)])
            eq_residuals = []
            for row, rhs in zip(Aeqq, beq):
                lhs = sum(c * v for c, v in zip(row, x))
                if lhs != rhs:
                    eq_residuals.append(str(lhs - rhs))
            ex = coefficients.exact_eval(rec, weights, beta, lam, rmin, db)
            signs = [1 if args.mask >> q & 1 else -1 for q in range(9)]
            expected = ([(Q(q_)) for q_ in ex["g"]] and
                        all((signs[q] > 0) == (Q(ex["g"][q]) >= 0)
                            for q in range(9)))
            repair.update(beta=[str(v) for v in beta],
                          lam_nonzero=[[list(common.PAIRS[k]), str(lam[k])]
                                       for k in range(90) if lam[k]],
                          solution=ex, inequality_violations=ub_violations,
                          equality_residuals=eq_residuals,
                          sign_region_matches=expected,
                          exact_reduced_feasible=(ex["reduced"] and
                                                  not ub_violations and
                                                  not eq_residuals and expected),
                          status="PASS" if (ex["pass"] and ex["reduced"] and
                                             not ub_violations and
                                             not eq_residuals and expected)
                                     else "exact-negative-or-invalid")
        else:
            repair["status"] = "pinned-solve-failed"
        result["repair"] = repair
    OUT.write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps({k: result[k] for k in
                      ("exact_rank", "inconsistent_reduced_row",
                       "certificate_support", "status")}, indent=1))
    if "repair" in result:
        print(json.dumps({k: result["repair"].get(k) for k in
                          ("removed_row", "pinned_exact_rank",
                           "pinned_free_columns", "status",
                           "exact_reduced_feasible")}, indent=1))
        print("gap", result["repair"].get("solution", {}).get("gap"))


if __name__ == "__main__":
    main()
