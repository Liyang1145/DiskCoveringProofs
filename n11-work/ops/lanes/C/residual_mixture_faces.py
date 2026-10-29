#!/usr/bin/env python3
"""Exact 1- and 2-field search for the residual public records.

Scope (stated, no overclaim): for each id enumerate every mixture supported on at
most two of the nine endpoint fields, y = a*e_p + b*e_q with a+b = 1, a,b >= 0.
On that face every constraint is linear in (a,b), so the optimum is at a vertex of
the 2-D polygon, found by solving pairs of tight constraints exactly.  A reported
PASS is an exact `Fraction` witness: all 100 row caps hold and
F0 + sum_q y_q E_q < T^2.  "fails" only means no <=2-field mixture works; it does
NOT prove the full 9-field LP infeasible.
"""
from fractions import Fraction as Q
from itertools import combinations
import json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common

IDS = [1409, 2337, 2341, 2356, 2360, 2368, 2370]
PAIRS = [(i, j) for i in range(10) for j in range(10)]


def solve2(r1, r2):
    (a, b, c1), (d, e, c2) = r1, r2
    det = a * e - b * d
    if det == 0:
        return None
    return ((c1 * e - b * c2) / det, (a * c2 - c1 * d) / det)


def face_opt(p, q, E, caps):
    lines = [(Q(1), Q(1), Q(1)), (Q(-1), Q(0), Q(0)), (Q(0), Q(-1), Q(0))] + caps
    cands = [(Q(1), Q(0)), (Q(0), Q(1))]
    for r1, r2 in combinations(lines, 2):
        s = solve2(r1, r2)
        if s is not None:
            cands.append(s)
    best = None
    for a, b in cands:
        if a < 0 or b < 0:
            continue
        if all(cp * a + cq * b <= rhs for cp, cq, rhs in lines):
            g = a * E[p] + b * E[q]
            if best is None or g > best[0]:
                best = (g, a, b)
    return best


def main():
    prop = json.loads((ROOT / "evidence-20261028/inputs/paid16-general-next512.json")
                      .read_text(encoding="utf-8-sig"))
    recs = {r["id"]: r for r in prop["records"]}
    text = common.DBM.read_text()
    results = []
    for n in IDS:
        rec = recs[n]
        db = common.parse_db(text, n)
        rhs = {ij: Q(db[ij[0]][ij[1]], 4096) for ij in PAIRS}
        E = [common.endpoint_lo(Q(s)) for s in rec["g"]]
        req = common.T2 - Q(rec["f0Lo"])
        best = None
        for p, q in combinations(range(9), 2):
            caps = [(common.row_a(i, j, p), common.row_a(i, j, q), rhs[(i, j)])
                    for i, j in PAIRS]
            b = face_opt(p, q, E, caps)
            if b is not None and (best is None or b[0] > best[0]):
                best = (b[0], p, q, b[1], b[2])
        for p in range(9):
            if all(common.row_a(i, j, p) <= rhs[(i, j)] for i, j in PAIRS):
                if best is None or E[p] > best[0]:
                    best = (E[p], p, p, Q(1), Q(0))
        status = ("PASS" if best is not None and best[0] > req else
                  "no <=2-field rescue")
        results.append({
            "id": n,
            "best_gain": str(best[0]) if best else None,
            "support": [best[1], best[2]] if best else None,
            "alpha": str(best[3]) if best else None,
            "beta": str(best[4]) if best else None,
            "required": str(req),
            "exact_margin": str(best[0] - req) if best else None,
            "status": status,
        })
        print(n, status,
              ("margin=%.3e" % float(best[0] - req)) if best else "",
              "support=", best[1:3] if best else None)
        if best is not None:
            p, q, a, b = best[1], best[2], best[3], best[4]
            y = [Q(0)] * 9
            y[p] += a
            y[q] += b
            assert all(v >= 0 for v in y) and sum(y) == 1
            assert sum(y[k] * E[k] for k in range(9)) == best[0]
            assert all(sum(y[k] * common.row_a(i, j, k) for k in range(9)) <= rhs[(i, j)]
                       for i, j in PAIRS), n
            assert Q(rec["f0Lo"]) + sum(y[k] * E[k] for k in range(9)) < common.T2
    (HERE / "residual-mixture-faces.json").write_text(json.dumps(results, indent=1) + "\n")
    print("wrote residual-mixture-faces.json")


if __name__ == "__main__":
    main()
