#!/usr/bin/env python3
"""Exact exhaustive 3-field search for the seven public residual records.

On a face supported on fields p<q<r write y = a*e_p + b*e_q + (1-a-b)*e_r.
Every row cap is an interval-sum bound, so its restriction to the face is one
of at most seven distinct half-planes.  We enumerate every vertex of the
resulting bounded 2-D polygon exactly over Fraction.  A PASS includes an exact
9-field mixture witness satisfying all 100 caps.  Failure means only that no
<=3-field mixture passes; it is not a full LP infeasibility claim.
"""
from fractions import Fraction as Q
from itertools import combinations
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common

IDS = [1409, 2337, 2341, 2356, 2360, 2368, 2370]
PAIRS = [(i, j) for i in range(10) for j in range(10)]


def intersect(l1, l2):
    a, b, c = l1
    d, e, f = l2
    det = a * e - b * d
    if det == 0:
        return None
    return ((c * e - b * f) / det, (a * f - c * d) / det)


def face3(p, q, r, E, rhs):
    # Minimum rhs for each intersection pattern of an interval with {p,q,r}.
    subset_rhs = {}
    for (i, j), cap in rhs.items():
        mask = ((1 if p in range(i, j) else 0) |
                (2 if q in range(i, j) else 0) |
                (4 if r in range(i, j) else 0))
        subset_rhs[mask] = min(cap, subset_rhs.get(mask, cap))

    lines = [(-Q(1), Q(0), Q(0)), (Q(0), -Q(1), Q(0)), (Q(1), Q(1), Q(1))]
    for mask, cap in subset_rhs.items():
        cp = Q(1 if mask & 1 else 0)
        cq = Q(1 if mask & 2 else 0)
        cr = Q(1 if mask & 4 else 0)
        # cp*a + cq*b + cr*(1-a-b) <= cap
        lines.append((cp - cr, cq - cr, cap - cr))

    cands = []
    for l1, l2 in combinations(lines, 2):
        point = intersect(l1, l2)
        if point is not None:
            cands.append(point)
    best = None
    for a, b in cands:
        if all(A * a + B * b <= C for A, B, C in lines):
            gain = E[r] + (E[p] - E[r]) * a + (E[q] - E[r]) * b
            if best is None or gain > best[0]:
                best = (gain, a, b)
    return best


def main():
    prop = json.loads((ROOT / "evidence-20261028/inputs/paid16-general-next512.json")
                      .read_text(encoding="utf-8-sig"))
    recs = {rec["id"]: rec for rec in prop["records"]}
    text = common.DBM.read_text()
    results = []
    for node in IDS:
        rec = recs[node]
        db = common.parse_db(text, node)
        rhs = {ij: Q(db[ij[0]][ij[1]], 4096) for ij in PAIRS}
        E = [common.endpoint_lo(Q(s)) for s in rec["g"]]
        req = common.T2 - Q(rec["f0Lo"])
        best = None
        for p, q, r in combinations(range(9), 3):
            candidate = face3(p, q, r, E, rhs)
            if candidate is not None and (best is None or candidate[0] > best[0]):
                best = (candidate[0], p, q, r, candidate[1], candidate[2])
        status = ("PASS" if best is not None and best[0] > req else
                  "no <=3-field rescue")
        row = {
            "id": node,
            "best_gain": str(best[0]) if best else None,
            "support": [best[1], best[2], best[3]] if best else None,
            "alpha": str(best[4]) if best else None,
            "beta": str(best[5]) if best else None,
            "required": str(req),
            "exact_margin": str(best[0] - req) if best else None,
            "status": status,
            "faces_checked": len(list(combinations(range(9), 3))),
        }
        results.append(row)
        print(node, status,
              ("margin=%.3e" % float(best[0] - req)) if best else "",
              "support=", row["support"])

        if best is not None:
            p, q, r, a, b = best[1], best[2], best[3], best[4], best[5]
            y = [Q(0)] * 9
            y[p], y[q], y[r] = a, b, 1 - a - b
            assert all(v >= 0 for v in y) and sum(y) == 1
            assert sum(y[k] * E[k] for k in range(9)) == best[0]
            assert all(sum(y[k] * common.row_a(i, j, k) for k in range(9)) <= rhs[(i, j)]
                       for i, j in PAIRS), node
            if status == "PASS":
                assert Q(rec["f0Lo"]) + sum(y[k] * E[k] for k in range(9)) < common.T2

    payload = {
        "scope": "exact <=3-field HOST-only search; no kernel credit",
        "proposal_sha256": hashlib.sha256(
            (ROOT / "evidence-20261028/inputs/paid16-general-next512.json").read_bytes()
        ).hexdigest().upper(),
        "dbm_sha256": hashlib.sha256(common.DBM.read_bytes()).hexdigest().upper(),
        "records": results,
        "pass_count": sum(r["status"] == "PASS" for r in results),
    }
    (HERE / "residual-mixture-faces3.json").write_text(json.dumps(payload, indent=1) + "\n")
    print("pass_count", payload["pass_count"])
    print("wrote residual-mixture-faces3.json")


if __name__ == "__main__":
    main()
