#!/usr/bin/env python3
"""Exact exhaustive 4-field search for the seven public residual records.

The 100 ordered-pair row caps collapse on a fixed 4-field support to at most
15 distinct half-spaces.  Vertices of the resulting bounded polytope are
intersections of three tight half-spaces; all arithmetic is rational.  A PASS
would include an exact 9-field cap-feasible witness.  Failure means only that
no <=4-field mixture passes (the existing five/six-field cap certificates
already exclude every number of rows).
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


def det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def solve3(l1, l2, l3):
    m = [list(l[:3]) for l in (l1, l2, l3)]
    rhs = [l[3] for l in (l1, l2, l3)]
    d = det3(m)
    if d == 0:
        return None
    out = []
    for col in range(3):
        mc = [row[:] for row in m]
        for k in range(3):
            mc[k][col] = rhs[k]
        out.append(det3(mc) / d)
    return tuple(out)


def face4(fields, E, rhs):
    subset_rhs = {}
    for (i, j), cap in rhs.items():
        mask = sum(1 << k for k, field in enumerate(fields)
                   if i <= field < j)
        subset_rhs[mask] = min(cap, subset_rhs.get(mask, cap))

    lines = [(Q(-1), Q(0), Q(0), Q(0)),
             (Q(0), Q(-1), Q(0), Q(0)),
             (Q(0), Q(0), -Q(1), Q(0)),
             (Q(1), Q(1), Q(1), Q(1))]
    for mask, cap in subset_rhs.items():
        bits = [Q(1 if mask & (1 << k) else 0) for k in range(4)]
        lines.append(tuple(bits[k] - bits[3] for k in range(3)) +
                     (cap - bits[3],))

    best = None
    for l1, l2, l3 in combinations(lines, 3):
        point = solve3(l1, l2, l3)
        if point is None:
            continue
        if all(A * point[0] + B * point[1] + C * point[2] <= D
               for A, B, C, D in lines):
            gain = E[fields[3]] + sum(
                (E[fields[k]] - E[fields[3]]) * point[k] for k in range(3))
            if best is None or gain > best[0]:
                best = (gain,) + point
    return best


def main():
    prop_path = ROOT / "evidence-20261028/inputs/paid16-general-next512.json"
    recs = {rec["id"]: rec for rec in
            json.loads(prop_path.read_text(encoding="utf-8-sig"))["records"]}
    text = common.DBM.read_text()
    results = []
    for node in IDS:
        rec = recs[node]
        db = common.parse_db(text, node)
        rhs = {ij: Q(db[ij[0]][ij[1]], 4096) for ij in PAIRS}
        E = [common.endpoint_lo(Q(s)) for s in rec["g"]]
        req = common.T2 - Q(rec["f0Lo"])
        best = None
        for fields in combinations(range(9), 4):
            candidate = face4(fields, E, rhs)
            if candidate is not None and (best is None or candidate[0] > best[0]):
                best = (candidate[0], fields, candidate[1:])
        status = ("PASS" if best is not None and best[0] > req else
                  "no <=4-field rescue")
        row = {
            "id": node,
            "best_gain": str(best[0]) if best else None,
            "support": list(best[1]) if best else None,
            "coordinates": [str(v) for v in best[2]] if best else None,
            "required": str(req),
            "exact_margin": str(best[0] - req) if best else None,
            "status": status,
            "faces_checked": len(list(combinations(range(9), 4))),
        }
        results.append(row)
        print(node, status,
              ("margin=%.3e" % float(best[0] - req)) if best else "",
              "support=", row["support"])

        if best is not None:
            fields, coords = best[1], best[2]
            y = [Q(0)] * 9
            for k in range(3):
                y[fields[k]] = coords[k]
            y[fields[3]] = 1 - sum(coords)
            assert all(v >= 0 for v in y) and sum(y) == 1
            assert sum(y[k] * E[k] for k in range(9)) == best[0]
            assert all(sum(y[k] * common.row_a(i, j, k) for k in range(9)) <= rhs[(i, j)]
                       for i, j in PAIRS), node

    payload = {
        "scope": "exact <=4-field HOST-only search; no kernel credit",
        "proposal_sha256": hashlib.sha256(prop_path.read_bytes()).hexdigest().upper(),
        "dbm_sha256": hashlib.sha256(common.DBM.read_bytes()).hexdigest().upper(),
        "records": results,
        "pass_count": sum(r["status"] == "PASS" for r in results),
    }
    (HERE / "residual-mixture-faces4.json").write_text(json.dumps(payload, indent=1) + "\n")
    print("pass_count", payload["pass_count"])


if __name__ == "__main__":
    main()
