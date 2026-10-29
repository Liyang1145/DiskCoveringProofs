#!/usr/bin/env python3
"""Exact exhaustive <=5-field gain search for the seven public residual records.

For a fixed five-field support, the 100 ordered-pair caps collapse to at most
31 distinct half-spaces. The cap-feasible piecewise-linear gain is maximised at
a rational vertex. A PASS is a genuine five-field rescue; failure is evidence
only for supports of size at most five, not a kernel theorem.
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


def det(matrix):
    n = len(matrix)
    if n == 1:
        return matrix[0][0]
    return sum(((-1) ** c) * matrix[0][c] * det(
        [row[:c] + row[c + 1:] for row in matrix[1:]]) for c in range(n))


def solve(lines):
    matrix = [list(line[:-1]) for line in lines]
    rhs = [line[-1] for line in lines]
    denominator = det(matrix)
    if denominator == 0:
        return None
    result = []
    for column in range(len(matrix)):
        changed = [row[:] for row in matrix]
        for row in range(len(matrix)):
            changed[row][column] = rhs[row]
        result.append(det(changed) / denominator)
    return tuple(result)


def face5(fields, gains, rhs):
    subset_rhs = {}
    for (i, j), cap in rhs.items():
        mask = sum(1 << k for k, field in enumerate(fields)
                   if i <= field < j)
        subset_rhs[mask] = min(cap, subset_rhs.get(mask, cap))

    lines = [tuple(Q(-1 if k == column else 0) for k in range(4)) + (Q(0),)
             for column in range(4)]
    lines.append((Q(1), Q(1), Q(1), Q(1), Q(1)))
    for mask, cap in subset_rhs.items():
        bits = [Q(1 if mask & (1 << k) else 0) for k in range(5)]
        lines.append(tuple(bits[k] - bits[4] for k in range(4)) +
                     (cap - bits[4],))

    best = None
    for tight in combinations(lines, 4):
        point = solve(tight)
        if point is None:
            continue
        if all(A * point[0] + B * point[1] + C * point[2] + D * point[3] <= E
               for A, B, C, D, E in lines):
            gain = gains[fields[4]] + sum(
                (gains[fields[k]] - gains[fields[4]]) * point[k]
                for k in range(4))
            if best is None or gain > best[0]:
                best = (gain,) + point
    return best


def main():
    prop_path = ROOT / "evidence-20261028/inputs/paid16-general-next512.json"
    recs = {rec["id"]: rec for rec in json.loads(
        prop_path.read_text(encoding="utf-8-sig"))["records"]}
    text = common.DBM.read_text()
    results = []
    for node in IDS:
        rec = recs[node]
        db = common.parse_db(text, node)
        rhs = {ij: Q(db[ij[0]][ij[1]], 4096) for ij in PAIRS}
        gains = [common.endpoint_lo(Q(s)) for s in rec["g"]]
        required = common.T2 - Q(rec["f0Lo"])
        best = None
        for fields in combinations(range(9), 5):
            candidate = face5(fields, gains, rhs)
            if candidate is not None and (best is None or candidate[0] > best[0]):
                best = (candidate[0], fields, candidate[1:])
        status = ("PASS" if best is not None and best[0] > required else
                  "no <=5-field rescue")
        row = {
            "id": node,
            "best_gain": str(best[0]) if best else None,
            "support": list(best[1]) if best else None,
            "coordinates": [str(v) for v in best[2]] if best else None,
            "required": str(required),
            "exact_margin": str(best[0] - required) if best else None,
            "status": status,
            "faces_checked": len(list(combinations(range(9), 5))),
        }
        results.append(row)
        print(node, status,
              ("margin=%.3e" % float(best[0] - required)) if best else "",
              "support=", row["support"])

    payload = {
        "scope": "exact <=5-field HOST-only search; no kernel credit",
        "proposal_sha256": hashlib.sha256(prop_path.read_bytes()).hexdigest().upper(),
        "dbm_sha256": hashlib.sha256(common.DBM.read_bytes()).hexdigest().upper(),
        "records": results,
        "pass_count": sum(r["status"] == "PASS" for r in results),
    }
    (HERE / "residual-mixture-faces5.json").write_text(
        json.dumps(payload, indent=1) + "\n")
    print("pass_count", payload["pass_count"])


if __name__ == "__main__":
    main()
