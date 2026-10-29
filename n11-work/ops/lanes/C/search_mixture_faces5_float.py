#!/usr/bin/env python3
"""Fast float prefilter + exact-rational recheck for <=5-field rescues.

Float arithmetic only ranks five-field supports. Every reported PASS is
recomputed by `residual_mixture_faces5.face5` with Fractions and checked on all
100 ordered-pair caps. A miss is not a proof over supports of size 5--9.
"""
from fractions import Fraction as Q
from itertools import combinations
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
import recheck_next512_rows as common
import residual_mixture_faces5 as exact5

IDS = [2356, 2360]
PAIRS = exact5.PAIRS


def float_face5(fields, gains, rhs):
    sub = {}
    for (i, j), cap in rhs.items():
        bits = [float(common.row_a(i, j, f)) for f in fields]
        coeffs = tuple(bits[k] - bits[4] for k in range(4))
        line_rhs = float(cap) - bits[4]
        sub[coeffs] = min(line_rhs, sub.get(coeffs, line_rhs))
    inequalities = [tuple(-1.0 if k == c else 0.0 for k in range(4)) + (0.0,)
                    for c in range(4)]
    inequalities += [coeffs + (line_rhs,) for coeffs, line_rhs in sub.items()]
    simplex = (1.0, 1.0, 1.0, 1.0, 1.0)
    gain = lambda p: gains[fields[4]] + sum(
        (gains[fields[k]] - gains[fields[4]]) * p[k] for k in range(4))
    feasible = lambda p: all(
        a * p[0] + b * p[1] + c * p[2] + d * p[3] <= e
        for a, b, c, d, e in inequalities)
    best = None
    if feasible((0.0, 0.0, 0.0, 0.0)):
        best = (gain((0.0, 0.0, 0.0, 0.0)),) + (0.0,) * 4
    for tight in combinations(inequalities, 3):
        point = exact5.solve((simplex,) + tight)
        if point is not None and feasible(point):
            value = gain(point)
            if best is None or value > best[0]:
                best = (value,) + point
    for tight in combinations(inequalities, 4):
        point = exact5.solve(tight)
        if point is not None and feasible(point):
            value = gain(point)
            if best is None or value > best[0]:
                best = (value,) + point
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ids", default="2356,2360")
    ap.add_argument("--top", type=int, default=8)
    ap.add_argument("--time-budget", type=float, default=70.0)
    args = ap.parse_args()
    ids = [int(v) for v in args.ids.split(",") if v]
    started = time.monotonic()
    prop = ROOT / "evidence-20261028/inputs/paid16-general-next512.json"
    recs = {r["id"]: r for r in json.loads(prop.read_text(encoding="utf-8-sig"))["records"]}
    text = common.DBM.read_text()
    results = []
    for node in ids:
        rec = recs[node]
        db = common.parse_db(text, node)
        rhs = {ij: Q(db[ij[0]][ij[1]], 4096) for ij in PAIRS}
        gains_f = [float(common.endpoint_lo(Q(s))) for s in rec["g"]]
        required = common.T2 - Q(rec["f0Lo"])
        ranked = []
        timed_out = False
        faces = list(combinations(range(9), 5))
        for idx, fields in enumerate(faces):
            if time.monotonic() - started > args.time_budget:
                timed_out = True
                break
            cand = float_face5(fields, gains_f, rhs)
            if cand is not None:
                ranked.append((cand[0], fields))
        ranked.sort(reverse=True)
        best = None
        for _, fields in ranked[:args.top]:
            cand = exact5.face5(fields, [common.endpoint_lo(Q(s)) for s in rec["g"]], rhs)
            if cand is not None and (best is None or cand[0] > best[0]):
                best = (cand[0], fields, cand[1:])
        row = {"id": node, "required": str(required),
               "float_faces_checked": len(ranked), "faces_total": len(faces),
               "float_timeout": timed_out, "exact_supports_checked":
               min(args.top, len(ranked)), "best_gain": None,
               "support": None, "coordinates": None, "exact_margin": None,
               "status": "no rank PASS among checked exact supports"}
        if best is not None:
            row.update(best_gain=str(best[0]), support=list(best[1]),
                       coordinates=[str(v) for v in best[2]],
                       exact_margin=str(best[0] - required),
                       status="PASS" if best[0] > required else row["status"])
            y = [Q(0)] * 9
            for k in range(4): y[best[1][k]] = best[2][k]
            y[best[1][4]] = 1 - sum(best[2])
            assert all(v >= 0 for v in y) and sum(y) == 1
            assert all(sum(y[q] * common.row_a(i, j, q) for q in range(9)) <= rhs[(i, j)]
                       for i, j in PAIRS), node
        results.append(row)
        print(node, row["status"], "ranked", len(ranked),
              "exact_top", row["exact_supports_checked"],
              "margin", row["exact_margin"])
    out = {"scope": "float support ranking plus exact <=5-field recheck; no kernel credit",
           "proposal_sha256": hashlib.sha256(prop.read_bytes()).hexdigest().upper(),
           "dbm_sha256": hashlib.sha256(common.DBM.read_bytes()).hexdigest().upper(),
           "records": results,
           "pass_count": sum(r["status"] == "PASS" for r in results)}
    path = HERE / ("residual-mixture-faces5-float-" + "-".join(map(str, ids)) + ".json")
    path.write_text(json.dumps(out, indent=1) + "\n")
    print("pass_count", out["pass_count"])

if __name__ == "__main__":
    main()
