#!/usr/bin/env python3
"""Exact audit and 90-row LP search for the frozen next512 HOST survey.

The float LP is a search only. Every reported extension is re-evaluated with
Fraction arithmetic from the frozen records and the exact rational pi bounds.
Output is evidence of a candidate row extension, not kernel credit.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PROPOSAL = ROOT / "n11-work/evidence-20261028/inputs/paid16-general-next512.json"
DBM = ROOT / "n11-work/lean/N11Formalization/DBMSourceTreeData.lean"
OUT = HERE / "next512-row-extension-results.json"

T2 = Q(1899919265599193545242591, 5000000000000000000000000) ** 2
LQ = 2 * Q(449404532622434011541355675101, 1152921504606846976000000000000)
PI_LO = Q(314159265358979323846, 10**20)
PI_HI = Q(314159265358979323847, 10**20)
DQ = 9 * LQ - 2 * PI_LO
Dq = 9 * Q(2 * 1150475603510479590494077, 2951479051793528258560000) - 2 * PI_HI
PAIRS = [(i, j) for i in range(10) for j in range(10) if i != j]


def endpoint_lo(g):
    return g * Dq if 0 <= g else g * DQ


def row_a(i, j, q):
    return (1 if q < j else 0) - (1 if q < i else 0)


def evaluate(rec, db, lam):
    rmin = min(endpoint_lo(Q(s)) + sum(Q(lam[k]) * row_a(i, j, q)
               for k, (i, j) in enumerate(PAIRS) if lam[k])
               for q, s in enumerate(rec["g"]))
    lam_b = sum(Q(lam[k]) * Q(db[i][j], 4096)
                for k, (i, j) in enumerate(PAIRS) if lam[k])
    lower = Q(rec["f0Lo"]) - lam_b + rmin
    return {"rmin": str(rmin), "lamB": str(lam_b), "lower": str(lower),
            "gap": str(lower - T2), "pass": lower > T2}


def parse_db(text, node):
    m = re.search(rf"def node{node} : Node 5011 where\s*db := (.*?)\n\s*terminal :=",
                  text, re.S)
    if not m:
        raise ValueError(f"node {node} not found")
    nums = [int(x) for x in re.findall(r"-?\d+", m.group(1))]
    if len(nums) != 100:
        raise ValueError(f"node {node}: got {len(nums)} DBM entries")
    return [nums[10 * i:10 * i + 10] for i in range(10)]


def main():
    # The LP dependency is search-only.  Exact auditors import this module for
    # PAIRS/row_a/endpoint_lo and must remain runnable without SciPy installed.
    import numpy as np
    from scipy.optimize import linprog

    text = DBM.read_text()
    doc = json.loads(PROPOSAL.read_text(encoding="utf-8-sig"))
    rows = doc["records"]
    identity_errors = []
    for rec in rows:
        if Q(rec["lower"]) != Q(rec["f0Lo"]) - Q(rec["lamB"]) + Q(rec["rmin"]):
            identity_errors.append(rec["id"])
        if (Q(rec["lower"]) > T2) != rec["pass"]:
            identity_errors.append(rec["id"])
    if identity_errors:
        raise AssertionError(f"frozen record identity failures: {identity_errors}")

    extensions = []
    for rec in rows:
        if rec["pass"]:
            continue
        db = parse_db(text, rec["id"])
        ep = [float(endpoint_lo(Q(s))) for s in rec["g"]]
        c = np.zeros(91)
        c[-1] = -1
        for k, (i, j) in enumerate(PAIRS):
            c[k] = db[i][j] / 4096
        A = np.zeros((9, 91))
        for q in range(9):
            A[q, -1] = 1
            for k, (i, j) in enumerate(PAIRS):
                A[q, k] = -row_a(i, j, q)
        lp = linprog(c, A_ub=A, b_ub=np.array(ep),
                     bounds=[(0, None)] * 90 + [(None, None)], method="highs")
        if not lp.success:
            raise RuntimeError(f"node {rec['id']}: {lp.message}")
        lam = [Q(float(v)).limit_denominator(10**18) for v in lp.x[:90]]
        exact = evaluate(rec, db, lam)
        exact["id"] = rec["id"]
        exact["nonzero_rows"] = [[list(PAIRS[k]), str(lam[k])]
                                 for k in range(90) if lam[k]]
        extensions.append(exact)

    result = {
        "scope": "HOST-only exact-rational recheck; no kernel or terminal credit",
        "proposal_sha256": hashlib.sha256(PROPOSAL.read_bytes()).hexdigest().upper(),
        "dbm_sha256": hashlib.sha256(DBM.read_bytes()).hexdigest().upper(),
        "records": len(rows), "frozen_identity_errors": identity_errors,
        "frozen_failures": sum(not r["pass"] for r in rows),
        "new_exact_passes": sum(r["pass"] for r in extensions),
        "extensions": extensions,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "extensions"}, indent=2))
    for r in extensions:
        print(r["id"], r["pass"], "gap", float(Q(r["gap"])),
              "rows", len(r["nonzero_rows"]))


if __name__ == "__main__":
    main()
