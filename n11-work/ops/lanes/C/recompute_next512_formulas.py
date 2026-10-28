#!/usr/bin/env python3
"""Recompute the frozen next512 survey's mathematical fields exactly.

Unlike `recheck_next512_rows.py`, this audit does not trust stored `cl`, `g`,
or `f0Lo`.  It derives them from `beta`, `packets`, and the frozen accepted
field weights using `Fraction`, then checks the stored dual-row inequalities
and lower-bound identity.  This is an evidence audit, not kernel credit.
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

PROPOSAL_SHA = "F49F06FC57A818E464D8DCBDAACE2E4D57A3C2E84CEA27FE86C4551363F3DD16"
T2 = Q(1899919265599193545242591, 5000000000000000000000000) ** 2
LQ = 2 * Q(449404532622434011541355675101, 1152921504606846976000000000000)
Lq = 2 * Q(1150475603510479590494077, 2951479051793528258560000)
PI_LO = Q(314159265358979323846, 10**20)
PI_HI = Q(314159265358979323847, 10**20)
DQ = 9 * LQ - 2 * PI_LO
Dq = 9 * Lq - 2 * PI_HI
ANGLE_PAIRS = [(i, j) for i in range(9) for j in range(i + 1, 9)]
DBM_PAIRS = [(i, j) for i in range(10) for j in range(10) if i != j]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def endpoint_lo(a, b, x):
    return x * (a if 0 <= x else b)


def row_a(i, j, q):
    return (1 if q < j else 0) - (1 if q < i else 0)


def parse_db(text, node):
    match = re.search(
        rf"def node{node} : Node 5011 where\s*db := (.*?)\n\s*terminal :=", text, re.S
    )
    if not match:
        raise ValueError(f"node {node} not found")
    nums = [int(x) for x in re.findall(r"-?\d+", match.group(1))]
    if len(nums) != 100:
        raise ValueError(f"node {node}: got {len(nums)} DBM entries")
    return [nums[10 * i:10 * i + 10] for i in range(10)]


def req(cond, message):
    if not cond:
        raise AssertionError(message)


def main():
    req(sha(PROPOSAL) == PROPOSAL_SHA, "proposal hash changed")
    doc = json.loads(PROPOSAL.read_text(encoding="utf-8-sig"))
    weights = [[Q(str(x)) / Q(10**12) for x in row] for row in doc["weights"]]
    req(len(weights) == 16 and all(len(row) == 36 for row in weights),
        "weights are not 16 x 36")
    db_text = DBM.read_text()

    failures = []
    passing = 0
    for rec in doc["records"]:
        rid = rec["id"]
        beta = [Q(x) for x in rec["beta"]]
        req(len(beta) == 16, f"node {rid}: beta length")
        req(all(x >= 0 for x in beta) and sum(beta) == 1,
            f"node {rid}: beta is not a probability vector")
        req(len(rec["packets"]) == 36, f"node {rid}: packet count")
        slopes = [Q(p["s"]) for p in rec["packets"]]
        inters = [Q(p["c"]) for p in rec["packets"]]

        W = [sum(beta[f] * weights[f][k] for f in range(16)) for k in range(36)]
        cl = sum(W[k] * slopes[k] * (ANGLE_PAIRS[k][0] - ANGLE_PAIRS[k][1])
                 for k in range(36))
        cv = sum(W[k] * inters[k] for k in range(36))
        g = [sum(W[k] * slopes[k] for k in range(36)
                 if ANGLE_PAIRS[k][0] <= q < ANGLE_PAIRS[k][1])
             for q in range(9)]
        f0 = cv + endpoint_lo(Lq, LQ, cl)

        req(cl == Q(rec["cl"]), f"node {rid}: stored cl mismatch")
        req(g == [Q(x) for x in rec["g"]], f"node {rid}: stored g mismatch")
        req(f0 == Q(rec["f0Lo"]), f"node {rid}: stored f0Lo mismatch")

        lam = [Q(x) for x in rec["lam"]]
        req(all(x >= 0 for x in lam), f"node {rid}: negative lambda")
        req(len(rec["row_from"]) == len(lam) == len(rec["row_to"]),
            f"node {rid}: row count")
        db = parse_db(db_text, rid)
        rmin = Q(rec["rmin"])
        rhs = [endpoint_lo(Dq, DQ, g[q]) + sum(
            lam[k] * row_a(rec["row_from"][k], rec["row_to"][k], q)
            for k in range(len(lam))) for q in range(9)]
        req(all(rmin <= x for x in rhs), f"node {rid}: reduced-cost failure")
        # The frozen records use arbitrary ordered rows, not the first rows.
        lam_b = sum(lam[k] * Q(db[rec["row_from"][k]][rec["row_to"][k]], 4096)
                    for k in range(len(lam)))
        req(lam_b == Q(rec["lamB"]), f"node {rid}: stored lamB mismatch")
        lower = f0 - lam_b + rmin
        req(lower == Q(rec["lower"]), f"node {rid}: stored lower mismatch")
        req((lower > T2) == rec["pass"], f"node {rid}: pass flag mismatch")
        if rec["pass"]:
            passing += 1
        else:
            failures.append(rid)

    print(f"PASS: recomputed {len(doc['records'])} records; "
          f"passing={passing}; failures={len(failures)}")
    print("failure ids:", ",".join(map(str, failures)))
    print("scope: exact Python recomputation from frozen inputs, not kernel credit")


if __name__ == "__main__":
    main()
