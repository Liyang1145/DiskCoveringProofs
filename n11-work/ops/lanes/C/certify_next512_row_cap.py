#!/usr/bin/env python3
"""Exact-rational upper bounds excluding the seven public next512 failures.

HiGHS was used only to suggest the dyadic dual weights below.  This script
rechecks every hypothesis and conclusion with Fraction arithmetic.  If y >= 0,
sum y = 1, and sum_q y_q row_a(i,j,q) <= db(i,j)/4096, then for every
nonnegative row vector lam and every rmin <= min_q endpointLo(s_q) + A_q lam,

    rmin - sum_k lam_k db_k/4096 <= sum_q y_q endpointLo(s_q).

Thus the weighted endpoint value is an exact upper bound on the attainable
increase from the 90-row cap.  No floating-point value enters the verdict.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import recheck_next512_rows as common

HERE = Path(__file__).resolve().parent
OUT = HERE / "next512-row-cap-certificates.json"

# HiGHS-selected dyadic weights, represented as (numerators, denominator).
CANDIDATES = {
    1409: ([0, 1, 0, 2, 2, 0, 0, 1, 2], 8),
    2337: ([0, 0, 0, 2, 1, 1, 0, 1, 3], 8),
    2341: ([0, 1, 0, 2, 1, 0, 1, 1, 2], 8),
    2356: ([0, 1, 0, 4, 2, 2, 0, 2, 5], 16),
    2360: ([0, 0, 1, 4, 3, 1, 0, 3, 4], 16),
    2368: ([0, 0, 1, 2, 1, 0, 1, 1, 2], 8),
    2370: ([0, 0, 0, 2, 1, 1, 0, 1, 3], 8),
}


def certify(rec, db, weights):
    y = [Q(v, 16) for v in weights[0]] if weights[1] == 16 else \
        [Q(v, weights[1]) for v in weights[0]]
    if any(v < 0 for v in y) or sum(y) != 1:
        raise AssertionError(f"node {rec['id']}: invalid dual weights")

    row_slacks = []
    for k, (i, j) in enumerate(common.PAIRS):
        row_cap = Q(db[i][j], 4096)
        weighted_row = sum(y[q] * common.row_a(i, j, q) for q in range(9))
        if weighted_row > row_cap:
            raise AssertionError(
                f"node {rec['id']}: row {(i, j)} violates cap by {weighted_row-row_cap}")
        row_slacks.append(row_cap - weighted_row)

    endpoint = [common.endpoint_lo(Q(s)) for s in rec["g"]]
    upper_gain = sum(y[q] * endpoint[q] for q in range(9))
    required_gain = common.T2 - Q(rec["f0Lo"])
    if not upper_gain < required_gain:
        raise AssertionError(
            f"node {rec['id']}: bound {upper_gain} does not exclude {required_gain}")

    return {
        "id": rec["id"],
        "weights": [str(v) for v in y],
        "weight_sum": str(sum(y)),
        "row_cap_violations": 0,
        "min_row_cap_slack": str(min(row_slacks)),
        "upper_gain": str(upper_gain),
        "required_gain": str(required_gain),
        "strict_margin": str(required_gain - upper_gain),
        "excludes_90_row_pass": True,
    }


def main():
    text = common.DBM.read_text()
    rows = json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))["records"]
    failures = [rec for rec in rows if not rec["pass"]]
    if {rec["id"] for rec in failures} != set(CANDIDATES):
        raise AssertionError("public failure set changed; refusing stale certificates")

    certs = [certify(rec, common.parse_db(text, rec["id"]), CANDIDATES[rec["id"]])
             for rec in failures]
    result = {
        "scope": "public next512 HOST failures under the 90 ordered-pair row cap; exact rational certificate, no kernel credit",
        "proposal_sha256": hashlib.sha256(common.PROPOSAL.read_bytes()).hexdigest().upper(),
        "dbm_sha256": hashlib.sha256(common.DBM.read_bytes()).hexdigest().upper(),
        "records_checked": len(rows),
        "failures_excluded": len(certs),
        "certificates": certs,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "certificates"}, indent=2))
    for cert in certs:
        print(cert["id"], "strict margin", float(Q(cert["strict_margin"])))


if __name__ == "__main__":
    main()
