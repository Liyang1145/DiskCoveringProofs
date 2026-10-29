#!/usr/bin/env python3
"""Deterministic exact-rational check of MCap's weighted-row identity.

This checks the finite-sum algebra used in
`PaidCellCertificateMCap.weighted_reduced_le`, not the Lean theorem or its
kernel verdict.  It is deliberately independent of floating point.
"""
import hashlib
import json
import random
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MCAP = ROOT / "n11-work/lean/N11Formalization/PaidCellCertificateMCap.lean"
OUT = HERE / "mcap-weighted-identity-check.json"
PAIRS = [(i, j) for i in range(10) for j in range(10)]


def row_a(i, j, q):
    return (1 if q < j else 0) - (1 if q < i else 0)


def check_case(rng, m):
    rows = [PAIRS[rng.randrange(len(PAIRS))] for _ in range(m)]
    lam = [Q(rng.randrange(17), rng.randrange(1, 17)) for _ in range(m)]
    raw_y = [rng.randrange(17) for _ in range(9)]
    total = sum(raw_y)
    if total == 0:
        raw_y[0] = 1
        total = 1
    y = [Q(value, total) for value in raw_y]

    rho = [sum(lam[a] * row_a(*rows[a], q) for a in range(m))
           for q in range(9)]
    lhs = sum(y[q] * rho[q] for q in range(9))
    rhs = sum(lam[a] * sum(y[q] * row_a(*rows[a], q) for q in range(9))
              for a in range(m))
    if lhs != rhs:
        raise AssertionError((m, rows, lam, y, lhs, rhs))
    return lhs


def main():
    rng = random.Random(20261029)
    cases = 0
    for m in (1, 2, 5, 9, 16):
        for _ in range(200):
            check_case(rng, m)
            cases += 1
    payload = {
        "scope": "exact-rational finite-sum identity only; no Lean/kernel credit",
        "seed": 20261029,
        "row_counts": [1, 2, 5, 9, 16],
        "cases_per_row_count": 200,
        "cases_checked": cases,
        "failures": 0,
        "mcap_sha256": hashlib.sha256(MCAP.read_bytes()).hexdigest().upper(),
    }
    if cases != 1000:
        raise AssertionError(cases)
    OUT.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
