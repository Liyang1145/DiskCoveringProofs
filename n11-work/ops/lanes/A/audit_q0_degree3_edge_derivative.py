#!/usr/bin/env python3
"""Exact derivative-sign audit for the q0 degree-three edge upper brackets.

For `E_b(q) = (19/50)^2 * sinHi(q) - b*q`, the derivative is
`(19/50)^2 * cosHi(q) - b`.  This script checks the exact rational sign of that
expression at every grid point.  The result is candidate data for a Lean proof
using `SevenClassQ0Deg3Cos.cosHiNLag_antitone`; it is not a kernel proof.
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "q0-degree3-piecewise-8.json"
OUT = HERE / "q0-degree3-edge-derivative.json"
N = 2048
A = F(19, 50) ** 2
FACT = [factorial(i) for i in range(30)]


def cos_hi(q: F) -> F:
    total, power, square = F(0), F(1), q * q
    for j in range(14):
        total += F((-1) ** j, FACT[2 * j]) * power
        power *= square
    return total + abs(q) ** 28 / FACT[28]


def main() -> None:
    raw = SRC.read_bytes()
    data = json.loads(raw)
    assert data["N"] == N and len(data["edges"]) == 21
    mu, U = [F(x) for x in data["mu"]], F(data["piHi"])
    rows = []
    for i, edge in enumerate(data["edges"]):
        b = sum(mu[j] for j in edge["edge"])
        witness = edge["witnessK"]
        slopes = [A * cos_hi(U * k / N) - b for k in range(N + 1)]
        assert all(slopes[k] >= 0 for k in range(witness)), i
        assert all(slopes[k] <= 0 for k in range(witness + 1, N + 1)), i
        rows.append({
            "edge": edge["edge"],
            "witnessK": witness,
            "coefficient": str(b),
            "derivativeAtPeak": str(slopes[witness]),
            "prefixMinusSuffixSign": True,
            "minimumPrefixSlope": str(min(slopes[:witness + 1])),
            "maximumSuffixSlope": str(max(slopes[witness:])),
        })
    report = {
        "scope": "exact rational derivative signs at grid nodes; not a Lean proof",
        "source": SRC.name,
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "N": N,
        "A": str(A),
        "edges": rows,
        "allDerivativeSignsAligned": True,
    }
    OUT.write_text(json.dumps(report, indent=1) + "\n")
    print(f"PASS: {len(rows)} edges have exact derivative signs aligned with their peaks")
    print("sha256 json:", hashlib.sha256(OUT.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
