#!/usr/bin/env python3
"""Exact-rational audit of the single-peak q0 degree-three edge reduction.

This checks the emitted witness of each edge is a global discrete maximum and
that the sequence increases to it and decreases afterwards.  It is candidate
finite data for the Lean shape obligations, not a kernel proof.
"""
from __future__ import annotations

import hashlib
import json
import re
from fractions import Fraction as F
from math import factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "q0-degree3-piecewise-8.json"
OUT = HERE / "q0-degree3-edge-unimodal.json"
LEAN = HERE.parents[3] / "n11-work/lean/N11Formalization/SevenClassQ0Deg3UpperReductionUnimodal.lean"
N = 2048
A = F(19, 50) ** 2
FACT = [factorial(i) for i in range(30)]


def sin_t(q: F) -> F:
    total, power, square = F(0), q, q * q
    for j in range(15):
        total += F((-1) ** j, FACT[2 * j + 1]) * power
        power *= square
    return total


def sin_hi(q: F) -> F:
    return sin_t(q) + abs(q) ** 29 / FACT[29]


def main() -> None:
    raw = SRC.read_bytes()
    data = json.loads(raw)
    assert data["N"] == N and len(data["edges"]) == 21
    mu, U = [F(x) for x in data["mu"]], F(data["piHi"])
    rows = []
    for i, edge in enumerate(data["edges"]):
        b = sum(mu[j] for j in edge["edge"])
        vals = [A * sin_hi(U * k / N) - b * (U * k / N) for k in range(N + 1)]
        witness = edge["witnessK"]
        peak = vals[witness]
        assert peak == max(vals) == F(edge["max"]), i
        assert all(vals[k] <= vals[k + 1] for k in range(witness)), i
        assert all(vals[k] >= vals[k + 1] for k in range(witness, N)), i
        rows.append({"edge": edge["edge"], "witnessK": witness,
                     "peak": str(peak), "increasingPrefix": True,
                     "decreasingSuffix": True})
    lean = LEAN.read_text(encoding="utf-8")
    block = lean.split("def edgeCoeff : Fin 21 → ℚ := ![", 1)[1].split("]", 1)[0]
    lean_coeffs = [
        F(int(num), int(den))
        for num, den in re.findall(r"\(\s*(-?\d+)\s*/\s*(\d+)\s*\)", block)
    ]
    expected = [sum(mu[j] for j in edge["edge"]) for edge in data["edges"]]
    assert lean_coeffs == expected, (len(lean_coeffs), len(expected))

    report = {
        "scope": "exact discrete unimodality, peak values, and Lean edgeCoeff vector; not a Lean proof",
        "source": SRC.name,
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "N": N,
        "edges": rows,
        "allUnimodal": True,
    }
    OUT.write_text(json.dumps(report, indent=1) + "\n")
    print(f"PASS: {len(rows)} edges are exactly single-peaked; witnesses, maxima, and Lean coefficients agree")
    print("sha256 json:", hashlib.sha256(OUT.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
