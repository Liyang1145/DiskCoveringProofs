#!/usr/bin/env python3
"""Exact-rational audit of every arithmetic obligation in `SectorBin3`.

This evaluates the frozen row-0 table on nodes 768--1023.  It checks the
certified cosine ceiling used by the strict-step proof, the sine-increment
Lipschitz bound on every pair in the bin, and the resulting strict decrease.
It is source/arithmetic evidence only, not a Lean kernel check.
"""
from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction as F
from math import factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import probe_q0_degree3_nodes as probe  # noqa: E402

PIECE8 = HERE / "q0-degree3-piecewise-8.json"
SOURCE = HERE.parents[2] / "lean/N11Formalization/SevenClassQ0Deg3SectorBin3.lean"
OUT = HERE / "q0-degree3-bin3-proof-obligations-audit.json"
LO, HI = 768, 1023


def cos_hi(q: F) -> F:
    taylor = sum(
        F((-1) ** j, factorial(2 * j)) * q ** (2 * j) for j in range(15)
    )
    return taylor + abs(q) ** 28 / factorial(28)


def main() -> None:
    raw, row = probe.load()
    piece8_raw = PIECE8.read_bytes()
    piece8 = json.loads(piece8_raw)
    mu = probe.mid(row["mu"][0])
    lam = probe.mid(row["lambda"])
    pi_lo, pi_hi = probe.interval(row["pi_interval"])
    qs = [pi_hi * k / probe.N for k in range(probe.N + 1)]
    sines = [probe.sinHi(q) for q in qs]
    cosines = [cos_hi(q) for q in qs]
    node8 = [F(item["node"]) for item in piece8["bins"]]
    nodes = [node8[min(7, 8 * k // probe.N)] for k in range(probe.N + 1)]
    segment = [(2 * a - probe.sinLo(2 * a)) / 2 for a in node8]

    def value(k: int) -> F:
        return segment[min(7, 8 * k // probe.N)] + probe.R2 * sines[k] / 2 \
            + 2 * lam * nodes[k] - mu * qs[k]

    values = [value(k) for k in range(probe.N + 1)]
    coefficient = probe.R2 / 4 - mu
    maximum_cos = max(cosines[LO:HI + 1])
    maximum_sine_increment_defect = max(
        sines[l] - sines[k] - (qs[l] - qs[k]) / 2
        for k in range(LO, HI)
        for l in range(k + 1, HI + 1)
    )
    maximum_bound_defect = max(
        values[l] - values[k] - coefficient * (qs[l] - qs[k])
        for k in range(LO, HI)
        for l in range(k + 1, HI + 1)
    )
    minimum_pair_drop = min(
        values[k] - values[l]
        for k in range(LO, HI)
        for l in range(k + 1, HI + 1)
    )
    adjacent_failures = [
        k for k in range(LO, HI) if not values[k + 1] < values[k]
    ]

    assert pi_lo <= pi_hi
    assert maximum_cos <= F(1, 2)
    assert maximum_sine_increment_defect <= 0
    assert coefficient < 0
    assert maximum_bound_defect <= 0
    assert minimum_pair_drop > 0 and not adjacent_failures
    assert piece8["source_sha256"] == hashlib.sha256(raw).hexdigest()

    report = {
        "scope": "exact-rational proof obligations for row-0 bin 3; no Lean claim",
        "source": str(SOURCE.relative_to(HERE.parents[3])),
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "piecewise_report_sha256": hashlib.sha256(piece8_raw).hexdigest(),
        "nodes": [LO, HI],
        "node_count": HI - LO + 1,
        "pair_count": (HI - LO + 1) * (HI - LO) // 2,
        "maximum_cosHiNLag": str(maximum_cos),
        "one_half_minus_maximum_cosHiNLag": str(F(1, 2) - maximum_cos),
        "maximum_sine_increment_defect": str(maximum_sine_increment_defect),
        "R2_over_4_minus_mu": str(coefficient),
        "maximum_bound_defect": str(maximum_bound_defect),
        "minimum_pair_drop": str(minimum_pair_drop),
        "adjacent_failures": adjacent_failures,
        "conclusion": "all bin-3 arithmetic obligations hold exactly",
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print("PASS: cosHiNLag <= 1/2 on nodes 768..1023")
    print("PASS: every sine increment <= (1/2) * q increment")
    print("PASS: R2/4 - mu < 0 and every pair satisfies the proof upper bound")
    print("PASS: all 32640 pairs strictly decrease; zero adjacent failures")
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
