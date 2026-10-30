#!/usr/bin/env python3
"""Exact audit of the degree-28 cosine tail relevant to edges 9 and 10."""

import hashlib
import json
from fractions import Fraction
from math import factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent
THRESHOLD_JSON = HERE / "q0-degree3-suffix-threshold.json"
PI_HI = Fraction(314159265358979323847, 10**20)
GRID_N = 2048
NODE = 1490
WITNESS = 1489
BOUND = Fraction(-131, 200)
A = Fraction(19, 50) ** 2


def cos_hi_lag(q: Fraction) -> Fraction:
    cos_t14 = sum((-1) ** k * q ** (2 * k) / factorial(2 * k) for k in range(15))
    return cos_t14 + q**28 / factorial(28)


def sin_hi_lag(q: Fraction) -> Fraction:
    sin_t14 = sum((-1) ** k * q ** (2 * k + 1) / factorial(2 * k + 1)
                  for k in range(15))
    return sin_t14 + abs(q) ** 29 / factorial(29)


def edge_upper(b: Fraction, node: int) -> Fraction:
    q = PI_HI * node / GRID_N
    return A * sin_hi_lag(q) - b * q


def main() -> None:
    q = PI_HI * NODE / GRID_N
    value = cos_hi_lag(q)
    data = json.loads(THRESHOLD_JSON.read_text())
    ratios = [Fraction(data["coefficients"][i]) / A for i in (9, 10)]
    steps = {
        i: edge_upper(Fraction(data["coefficients"][i]), NODE)
           - edge_upper(Fraction(data["coefficients"][i]), WITNESS)
        for i in (9, 10)
    }
    checks = {
        "node_1490_above_2": q > 2,
        "cos_hi_node_1490_le_neg_131_over_200": value <= BOUND,
        "neg_131_over_200_le_edge_9_ratio": BOUND <= ratios[0],
        "neg_131_over_200_le_edge_10_ratio": BOUND <= ratios[1],
        "cos_hi_node_1490_le_neg_2_over_3": value <= Fraction(-2, 3),
        "edge_9_step_1490_le_1489": steps[9] <= 0,
        "edge_10_step_1490_le_1489": steps[10] <= 0,
    }
    report = {
        "scope": "exact rational arithmetic only; not a Lean proof",
        "source": THRESHOLD_JSON.name,
        "source_sha256": hashlib.sha256(THRESHOLD_JSON.read_bytes()).hexdigest(),
        "node": NODE,
        "q_1490": str(q),
        "cos_hi_lag_q_1490": str(value),
        "cos_hi_lag_q_1490_float": float(value),
        "bound": str(BOUND),
        "edge_9_ratio": str(ratios[0]),
        "edge_10_ratio": str(ratios[1]),
        "edge_9_step_1490_minus_1489": str(steps[9]),
        "edge_10_step_1490_minus_1489": str(steps[10]),
        "checks": checks,
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    assert checks["node_1490_above_2"]
    assert checks["cos_hi_node_1490_le_neg_131_over_200"]
    assert checks["neg_131_over_200_le_edge_9_ratio"]
    assert checks["neg_131_over_200_le_edge_10_ratio"]
    assert not checks["cos_hi_node_1490_le_neg_2_over_3"]
    assert checks["edge_9_step_1490_le_1489"]
    assert checks["edge_10_step_1490_le_1489"]


if __name__ == "__main__":
    main()
