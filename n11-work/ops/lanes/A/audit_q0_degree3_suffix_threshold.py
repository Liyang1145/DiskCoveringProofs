#!/usr/bin/env python3
"""Exact classification of q0 degree-three edges covered by the high-coefficient
decreasing-suffix lemma.  This is finite candidate data, not a kernel proof."""

import json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "q0-degree3-piecewise-8.json"
OUT = HERE / "q0-degree3-suffix-threshold.json"
EDGES = (
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8),
    (8, 0), (9, 0), (9, 1), (9, 10), (10, 0), (10, 1), (10, 2),
    (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8),
)


def main():
    data = json.loads(DATA.read_text())
    mu = [Fraction(value) for value in data["mu"]]
    threshold = Fraction(19, 50) ** 2
    coeffs = [mu[a] + mu[b] for a, b in EDGES]
    covered = [i for i, value in enumerate(coeffs) if value > threshold]
    assert covered == [12, 13], covered
    report = {
        "scope": "exact rational classification of the high-coefficient suffix route",
        "source": str(DATA.name),
        "source_sha256": data["source_sha256"],
        "threshold": str(threshold),
        "covered_edges": covered,
        "coefficients": [str(value) for value in coeffs],
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print(f"exactly edges {covered} lie above {threshold}")
    for i in covered:
        print(f"edge {i}: {coeffs[i]}")


if __name__ == "__main__":
    main()
