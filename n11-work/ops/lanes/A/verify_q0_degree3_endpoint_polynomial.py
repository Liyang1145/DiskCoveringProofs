#!/usr/bin/env python3
"""Exact checks for the lane-A degree-seven endpoint reduction.

This verifies the rational arithmetic behind
`SevenClassQ0Deg3EndpointChecks`: the polynomial sine lower bound must exceed
the polynomial cap upper bound at every bin endpoint.  It is candidate data,
not Lean kernel evidence.
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction as F
from math import factorial
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "q0-degree3-piecewise-8.json"
OUT = HERE / "q0-degree3-endpoint-poly.json"


def poly4(a: F) -> F:
    return a - a**3 / 6 + a**5 / 120 - a**7 / 5040


def main() -> None:
    data = json.loads(SRC.read_text())
    assert data["N"] == 2048 and len(data["bins"]) == 8
    pi_hi = F(data["piHi"])
    r9 = F(1, factorial(9))
    r29 = F(1, factorial(29))
    rows = []
    for j, bin_data in enumerate(data["bins"]):
        k = 2048 if j == 7 else 256 * j + 255
        q = pi_hi * k / 2048
        x = q / 2
        cap_upper = F(19, 50) * max(F(1, 2), min(F(1), poly4(x) + r9 + 2 * r29))
        node_lower = poly4(F(bin_data["node"])) - r9 - 2 * r29
        assert cap_upper <= node_lower, (j, cap_upper, node_lower)
        rows.append(
            {
                "bin": j,
                "k": k,
                "capUpper": str(cap_upper),
                "nodeLower": str(node_lower),
                "slack": str(node_lower - cap_upper),
            }
        )
    report = {
        "scope": "exact rational degree-seven endpoint bounds; candidate data, not kernel evidence",
        "source": SRC.name,
        "sourceSha256": hashlib.sha256(SRC.read_bytes()).hexdigest(),
        "minSlack": str(min(F(row["slack"]) for row in rows)),
        "bins": rows,
    }
    OUT.write_text(json.dumps(report, indent=1) + "\n")
    print("PASS: 8 endpoint polynomial comparisons; min slack", report["minSlack"])
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
