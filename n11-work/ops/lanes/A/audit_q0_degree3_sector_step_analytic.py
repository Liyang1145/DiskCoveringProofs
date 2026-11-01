#!/usr/bin/env python3
"""Exact-rational feasibility check for a coarse row-0 sector-step proof.

The direct kernel comparison of the two evaluated sector values involves a
1237-digit numerator.  This audit checks the alternative proof route:

    sin(q2) - sin(q1) <= (q2 - q1) / 2
    sinHiNLag(q2) - sinHiNLag(q1) <= (q2 - q1) / 2 + 1/10^6

on the specific interval q1 < q2 near pi/2.  The cosine bound follows from
3*midpoint(q1,q2) > piHi > pi and monotonicity of cosine.  This is source-level
arithmetic evidence for a future Lean proof, not kernel credit.
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
import emit_q0_degree3_sector_step_counterexample as step
import probe_q0_degree3_nodes as probe

AUDIT = HERE / "q0-degree3-sector-steps-audit.json"
OUT = HERE / "q0-degree3-sector-step-analytic-audit.json"


def main() -> None:
    _, row = probe.load()
    pi_lo, pi_hi = probe.interval(row["pi_interval"])
    mu = [probe.mid(x) for x in row["mu"]]
    values = step.sector_values()

    q1 = pi_hi * 1022 / probe.N
    q2 = pi_hi * 1023 / probe.N
    half_step = (q2 - q1) / 2
    midpoint = (q1 + q2) / 2
    remainder_bound = F(1, 10**6)
    r2 = probe.R2
    mu1 = mu[1]

    assert q1 < q2
    assert values[1023] < values[1022]
    assert 3 * midpoint > pi_hi, "midpoint/pi monotonicity interval not justified"
    assert pi_hi < 22 / 7, "piHi is outside the expected coarse bound"
    assert 2 * F(2**29, factorial(29)) < remainder_bound
    assert q2 <= 2, "Taylor remainder bound assumes |q2| <= 2"

    margin = mu1 * (q2 - q1) - (r2 / 2) * (half_step + remainder_bound)
    assert margin > 0, "coarse analytic bound does not separate the step"

    audit = json.loads(AUDIT.read_text())
    audited = next(r for r in audit["rows"] if r["site"] == 0)
    exact_drop = values[1022] - values[1023]
    assert exact_drop == F(audited["largestIncDrop"])

    report = {
        "scope": "exact-rational feasibility of a small-denominator analytic proof; no Lean claim",
        "indices": [1022, 1023],
        "q1": str(q1),
        "q2": str(q2),
        "q_step": str(q2 - q1),
        "three_midpoint_minus_piHi": str(3 * midpoint - pi_hi),
        "cos_bound": "cos(midpoint) <= 1/2 because pi/3 <= midpoint <= pi",
        "sinHi_step_bound": "(q2-q1)/2 + 1/10^6",
        "two_taylor_remainder_bound": str(remainder_bound),
        "separation_margin": str(margin),
        "exact_drop": str(exact_drop),
        "audit_sha256": hashlib.sha256(AUDIT.read_bytes()).hexdigest(),
        "conclusion": "coarse analytic bounds leave a positive exact separation margin",
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print("PASS: 3*midpoint > piHi > pi, hence cos midpoint <= 1/2")
    print("PASS: sine step <= q_step/2 + 1e-6")
    print("PASS: separation margin is positive")
    print("margin numerator digits:", len(str(margin.numerator)))
    print("wrote", OUT.relative_to(HERE.parents[3]),
          "sha256", hashlib.sha256(OUT.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
