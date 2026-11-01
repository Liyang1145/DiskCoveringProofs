#!/usr/bin/env python3
"""Audit the numerical side conditions in the row-0, bin-3 cosine proof.

This is exact-rational arithmetic evidence for the Lean source. It checks
the thresholds and Taylor-tail constants used by
`SevenClassQ0Deg3SectorBin3`, but does not replace a kernel check.
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
import probe_q0_degree3_nodes as probe

OUT = HERE / "q0-degree3-bin3-local-cos-audit.json"


def main() -> None:
    source = HERE.parents[2] / "lean/N11Formalization/SevenClassQ0Deg3SectorBin3.lean"
    _, row = probe.load()
    pi_lo, pi_hi = probe.interval(row["pi_interval"])
    mu1 = probe.mid(row["mu"][1])

    q768 = pi_hi * F(768, probe.N)
    q1023 = pi_hi * F(1023, probe.N)
    taylor = F(4**28, factorial(28))
    coefficient = F(19, 50) ** 2 / 4 - mu1

    assert pi_lo <= pi_hi
    assert q768 <= pi_hi / 2, "q768 is not in the monotone cosine half"
    assert q768 <= q1023 <= pi_hi, "bin-3 nodes leave the Taylor interval"
    # `hct` and the definition of `cosHiReal` each contribute one tail error.
    assert taylor <= F(1, 4), "the doubled degree-28 tail does not give 1/2"
    assert coefficient < 0, "the strict bin-3 coefficient is not negative"
    assert source.exists()

    report = {
        "scope": "exact-rational side conditions for row-0 bin-3; no Lean claim",
        "source": str(source.relative_to(HERE.parents[3])),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "pi_lo": str(pi_lo),
        "pi_hi": str(pi_hi),
        "q768": str(q768),
        "q1023": str(q1023),
        "pi_hi_over_2_minus_q768": str(pi_hi / 2 - q768),
        "four_pow_28_over_28_factorial": str(taylor),
        "one_quarter_minus_taylor": str(F(1, 4) - taylor),
        "A_squared_over_4_minus_mu_nextSite0": str(coefficient),
        "conclusion": "all scalar side conditions used by the bin-3 proof hold",
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print("PASS: q768 <= piHi/2")
    print("PASS: q768 <= q1023 <= piHi")
    print("PASS: 4^28/28! <= 1/4")
    print("PASS: (19/50)^2/4 - mu(nextSite 0) < 0")
    print("wrote", OUT.relative_to(HERE.parents[3]),
          "sha256", hashlib.sha256(OUT.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
