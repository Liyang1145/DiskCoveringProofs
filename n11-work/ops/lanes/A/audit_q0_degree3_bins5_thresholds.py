#!/usr/bin/env python3
"""Exact threshold audit for the all-row bin-5 sector proof."""
from __future__ import annotations

import hashlib
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import probe_q0_degree3_nodes as probe  # noqa: E402

OUT = HERE / "q0-degree3-bins5-thresholds-audit.json"
SHAPE = HERE / "q0-degree3-sector-bins-audit.json"
WITNESS = (1280,) * 9


def cosTQ(n: int, q: F) -> F:
    return sum((F(-1) ** k) * q ** (2 * k) / math.factorial(2 * k)
               for k in range(n + 1))


def cosHiNLag(q: F) -> F:
    return cosTQ(14, q) + abs(q) ** 28 / math.factorial(28)


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def main() -> None:
    raw, row = probe.load()
    mu = [probe.mid(x) for x in row["mu"]]
    _, upper = probe.interval(row["pi_interval"])
    q = upper * 1280 / probe.N
    threshold = [2 * m / F(19, 50) ** 2 for m in mu]
    shape = json.loads(SHAPE.read_text())

    require(len(threshold) >= 9, "sector-row table is too short")
    require(all(cosHiNLag(q) <= threshold[i] for i in range(9)),
            "node-1280 decreasing threshold failed")
    require(all(F(-2, 3) <= threshold[i] for i in range(9)),
            "bin-5 tail bound failed")
    for i in range(9):
        require(shape["rows"][i]["bins"][5]["argmaxK"] == WITNESS[i],
                f"row {i}: bin-5 argmax mismatch")

    result = {
        "scope": "exact-rational threshold audit only; no Lean kernel claim",
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "shape_sha256": hashlib.sha256(SHAPE.read_bytes()).hexdigest(),
        "witness": WITNESS,
        "nodeQ": str(q),
        "threshold": [str(x) for x in threshold],
        "margins": [str(threshold[i] - cosHiNLag(q)) for i in range(9)],
        "checks": 9 + 9 + 9,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: 9/9 node-1280 decreasing crossings")
    print("PASS: 9/9 -2/3 tail-cutoff comparisons")
    print("PASS: 9/9 bin-5 argmax patterns")
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
