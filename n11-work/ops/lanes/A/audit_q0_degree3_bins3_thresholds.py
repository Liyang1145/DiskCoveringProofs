#!/usr/bin/env python3
"""Exact threshold audit for the all-row bin-3 sector proof."""
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

OUT = HERE / "q0-degree3-bins3-thresholds-audit.json"
SHAPE = HERE / "q0-degree3-sector-bins-audit.json"


def cosTQ(n: int, q: F) -> F:
    return sum((F(-1) ** k) * q ** (2 * k) / math.factorial(2 * k)
               for k in range(n + 1))


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def main() -> None:
    raw, row = probe.load()
    mu = [probe.mid(x) for x in row["mu"]]
    _, upper = probe.interval(row["pi_interval"])
    q = {k: upper * k / probe.N for k in (768, 1023)}
    c = {k: cosTQ(14, q[k]) for k in q}
    threshold = [2 * m / F(19, 50) ** 2 for m in mu]
    shape = json.loads(SHAPE.read_text())

    require(len(threshold) >= 9, "sector-row table is too short")
    require(all(c[768] <= threshold[i] for i in range(2)),
            "node-768 decreasing threshold failed for rows 0--1")
    require(all(threshold[i] < c[1023] for i in range(2, 9)),
            "node-1023 increasing threshold failed for rows 2--8")
    for i in range(9):
        expected = 768 if i <= 1 else 1023
        require(shape["rows"][i]["bins"][3]["argmaxK"] == expected,
                f"row {i}: bin-3 argmax mismatch")

    result = {
        "scope": "exact-rational threshold audit only; no Lean kernel claim",
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "shape_sha256": hashlib.sha256(SHAPE.read_bytes()).hexdigest(),
        "nodeQ": {str(k): str(v) for k, v in q.items()},
        "cosTQ14": {str(k): str(v) for k, v in c.items()},
        "rows_0_1_node768_margins": [
            str(threshold[i] - c[768]) for i in range(2)
        ],
        "rows_2_8_node1023_margins": [
            str(c[1023] - threshold[i]) for i in range(2, 9)
        ],
        "checks": 2 + 7 + 9,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: 2/2 node-768 decreasing crossings")
    print("PASS: 7/7 node-1023 increasing prefixes")
    print("PASS: 9/9 bin-3 argmax patterns")
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
