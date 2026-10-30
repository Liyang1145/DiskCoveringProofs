#!/usr/bin/env python3
"""Exact threshold audit for the all-row bin-4 sector proof."""
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

OUT = HERE / "q0-degree3-bins4-thresholds-audit.json"
SHAPE = HERE / "q0-degree3-sector-bins-audit.json"
WITNESS = (1024, 1024, 1173, 1051, 1076, 1070, 1076, 1051, 1173)


def cosTQ(n: int, q: F) -> F:
    return sum((F(-1) ** k) * q ** (2 * k) / math.factorial(2 * k)
               for k in range(n + 1))


def sinTQ(n: int, q: F) -> F:
    return sum((F(-1) ** k) * q ** (2 * k + 1) / math.factorial(2 * k + 1)
               for k in range(n + 1))


def cosHiNLag(q: F) -> F:
    return cosTQ(14, q) + abs(q) ** 28 / math.factorial(28)


def sinHiNLag(q: F) -> F:
    return sinTQ(14, q) + abs(q) ** 29 / math.factorial(29)


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def main() -> None:
    raw, row = probe.load()
    mu = [probe.mid(x) for x in row["mu"]]
    _, upper = probe.interval(row["pi_interval"])
    q = {k: upper * k / probe.N
         for k in set(WITNESS) | {1024} | {w - 1 for w in WITNESS if w >= 2}}
    qnext = {k + 1: upper * (k + 1) / probe.N for k in set(WITNESS) if k >= 2}
    threshold = [2 * m / F(19, 50) ** 2 for m in mu]
    shape = json.loads(SHAPE.read_text())

    require(len(threshold) >= 9, "sector-row table is too short")
    require(all(cosHiNLag(q[1024]) <= threshold[i] for i in range(2)),
            "node-1024 decreasing threshold failed for rows 0--1")
    require(all(threshold[i] < cosTQ(14, q[WITNESS[i] - 1]) for i in range(2, 9)),
            "witness-node increasing threshold failed for rows 2--8")
    require(all(cosHiNLag(qnext[WITNESS[i] + 1]) <= threshold[i]
                for i in range(2, 9)),
            "next-node decreasing threshold failed for rows 2--8")
    require(all(F(-2, 3) <= threshold[i] for i in range(2, 9)),
            "bin-4 tail bound failed for rows 2--8")
    for i in range(9):
        require(shape["rows"][i]["bins"][4]["argmaxK"] == WITNESS[i],
                f"row {i}: bin-4 argmax mismatch")

    result = {
        "scope": "exact-rational threshold audit only; no Lean kernel claim",
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "shape_sha256": hashlib.sha256(SHAPE.read_bytes()).hexdigest(),
        "witness": WITNESS,
        "nodeQ": {str(k): str(v) for k, v in sorted(q.items())},
        "nodeQNext": {str(k): str(v) for k, v in sorted(qnext.items())},
        "threshold": [str(x) for x in threshold],
        "rows_0_1_node1024_margins": [
            str(threshold[i] - cosHiNLag(q[1024])) for i in range(2)
        ],
        "rows_2_8_prev_margins": [
            str(cosTQ(14, q[WITNESS[i] - 1]) - threshold[i]) for i in range(2, 9)
        ],
        "rows_2_8_next_margins": [
            str(threshold[i] - cosHiNLag(qnext[WITNESS[i] + 1]))
            for i in range(2, 9)
        ],
        "checks": 2 + 7 + 7 + 7 + 9,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: 2/2 node-1024 decreasing crossings")
    print("PASS: 7/7 previous-node increasing prefixes")
    print("PASS: 7/7 next-node decreasing tails")
    print("PASS: 7/7 -2/3 tail-cutoff comparisons")
    print("PASS: 9/9 bin-4 argmax patterns")
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
