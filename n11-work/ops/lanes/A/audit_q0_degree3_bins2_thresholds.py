#!/usr/bin/env python3
"""Exact threshold audit for the all-row bin-2 sector proof."""
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

OUT = HERE / "q0-degree3-bins2-thresholds-audit.json"


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
    q = {k: upper * k / probe.N for k in (543, 544, 767)}
    c = {k: cosTQ(14, q[k]) for k in q}
    threshold = [2 * m / F(19, 50) ** 2 for m in mu]

    require(len(threshold) >= 9, "sector-row table is too short")
    require(all(threshold[i] < c[543] for i in range(9)),
            "node-543 prefix threshold failed")
    require(all(c[544] <= threshold[i] for i in range(2)),
            "node-544 decreasing threshold failed for rows 0--1")
    require(all(threshold[i] < c[767] for i in range(2, 9)),
            "node-767 increasing threshold failed for rows 2--8")
    require(all(threshold[i] >= F(-2, 3) for i in range(2)),
            "negative-tail threshold failed for rows 0--1")

    result = {
        "scope": "exact-rational threshold audit only; no Lean kernel claim",
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "nodeQ": {str(k): str(v) for k, v in q.items()},
        "cosTQ14": {str(k): str(v) for k, v in c.items()},
        "rows_0_1_node544_margins": [str(threshold[i] - c[544]) for i in range(2)],
        "rows_2_8_node767_margins": [str(c[767] - threshold[i]) for i in range(2, 9)],
        "checks": 9 + 2 + 7 + 2,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: 9/9 node-543 prefixes")
    print("PASS: 2/2 sharp node-544 decreases")
    print("PASS: 7/7 endpoint node-767 increases")
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
