#!/usr/bin/env python3
"""Exact threshold audit for the all-row bin-6 and bin-7 sector proofs."""
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

OUT = HERE / "q0-degree3-bins67-thresholds-audit.json"
SHAPE = HERE / "q0-degree3-sector-bins-audit.json"
BINS = ((6, 1536), (7, 1792))


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
    threshold = [2 * m / F(19, 50) ** 2 for m in mu]
    shape = json.loads(SHAPE.read_text())
    records = []

    require(len(threshold) >= 9, "sector-row table is too short")
    for bin_index, node in BINS:
        q = upper * node / probe.N
        require(all(cosHiNLag(q) <= threshold[i] for i in range(9)),
                f"node-{node} decreasing threshold failed")
        require(all(F(-2, 3) <= threshold[i] for i in range(9)),
                f"bin-{bin_index} tail bound failed")
        witnesses = [shape["rows"][i]["bins"][bin_index]["argmaxK"]
                     for i in range(9)]
        require(all(witnesses[i] == node for i in range(9)),
                f"bin-{bin_index} argmax mismatch")
        records.append({
            "bin": bin_index,
            "node": node,
            "nodeQ": str(q),
            "witness": witnesses,
            "margins": [str(threshold[i] - cosHiNLag(q)) for i in range(9)],
        })

    result = {
        "scope": "exact-rational threshold audit only; no Lean kernel claim",
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "shape_sha256": hashlib.sha256(SHAPE.read_bytes()).hexdigest(),
        "records": records,
        "checks": 3 * 2 * 9,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: 18/18 node-1536/1792 decreasing crossings")
    print("PASS: 18/18 -2/3 tail-cutoff comparisons")
    print("PASS: 18/18 bin-6/7 argmax patterns")
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
