#!/usr/bin/env python3
"""Exact audit of the eight-bin sector shapes.

This records why the global adjacent-step premise in
`SevenClassQ0Deg3SectorShape` is false: the node table jumps at bin
boundaries, so a row can fall inside a bin and rise at the next boundary.
The report instead gives a single exact grid argmax for every bin.
"""
from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import probe_q0_degree3_nodes as probe  # noqa: E402

REPORT = HERE / "q0-degree3-piecewise-8.json"
OUT = HERE / "q0-degree3-sector-bins-audit.json"


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def bin_range(j: int) -> range:
    return range(256 * j, 2049 if j == 7 else 256 * j + 256)


def main() -> None:
    raw, row = probe.load()
    report = json.loads(REPORT.read_text())
    require(report["source_sha256"] == hashlib.sha256(raw).hexdigest(),
            "source hash mismatch")

    mu = [probe.mid(x) for x in row["mu"]]
    lam = probe.mid(row["lambda"])
    _, U = probe.interval(row["pi_interval"])
    bins = [F(item["node"]) for item in report["bins"]]
    qs = [U * k / probe.N for k in range(probe.N + 1)]
    sh = [probe.sinHi(q) for q in qs]

    base = []
    for k, (q, s) in enumerate(zip(qs, sh)):
        a = bins[min(7, 8 * k // probe.N)]
        base.append(probe.R2 * s / 2 + (2 * a - probe.sinLo(2 * a)) / 2 +
                    2 * lam * a)

    rows = []
    for i, expected in enumerate(report["sectors"]):
        values = [base[k] - mu[i] * qs[k] for k in range(probe.N + 1)]
        witness = expected["witnessK"]
        false_inc = [k for k in range(witness) if values[k] > values[k + 1]]
        false_dec = [k for k in range(witness, probe.N) if values[k + 1] > values[k]]
        require(false_inc and false_dec, f"sector {i}: expected shape failure missing")

        bin_rows = []
        for j in range(8):
            ks = bin_range(j)
            signs = []
            for k in range(ks.start, ks.stop - 1):
                delta = values[k + 1] - values[k]
                require(delta != 0, f"sector {i} bin {j}: zero adjacent step")
                signs.append(1 if delta > 0 else -1)
            require(all(signs[k] >= signs[k + 1] for k in range(len(signs) - 1)),
                    f"sector {i} bin {j}: not increase-then-decrease")
            local_max_k = max(ks, key=lambda k: values[k])
            require(values[local_max_k] == max(values[k] for k in ks),
                    f"sector {i} bin {j}: argmax mismatch")
            bin_rows.append({
                "bin": j,
                "start": ks.start,
                "last": ks.stop - 1,
                "inc_last": ks.start + signs.count(1),
                "argmaxK": local_max_k,
                "max": str(values[local_max_k]),
            })
        rows.append({
            "site": i,
            "globalWitnessK": witness,
            "falseGlobalIncSteps": len(false_inc),
            "firstFalseGlobalInc": false_inc[0],
            "falseGlobalDecSteps": len(false_dec),
            "firstFalseGlobalDec": false_dec[0],
            "bins": bin_rows,
        })

    result = {
        "scope": "exact-rational finite-grid audit only; no Lean claim",
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "report_sha256": hashlib.sha256(REPORT.read_bytes()).hexdigest(),
        "rows": rows,
        "conclusion": (
            "SectorIncSteps/SectorDecSteps as stated in SectorShape are false. "
            "Each of the 72 row-bin restrictions is monotone increasing then "
            "decreasing, with the exact grid argmax recorded above."
        ),
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: 9/9 global adjacent-step counterexamples reproduced")
    print("PASS: 72/72 row-bin restrictions are single-peaked")
    print("first false global inc step:", rows[0]["firstFalseGlobalInc"])
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
