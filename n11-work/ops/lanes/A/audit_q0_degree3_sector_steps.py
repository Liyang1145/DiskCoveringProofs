#!/usr/bin/env python3
"""Exact-rational counterexamples to the global sector adjacent-step premise.

`SectorIncSteps`/`SectorDecSteps` are false for every sector row.  The maxima
remain correct, but each row has interior dips before its listed witness and
small rises after it at bin boundaries.  This is arithmetic evidence only.
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
OUT = HERE / "q0-degree3-sector-steps-audit.json"


def main() -> None:
    raw, row = probe.load()
    report = json.loads(REPORT.read_text())
    assert report["source_sha256"] == hashlib.sha256(raw).hexdigest()
    mu = [probe.mid(x) for x in row["mu"]]
    lam = probe.mid(row["lambda"])
    _, upper = probe.interval(row["pi_interval"])
    qs = [upper * k / probe.N for k in range(probe.N + 1)]
    sines = [probe.sinHi(q) for q in qs]
    node8 = [F(item["node"]) for item in report["bins"]]
    nodes = [node8[min(7, 8 * k // probe.N)] for k in range(probe.N + 1)]
    segment = [(2 * a - probe.sinLo(2 * a)) / 2 for a in node8]

    rows = []
    for expected in report["sectors"]:
        i, witness = expected["site"], expected["witnessK"]
        values = [segment[min(7, 8 * k // probe.N)] +
                  probe.R2 * sines[k] / 2 + 2 * lam * nodes[k] - mu[i] * qs[k]
                  for k in range(probe.N + 1)]
        assert max(values) == F(expected["max"]) and values[witness] == max(values)
        inc = [k for k in range(witness) if values[k + 1] < values[k]]
        dec = [k for k in range(witness, probe.N) if values[k] < values[k + 1]]
        assert inc and dec, f"sector {i}: expected counterexamples missing"
        k = inc[0]
        rows.append({
            "site": i,
            "witnessK": witness,
            "incFailures": len(inc),
            "decFailures": len(dec),
            "firstIncFailureK": k,
            "firstIncDelta": str(values[k + 1] - values[k]),
        })

    result = {
        "scope": "exact-rational refutation only; no Lean claim",
        "report_sha256": hashlib.sha256(REPORT.read_bytes()).hexdigest(),
        "sectorCount": len(rows),
        "rows": rows,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: all nine exact maxima reproduce")
    print("PASS: every row refutes both global adjacent-step premises")
    print("first increasing-step counterexamples:",
          [(row["site"], row["firstIncFailureK"]) for row in rows])
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
