#!/usr/bin/env python3
"""Independent exact-rational audit of every q0(3,10) sector grid value.

Recomputes the 21 edge maxima, all nine 2049-point sector maxima, and the
strict total from the source intervals and the eight-bin node table.  Sector
rows use the Lean pairing `mu (nextSite i) = mu ((i+1) mod 9)`.  This is
arithmetic evidence for the next Lean factorization, not a Lean proof.
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
OUT = HERE / "q0-degree3-sector-grid-audit.json"


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def main() -> None:
    raw, row = probe.load()
    report = json.loads(REPORT.read_text())
    require(report["source_sha256"] == hashlib.sha256(raw).hexdigest(),
            "source hash mismatch")
    require(report["N"] == probe.N and report["binCount"] == 8, "grid metadata")

    mu = [probe.mid(x) for x in row["mu"]]
    lam = probe.mid(row["lambda"])
    piLo, U = probe.interval(row["pi_interval"])
    require(lam >= 0, "negative lambda")
    qs = [U * k / probe.N for k in range(probe.N + 1)]
    sh = [probe.sinHi(q) for q in qs]
    width = F(U, probe.N)

    bins = report["bins"]
    node8 = [F(item["node"]) for item in bins]
    nodes = [node8[min(7, 8 * k // probe.N)] for k in range(probe.N + 1)]
    require(all(probe.sinLo(a) >= probe.capQ(q) for q, a in zip(qs, nodes)),
            "node table is not valid")

    edge_max = []
    for expected in report["edges"]:
        b = sum(mu[i] for i in expected["edge"])
        value = max(probe.R2 * s - b * q for s, q in zip(sh, qs))
        require(value == F(expected["max"]), f"edge {expected['edge']} max mismatch")
        edge_max.append(value)

    segment = [(2 * a - probe.sinLo(2 * a)) / 2 for a in node8]
    sector_max = []
    sector_witness = []
    for i in range(9):
        values = [segment[min(7, 8 * k // probe.N)] +
                  probe.R2 * sh[k] / 2 + 2 * lam * nodes[k] -
                  mu[(i + 1) % 9] * qs[k]
                  for k in range(probe.N + 1)]
        witness = max(range(probe.N + 1), key=values.__getitem__)
        value = values[witness]
        # The source report indexes rows by `mu i`; Lean uses `mu (i+1)`.
        expected = report["sectors"][(i + 1) % 9]
        require(value == F(expected["max"]), f"sector {i} max mismatch")
        sector_max.append(value)
        sector_witness.append(witness)

    total = 2 * (sum(mu) - lam) * piLo
    for expected, value in zip(report["edges"], edge_max):
        b = sum(mu[i] for i in expected["edge"])
        total += value + (probe.R2 + abs(b)) * width
    for i, value in enumerate(sector_max):
        total += value + (1 + lam + abs(mu[(i + 1) % 9])) * width

    require(total == F(report["totalUpper"]), "totalUpper mismatch")
    require(total < piLo, "totalUpper is not strict")
    print("PASS: 21 edge maxima reproduce")
    print("PASS: 9 x 2049 sector values reproduce all sector maxima")
    print("PASS: totalUpper reproduces and is strictly below piLo")
    print("sector witnesses:", sector_witness)
    result = {
        "scope": "exact-rational grid audit only; no Lean claim",
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "report_sha256": hashlib.sha256(REPORT.read_bytes()).hexdigest(),
        "edge_count": len(edge_max),
        "sector_count": len(sector_max),
        "sector_grid_points": len(sector_max) * (probe.N + 1),
        "sector_pairing": "mu (nextSite i) = mu ((i+1) mod 9)",
        "sector_site_to_mu_index": [(i + 1) % 9 for i in range(9)],
        "sector_witnessK": sector_witness,
        "totalUpper": str(total),
        "piLo": str(piLo),
        "strictBelowPiLo": total < piLo,
        "slack": str(piLo - total),
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print("slack:", float(piLo - total))
    print("wrote", OUT.name)


if __name__ == "__main__":
    main()
