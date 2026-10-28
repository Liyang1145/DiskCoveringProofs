#!/usr/bin/env python3
"""Static audit of the q0(3,10) interval area certificate.

This verifies the source record and its graph convention with exact decimal
Fractions. It emits data for a future Lean emitter; it proves no Lean theorem.
"""
from __future__ import annotations
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
SRC = ROOT / "cover11/proof_bundle/research-2026/team-current/lead/degree3_area_certificate.json"
OUT = Path(__file__).with_name("q0-degree3-area-audit.json")


def interval(text: str) -> tuple[Fraction, Fraction]:
    lo, hi = text.strip()[1:-1].split(",")
    return Fraction(lo), Fraction(hi)


def main() -> None:
    raw = SRC.read_bytes()
    data = json.loads(raw)
    assert data["N"] == 2048
    q0 = [r for r in data["results"] if r["q"] == 0]
    assert len(q0) == 1 and len(data["results"]) == 9
    row = q0[0]
    assert row["small_hub_edge"] == [0, 1] and row["strict_less_pi"] is True
    assert len(row["mu"]) == 11
    ulo, uhi = interval(row["upper_interval"])
    plo, phi = interval(row["pi_interval"])
    assert uhi < plo
    assert ulo <= uhi and plo <= phi
    (llo, lhi), = [interval(row["lambda"])]
    assert llo <= lhi
    mus = [interval(x) for x in row["mu"]]
    assert all(a <= b for a, b in mus)

    edges = {(i, (i + 1) % 9) for i in range(9)}
    edges |= {(9, 0), (9, 1), (9, 10)}
    edges |= {(10, i) for i in range(9)}
    assert len(edges) == 21
    degree = {i: 0 for i in range(11)}
    for a, b in edges:
        degree[a] += 1
        degree[b] += 1
    assert (degree[9], degree[10]) == (3, 10)
    assert sum(degree.values()) == 42

    report = {
        "scope": "source q0 degree-three interval certificate and finite graph only; no Lean claim",
        "source": str(SRC.relative_to(ROOT)),
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "grid_N": data["N"],
        "q0_case_count": len(q0),
        "small_hub_edge": row["small_hub_edge"],
        "upper_interval": [str(ulo), str(uhi)],
        "pi_interval": [str(plo), str(phi)],
        "upper_below_pi": True,
        "mu_intervals": [[str(a), str(b)] for a, b in mus],
        "lambda_interval": [str(llo), str(lhi)],
        "edge_count": len(edges),
        "edges": sorted([list(e) for e in edges]),
        "hub_degrees": {"9": degree[9], "10": degree[10]},
        "edge_degree_sum": sum(degree.values()),
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("PASS: one q0 case, 11 mu intervals, lambda interval, upper < pi")
    print("PASS: canonical graph has 21 edges and hub degrees 3/10")
    print(f"wrote {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
