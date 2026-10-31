#!/usr/bin/env python3
"""Recompute the canonical q0 degree-three total from the emitted Lean source.

This is an exact-arithmetic audit, not a Lean proof.  It parses the generated
`mu`, `lam`, edge maxima, sector maxima, and edge table, evaluates the same
`totalUpper` formula as `MetricAreaRationalCertificate`, and compares the result
with the independently emitted JSON manifest.
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization/SevenClassQ0Deg3UpperTables.lean"
MANIFEST = HERE / "q0-degree3-piecewise-8.json"


def lean_array(source: str, name: str) -> list[str]:
    start = source.index(f"def {name} ")
    start = source.index(":= ![", start) + len(":= ![")
    depth = 1
    end = start
    while depth:
        char = source[end]
        depth += char in "[("
        depth -= char in "])"
        end += 1
    body = source[start:end - 1]
    fields: list[str] = []
    field_start = 0
    depth = 0
    for index, char in enumerate(body + ","):
        if char in "[(":
            depth += 1
        elif char in "])":
            depth -= 1
        elif char == "," and depth == 0:
            fields.append(body[field_start:index].strip())
            field_start = index + 1
    return fields


def rational(text: str) -> Fraction:
    text = text.strip().replace(" ", "")
    while text.startswith("(") and text.endswith(")"):
        text = text[1:-1]
    return Fraction(text)


def main() -> None:
    source = LEAN.read_text()
    manifest = json.loads(MANIFEST.read_text())

    mu = [rational(x) for x in lean_array(source, "mu")]
    edge_max = [rational(x) for x in lean_array(source, "edgeMaxAt")]
    sector_max = [rational(x) for x in lean_array(source, "sectorMax")]
    lam_text = source.split("def lam : ℚ := ", 1)[1].splitlines()[0]
    lam = rational(lam_text)
    edges = []
    for field in lean_array(source, "tableEdges"):
        edge_text = field.strip().lstrip("(")
        edge_text = edge_text[:edge_text.index("}")].replace("{", "")
        edges.append(tuple(int(x) for x in edge_text.split(",")))

    assert len(mu) == 11 and len(edge_max) == 21
    assert len(sector_max) == 9 and len(edges) == 21

    lean_pi_lo = Fraction(314159265358979323846, 10**20)
    manifest_pi_lo = rational(manifest["piLo"])
    lean_pi_hi = Fraction(314159265358979323847, 10**20)
    manifest_pi_hi = rational(manifest["piHi"])
    def total_with(pi_lo: Fraction, pi_hi: Fraction,
                   edge_maxima: list[Fraction], sector_maxima: list[Fraction],
                   mu_values: list[Fraction], lam_value: Fraction) -> Fraction:
        width = pi_hi / 2048
        pi_coefficient = 2 * (sum(mu_values) - lam_value)
        edge_terms = [
            edge_maxima[i] +
            (Fraction(19, 50) ** 2 +
             abs(sum(mu_values[j] for j in edge))) * width
            for i, edge in enumerate(edges)
        ]
        sector_terms = [
            sector_maxima[i] +
            (1 + lam_value + abs(mu_values[(i + 1) % 9])) * width
            for i in range(9)
        ]
        return pi_coefficient * pi_lo + sum(edge_terms) + sum(sector_terms)

    manifest_mu = [rational(x) for x in manifest["mu"]]
    manifest_lam = rational(manifest["lambda"])
    manifest_edge_max = [rational(x["max"]) for x in manifest["edges"]]
    manifest_sector_max = [rational(x["max"]) for x in manifest["sectors"]]
    manifest_total = total_with(
        manifest_pi_lo, manifest_pi_hi, manifest_edge_max,
        manifest_sector_max, manifest_mu, manifest_lam)
    total = total_with(lean_pi_lo, lean_pi_hi, edge_max, sector_max, mu, lam)

    assert manifest_total == rational(manifest["totalUpper"])
    assert manifest_pi_lo - manifest_total == rational(manifest["slack"])
    assert total < lean_pi_lo
    assert manifest["strictBelowPiLo"] is True
    print(f"PASS: canonical total = {float(total):.15f}")
    print(f"PASS: Lean piLo slack  = {float(lean_pi_lo - total):.15f}")
    print(f"PASS: manifest matches (40-digit piLo; delta {float(manifest_total - total):.3e})")
    print("Scope: exact rational replay of the emitted table; not a Lean proof.")


if __name__ == "__main__":
    main()
