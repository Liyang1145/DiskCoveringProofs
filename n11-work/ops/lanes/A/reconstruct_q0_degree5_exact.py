#!/usr/bin/env python3
"""Reconstruct the q0(5,8) dual source in exact decimal rational form.

The committed SciPy emitter `q0_closure_dual.py` serialises its LP vector `z`
as JSON decimal floats.  This wrapper parses those decimals exactly (rather
than converting through binary floats), checks the emitter's field layout and
the certificate's rounded coefficient copy, and writes rational pairs suitable
for a later Lean table.  It does not prove a factor bound or exclusion.
"""
from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from extract_finite_class_tables import (  # noqa: E402
    LEAD, ROOT, all_pairs, canonical, lean_q0_faces, require, sha256,
)

OUT = HERE / "q0-degree5-exact-source.json"
GRAPH = LEAD / "q0_closure_dual_0_3.json"
CERT = LEAD / "q0_closure_dual_certificate_0_3.json"
PRIMARY = LEAD / "q0_closure_dual.py"


def load_exact(path: Path) -> dict:
    return json.loads(path.read_text(), parse_float=Fraction, parse_int=Fraction)


def pair(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def check() -> dict:
    graph = load_exact(GRAPH)
    cert = load_exact(CERT)
    require(graph.get("start") == 0 and graph.get("span") == 3,
            "source row is not q0(start=0,span=3)")
    require(cert.get("start") == 0 and cert.get("span") == 3 and cert.get("strict") is True,
            "certificate header drifted")

    expected_faces = lean_q0_faces(3)
    source_faces = sorted(canonical(face) for face in graph["faces"])
    require(source_faces == expected_faces,
            "source face order/labels do not match Lean q0Faces 3")
    expected_edges = sorted({edge for face in expected_faces for edge in all_pairs(face)})
    source_edges = [tuple(edge) for edge in graph["edges"]]
    require(source_edges == expected_edges and all(a < b for a, b in source_edges),
            "source edges are not the canonical sorted Lean q0 edge list")

    z = graph["z"]
    require(len(z) == 121, f"source z has {len(z)} entries, not 121")
    require(all(isinstance(v, Fraction) for v in z), "source z decimal was not parsed exactly")
    groups = {
        "mu": (0, 9),
        "hub": (9, 2),
        "side": (11, 21),
        "radius": (32, 18),
        "angle_slack": (50, 21),
        "lambda": (71, 1),
        "eta": (72, 1),
        "linear": (73, 39),
        "closure": (112, 9),
    }
    for name, (start, size) in groups.items():
        require(start + size <= len(z), f"group {name} exceeds z")
    require(groups["closure"][0] + groups["closure"][1] == len(z), "group layout is not contiguous")
    first = sum(size for _, size in groups.values())
    require(first == 121, f"group sizes sum to {first}, not 121")
    require(all(v >= 0 for v in z[50:71]), "angle-slack multipliers must be nonnegative")
    require(z[72] == 0, "eta must be zero")

    cert_coeffs = [Fraction(v) for v in cert["coefficients"]]
    serialized = [Fraction(f"{float(v):.9f}") for v in z]
    require(len(cert_coeffs) == len(serialized) == 121, "certificate coefficient count drifted")
    require(cert_coeffs == serialized,
            "certificate coefficient field order/rounding does not match emitter z")

    return {
        "status": "PASS_EXACT_DECIMAL_SOURCE_RECONSTRUCTION",
        "claim_boundary": "No factor bound, strict total, exclusion, or Lean kernel check.",
        "class": "q0_degree5",
        "start": 0,
        "span": 3,
        "source_graph": GRAPH.relative_to(ROOT).as_posix(),
        "source_graph_sha256": sha256(GRAPH),
        "source_certificate": CERT.relative_to(ROOT).as_posix(),
        "source_certificate_sha256": sha256(CERT),
        "source_emitter": PRIMARY.relative_to(ROOT).as_posix(),
        "source_emitter_sha256": sha256(PRIMARY),
        "lean_graph_faces": [list(face) for face in expected_faces],
        "lean_graph_edges": [list(edge) for edge in expected_edges],
        "field_groups": {name: {"start": start, "size": size}
                         for name, (start, size) in groups.items()},
        "coefficient_count": len(z),
        "nonnegative_angle_slack_count": sum(v >= 0 for v in z[50:71]),
        "eta": pair(z[72]),
        "coefficients": [pair(v) for v in z],
        "encoding": "exact JSON decimal rationals, numerator/denominator",
    }


def main() -> None:
    report = check()
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS q0(5,8): {report['coefficient_count']} exact coefficients, "
          f"{len(report['lean_graph_faces'])} faces, {len(report['lean_graph_edges'])} edges")
    print(f"wrote {OUT.relative_to(ROOT)} sha256={sha256(OUT)}")


if __name__ == "__main__":
    main()
