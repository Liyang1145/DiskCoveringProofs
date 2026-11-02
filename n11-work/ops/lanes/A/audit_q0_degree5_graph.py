#!/usr/bin/env python3
"""Audit the q0(5,8) source graph/coefficient layout against Lean.

This is a source-graph and layout check only.  It does not emit Lean proof
terms, check a factor bound, or claim a kernel result.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from extract_finite_class_tables import (  # noqa: E402
    LEAD, LEAN, ROOT, all_pairs, canonical, lean_q0_faces, require, sha256,
)

OUT = HERE / "q0-degree5-graph-match.json"


def check() -> dict:
    graph_path = LEAD / "q0_closure_dual_0_3.json"
    cert_path = LEAD / "q0_closure_dual_certificate_0_3.json"
    graph = json.loads(graph_path.read_text())
    cert = json.loads(cert_path.read_text())

    require(graph.get("start") == 0 and graph.get("span") == 3,
            "closure graph is not q0(start=0,span=3)")
    require(cert.get("start") == 0 and cert.get("span") == 3 and cert.get("strict") is True,
            "closure certificate header drifted")

    expected_faces = lean_q0_faces(3)
    source_faces = sorted(canonical(face) for face in graph["faces"])
    require(len(source_faces) == 11, "source face count is not 11")
    require(source_faces == expected_faces,
            f"q0(5,8) labelled face mismatch: source={source_faces}, lean={expected_faces}")

    source_edges = sorted(tuple(sorted(edge)) for edge in graph["edges"])
    expected_edges = sorted({edge for face in expected_faces for edge in all_pairs(face)})
    require(len(source_edges) == 21, "source edge count is not 21")
    require(source_edges == expected_edges,
            f"q0(5,8) labelled edge mismatch: source={source_edges}, lean={expected_edges}")
    require(all(a < b for a, b in source_edges), "source edges are not canonically oriented")
    require(len(set(source_edges)) == 21, "source edges contain duplicates")

    coefficients = cert["coefficients"]
    z = graph["z"]
    require(len(coefficients) == 121, f"coefficient count {len(coefficients)} != 121")
    require(len(z) == 121, f"z-slot count {len(z)} != 121")
    require(all(isinstance(c, str) for c in coefficients),
            "coefficient rows are not decimal strings")
    require(all(isinstance(v, (int, float)) for v in z), "z rows are not numeric")
    exact_coefficients = all(isinstance(c, list) and len(c) == 2 for c in coefficients)

    factor_names = [record["factor"] for record in cert["factors"]]
    expected_names = ([f"face{i}" for i in range(11)] +
                      [f"switch{i}" for i in range(9)] +
                      [f"ring{i}" for i in range(9)])
    require(factor_names == expected_names, "factor labels/order do not match 11+9+9 layout")

    lean_file = LEAN / "ActualOrderedMetricGraphs.lean"
    text = lean_file.read_text()
    for fragment in (
        "def q0Fan (m i : Fin 9) : Finset (Fin 11) :=",
        "{ringSite i,nextSite i,if i.val < m.val then 9 else 10}",
        "Finset.univ.image (q0Fan m) ∪ {centralFace 0,centralFace m}",
    ):
        require(fragment in text, f"Lean q0 graph definition drifted: {fragment}")

    return {
        "status": "PASS_GRAPH_AND_LAYOUT_FLOATS_ONLY",
        "claim_boundary": "No Lean kernel check, factor bound, balance proof, or exclusion proved.",
        "class": "q0_degree5",
        "start": 0,
        "span": 3,
        "source_graph": graph_path.relative_to(ROOT).as_posix(),
        "source_graph_sha256": sha256(graph_path),
        "source_certificate": cert_path.relative_to(ROOT).as_posix(),
        "source_certificate_sha256": sha256(cert_path),
        "lean_graph_source": lean_file.relative_to(ROOT).as_posix(),
        "lean_graph_source_sha256": sha256(lean_file),
        "faces": [list(face) for face in expected_faces],
        "face_count": len(expected_faces),
        "edge_count": len(expected_edges),
        "coefficient_count": len(coefficients),
        "z_slot_count": len(z),
        "factor_count": len(factor_names),
        "factor_layout": {"face": 11, "switch": 9, "ring": 9},
        "coefficient_encoding": "exact rational pairs" if exact_coefficients
            else "decimal strings; exact rational certificates must be regenerated from the source emitter",
        "z_encoding": "decimal floats",
    }


def main() -> None:
    report = check()
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS q0(5,8): {report['face_count']} faces, {report['edge_count']} edges, "
          f"{report['coefficient_count']} coefficients, {report['factor_count']} factors")
    print(f"wrote {OUT.relative_to(ROOT)} sha256={sha256(OUT)}")


if __name__ == "__main__":
    main()
