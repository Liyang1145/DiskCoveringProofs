#!/usr/bin/env python3
"""Deterministic source-to-Lean graph audit for finite seven-class tables.

Only the q0(4,9) pilot is implemented.  This writes an inventory manifest; it
does not emit Lean proof terms or assert a kernel result.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
LEAD = ROOT / "cover11/proof_bundle/research-2026/team-current/lead"
LEAN = ROOT / "n11-work/lean/N11Formalization"
OUT = Path(__file__).resolve().with_name("q0-degree4-graph-match.json")


class AuditError(RuntimeError):
    pass


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AuditError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(face: list[int]) -> tuple[int, ...]:
    return tuple(sorted(face))


def lean_q0_faces(m: int) -> list[tuple[int, ...]]:
    """Reconstruct `q0Faces ⟨m, _⟩` from the definitions in the Lean source."""
    require(0 <= m < 9, f"fan split outside Fin 9: {m}")
    fans = [(i, (i + 1) % 9, 9 if i < m else 10) for i in range(9)]
    faces = fans + [(9, 10, 0), (9, 10, m)]
    return sorted(canonical(list(face)) for face in faces)


def all_pairs(face: tuple[int, ...]) -> set[tuple[int, int]]:
    return {(face[i], face[j]) for i in range(3) for j in range(i + 1, 3)}


def check_graph() -> dict:
    lean_file = LEAN / "ActualOrderedMetricGraphs.lean"
    text = lean_file.read_text()
    required_defs = (
        "def centralFace (i : Fin 9) : Finset (Fin 11) := {9,10,ringSite i}",
        "def q0Fan (m i : Fin 9) : Finset (Fin 11) :=",
        "{ringSite i,nextSite i,if i.val < m.val then 9 else 10}",
        "def q0Faces (m : Fin 9) : Finset (Finset (Fin 11)) :=",
        "Finset.univ.image (q0Fan m) ∪ {centralFace 0,centralFace m}",
    )
    for fragment in required_defs:
        require(fragment in text, f"Lean q0 graph definition drifted: {fragment}")

    raw_path = LEAD / "q0_moment_dual_0_2.json"
    raw = json.loads(raw_path.read_text())
    require(raw.get("start") == 0 and raw.get("span") == 2,
            "pilot source is not q0(start=0,span=2)")
    source_faces = [canonical(face) for face in raw["faces"]]
    expected_faces = lean_q0_faces(2)
    require(len(source_faces) == 11, "source face count is not 11")
    require(sorted(source_faces) == expected_faces,
            f"labelled face mismatch: source={sorted(source_faces)}, lean={expected_faces}")

    source_edges = [tuple(sorted(edge)) for edge in raw["edges"]]
    expected_edges = sorted({edge for face in expected_faces for edge in all_pairs(face)})
    require(len(source_edges) == 21, "source edge count is not 21")
    require(sorted(source_edges) == expected_edges,
            f"labelled edge mismatch: source={sorted(source_edges)}, lean={expected_edges}")
    require(all(left < right for left, right in source_edges),
            "source edge orientation/order is not canonical")
    require(len(set(source_edges)) == 21, "source edge list contains duplicates")

    cert_path = LEAD / "q0_moment_dual_certificate_0_2.json"
    cert = json.loads(cert_path.read_text())
    coefficients = cert["coefficients"]
    z = raw["z"]
    require(len(coefficients) == 112, f"coefficient count {len(coefficients)} != 112")
    require(len(z) == 112, f"z-slot count {len(z)} != 112")

    slot_groups = {
        "hub": 2,
        "angle": 9,
        "side2": 21,
        "radius2": 18,
        "edge_angle": 21,
        "width": 2,
        "side1": 21,
        "radius1": 18,
    }
    require(sum(slot_groups.values()) == 112, "z-slot group counts do not sum to 112")

    face_angle = [(t, i) for t, face in enumerate(source_faces) for i in face]
    face_edge = [(t, edge) for t, face in enumerate(source_faces) for edge in all_pairs(face)]
    atom_groups = {
        "face_angle": len(face_angle),
        "face_side2": len(face_edge),
        "face_side1": len(face_edge),
        "ring_b": 9,
        "switch_side2": 9,
        "switch_radius2": 9,
        "switch_side1": 9,
        "switch_radius1": 9,
        "alpha": 9,
        "width": 9,
        "copy2": 18,
        "copy1": 18,
        "pi": 1,
        "asin2R": 1,
    }
    require(atom_groups["face_angle"] == 33, "face-angle atom count is not 33")
    require(atom_groups["face_side2"] == atom_groups["face_side1"] == 33,
            "face side atom counts are not 33 each")
    require(sum(atom_groups.values()) == 200,
            f"symbolic atom count {sum(atom_groups.values())} != 200")

    factor_names = [record["factor"] for record in cert["factors"]]
    expected_names = ([f"face{i}" for i in range(11)] +
                      [f"switch{i}" for i in range(9)] +
                      [f"ring{i}" for i in range(9)])
    require(factor_names == expected_names, "factor labels/order do not match 11+9+9 layout")
    require(cert.get("strict") is True and cert.get("start") == 0 and cert.get("span") == 2,
            "source certificate header drifted")

    return {
        "status": "PASS_SOURCE_GRAPH_AND_LAYOUT_ONLY",
        "claim_boundary": "No Lean kernel check, factor bound, balance proof, or exclusion proved.",
        "start": 0,
        "span": 2,
        "lean_module": "N11Formalization.ActualOrderedMetricGraphs",
        "source_graph": raw_path.relative_to(ROOT).as_posix(),
        "source_graph_sha256": sha256(raw_path),
        "source_certificate": cert_path.relative_to(ROOT).as_posix(),
        "source_certificate_sha256": sha256(cert_path),
        "lean_graph_source": lean_file.relative_to(ROOT).as_posix(),
        "lean_graph_source_sha256": sha256(lean_file),
        "faces": [list(face) for face in expected_faces],
        "face_count": len(expected_faces),
        "edge_count": len(expected_edges),
        "declared_source_face_multiset_matches": True,
        "declared_source_edge_set_matches": True,
        "coefficient_count": len(coefficients),
        "z_slot_count": len(z),
        "z_slot_groups": slot_groups,
        "symbolic_atom_count": sum(atom_groups.values()),
        "symbolic_atom_groups": atom_groups,
        "factor_count": len(factor_names),
        "factor_layout": {"face": 11, "switch": 9, "ring": 9},
    }


def main() -> None:
    report = check_graph()
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS q0(4,9): {report['face_count']} faces, {report['edge_count']} edges, "
          f"{report['coefficient_count']} coefficients, {report['symbolic_atom_count']} atoms")
    print(f"wrote {OUT.relative_to(ROOT)} sha256={sha256(OUT)}")


if __name__ == "__main__":
    main()
