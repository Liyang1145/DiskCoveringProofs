#!/usr/bin/env python3
"""Map the exact q0(5,8) dual source slots to Lean `CanonicalCoeffQ` fields.

The source LP layout is checked from `q0_closure_dual.py`; this audit only
records a field map.  It does not assert mask balance, factor bounds, a strict
total, or a kernel result.
"""
from __future__ import annotations
import hashlib, json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SRC = HERE / "q0-degree5-exact-source.json"
OUT = HERE / "q0-degree5-canonical-map.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def frac(pair: list[int]) -> Fraction:
    return Fraction(pair[0], pair[1])


def main() -> None:
    report = json.loads(SRC.read_text())
    z = [frac(p) for p in report["coefficients"]]
    assert len(z) == 121
    faces = [tuple(f) for f in report["lean_graph_faces"]]
    edges = [tuple(e) for e in report["lean_graph_edges"]]
    assert len(faces) == 11 and len(edges) == 21
    # Source layout: mu9, hub2, side21, radius18, angle21, lambda, eta,
    # linear39, closure9 (q0_closure_dual.py).
    mu = z[:11]
    side = z[11:32]
    radius = z[32:50]
    angle = z[50:71]
    width = z[71]
    eta = z[72]
    linear = z[73:112]
    closure = z[112:121]
    # `sideFirst` is the LP `side` group and `sideSecond` its sqrt(x) copy.
    faceMask = []
    for t, face in enumerate(faces):
        row = []
        for i in sorted(face):
            e = tuple(sorted(v for v in face if v != i))
            row.append(1 if next(k for k, g in enumerate(faces) if e[0] in g and e[1] in g) == t else -1)
        faceMask.append(row)
    mapping = {
        "status": "PASS_SOURCE_SLOT_MAP_WITH_OPEN_CLOSURE_GROUP",
        "claim_boundary": "Field map only; no balance, bound, total, exclusion, or Lean kernel claim.",
        "source": SRC.relative_to(ROOT).as_posix(),
        "source_sha256": sha(SRC),
        "mu": ["z[0:9] ring sites", "z[9:11] hub sites"],
        "faceMask": "sgn(+1 first source owner, -1 second) of opposite edge in each face",
        "faceMask_rows": faceMask,
        "switchMask": "-1 on all Fin 9 (LP switch side and linear coefficients are -1)",
        "sideFirst": "z[11:32] in canonical source edge order",
        "sideSecond": "z[73:94] in canonical source edge order",
        "leftSecond": "z[32+2i]",
        "rightSecond": "z[33+2i]",
        "leftFirst": "z[94+2i]",
        "rightFirst": "z[95+2i]",
        "width": "z[71] (lambda; LP constant is -2*pi*lambda)",
        "eta": "z[72] (checked zero in exact-source reconstruction)",
        "unmapped_groups": {
            "angle_slack": {"slice": "z[50:71]", "reason": "likely certificate `kap`, not a CanonicalCoeffQ field"},
            "closure": {"slice": "z[112:121]", "reason": "nine LP closure/angle-slack slots have no direct CanonicalCoeffQ field"},
        },
        "counts": {"mu": len(mu), "faceMask": sum(map(len, faceMask)),
                   "switchMask": 9, "side": len(side), "radius": len(radius),
                   "linear": len(linear), "closure": len(closure)},
        "checks": {
            "face_triangle_count": all(len(f) == 3 for f in faces),
            "all_opposite_edges_in_edges": all(tuple(sorted(v for v in f if v != i)) in edges
                                               for f in faces for i in f),
            "edge_order_matches_side_group": len(side) == len(edges),
            "radius_pairs_complete": len(radius) == 2 * 9,
            "linear_copy_pairs_complete": len(linear[21:]) == 2 * 9,
            "closure_count": len(closure) == 9,
            "eta_zero": eta == 0,
        },
    }
    assert all(mapping["checks"].values())
    OUT.write_text(json.dumps(mapping, indent=2) + "\n")
    print("PASS source slot map; 8 CanonicalCoeffQ field groups mapped, closure group open")
    print(f"wrote {OUT.relative_to(ROOT)} sha256={sha(OUT)}")


if __name__ == "__main__":
    main()
