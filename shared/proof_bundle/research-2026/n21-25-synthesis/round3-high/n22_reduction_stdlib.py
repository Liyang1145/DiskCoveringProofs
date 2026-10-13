"""Fresh exact numerical interfaces for the written n22 arbitrary-cover reduction.

No inverse-trig discovery/optimizer is imported. The circle ownership,
Voronoi reduction and peeling induction are separate written arguments.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import sys
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(exact.kernel.ARCS))
import exact_arcs as arcs
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    constpath = ROOT.parent / "evidence/core-reduction/constants/n22.json"
    rootpath = ROOT / "evidence/n22-interfaces-resume1/evidence/n22/algebraic-check1/root-verified.json"
    sixpath = ROOT / "evidence/six-lower-stdlib-resume1.json"
    const, root, six = map(read, (constpath, rootpath, sixpath))
    assert const["verified"] and root["verified"] and six["verified"]
    assert root["N"] == const["N"] == 22
    assert root["root_sha256"] == sha(ROOT.parent / "evidence/n22/core-root.json")
    assert root["system_sha256"] == sha(ROOT.parent / "evidence/n22/core-system.json")
    assert root["source_sha256"] == sha(ROOT.parent / "algebraic_roots.py")
    U = F(const["radius_upper"])
    assert U == F("0.253251459835093")
    assert F(root["r_strict_interval"][1]) < U < F(1, 3)
    assert const["radius_root_report_sha256"] == sha(rootpath)
    circle_sine = F(arcs.sincos_turn(F(1, 24))[1][0], arcs.SCALE)
    assert U < circle_sine
    Q = F(2771, 5000)
    assert F(six["radius"]) == Q
    assert six["topology_orbits"] == 3 and six["independently_enumerated_fixed_boundary_types"] == 14
    assert six["source_sha256"] == sha(ROOT / "replay_six_stdlib.py")
    assert six["force_kernel_sha256"] == sha(ROOT.parent / "round2-grouped/partial_force_exact.py")
    assert six["trig_source_sha256"] == sha(exact.kernel.ARCS / "exact_arcs.py")
    oldsix = ROOT.parent.parent / "n21-global/evidence"
    assert six["six_census_sha256"] == sha(oldsix / "peeling-round1/N6-B6-noscreen.json")
    for row in six["trees"]:
        assert row["verified"] and F(row["minimum_margin"]) > 0
        assert row["tree_sha256"] == sha(oldsix / f"six-core-exclusion/hexagon-{row['index']}.json.gz")
    ratio = U/(1-2*U)
    assert Q-ratio > 0
    assert const["families"] == [[13, 9], [14, 8], [15, 7]]
    assert (const["minimum_boundary_cells"], const["minimum_interior_cells"],
            const["maximum_boundary_cells"]) == (13, 7, 15)
    D, caps = const["angle_scale"], const["angle_caps"]
    assert D == 10**7 and caps == [815002, 1690622, 2746810]
    assert 0 < 2*caps[0] < caps[1] < caps[2] < D//2
    margins = []
    for k, cap in zip((1, 2, 3), caps):
        lower = F(arcs.sincos_turn(F(cap, 2*D))[1][0], arcs.SCALE)
        margin = lower-k*U
        assert margin > 0
        margins.append(str(margin))
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    report = {"verified": True, "N": 22, "radius_upper": str(U),
              "strict_radius_root_gap": str(U-F(root["r_strict_interval"][1])),
              "circle_capacity_sine_gap": str(circle_sine-U),
              "minimum_boundary_cells": 13, "maximum_boundary_cells": 15,
              "minimum_interior_cells": 7, "families": const["families"],
              "auxiliary_radius": str(Q), "strict_core_gap": str(Q-ratio),
              "angle_scale": D, "angle_caps": caps, "sine_gaps": margins,
              "constants_sha256": sha(constpath), "root_report_sha256": sha(rootpath),
              "six_report_sha256": sha(sixpath),
              "trig_source_sha256": sha(exact.kernel.ARCS / "exact_arcs.py"),
              "source_sha256": sha(Path(__file__)), "no_optimizer_imported": True,
              "actual_cover_topology_argument_not_formalized_here": True,
              "global_optimality_proved": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N22 stdlib exact radius/capacity/core/angle-cap interfaces PASS", flush=True)


if __name__ == "__main__":
    main()
