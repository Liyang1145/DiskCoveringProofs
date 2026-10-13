"""Own-root, exact footprint/core quantitative family reduction only."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
import exact_graph as exact
sys.path.insert(0, str(exact.kernel.ARCS))
import exact_arcs as arcs

assert __debug__


def arithmetic(N, constants):
    assert type(N) is int and N in (23, 24)
    assert constants["verified"] and type(constants["N"]) is int and constants["N"] == N
    U, D = F(constants["radius_upper"]), constants["angle_scale"]
    assert 0 < U < F(1, 4) and type(D) is int and D == 10**7
    A = constants["angle_caps"][0]
    assert type(A) is int and 0 < A < D//2 and 12*A < D
    footprint_sine = F(arcs.sincos_turn(F(A, 2*D))[1][0], arcs.SCALE)
    assert footprint_sine > U
    core_upper = U/(1-2*U)
    sixth_sine = F(arcs.sincos_turn(F(1, 12))[1][0], arcs.SCALE)
    assert 0 < core_upper < sixth_sine <= F(1, 2)
    assert constants["minimum_boundary_cells"] == 13
    assert constants["minimum_interior_cells"] == 8
    assert constants["maximum_boundary_cells"] == N-8
    families = [[B, N-B] for B in range(13, N-8+1)]
    assert constants["families"] == families
    return {
        "N": N, "radius_upper": str(U), "angle_scale": D, "boundary_footprint_cap": A,
        "strict_circle_budget_gap_D_minus12A": D-12*A,
        "positive_two_rod_footprint_sine_margin": str(footprint_sine-U),
        "normalized_core_radius_upper": str(core_upper),
        "positive_seven_disk_auxiliary_sine_margin": str(sixth_sine-core_upper),
        "quarter_radius_gap": str(1-4*U), "necessary_boundary_internal_families": families,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    sourcepath = ROOT / "N23-N24-BOUNDARY-FAMILY-BUDGET-SOURCE.md"
    frozen, records, rejected = {str(sourcepath): sha(sourcepath)}, [], []
    proofdirs = {
        23: ROOT / "n23-nonstrict-core-fresh-root-upper-local-angle-audit-solo-v1",
        24: ROOT / "n24-core-fresh-v1",
    }
    proofsources = {
        23: ROOT / "replay_isolated_n23_core_prerequisites.py",
        24: ROOT / "replay_isolated_n24_core_prerequisites.py",
    }
    for N in (23, 24):
        constantspath = ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"
        constants = read(constantspath)
        record = arithmetic(N, constants)
        proofpath = proofdirs[N] / "VERIFIED.json"
        rootpath = proofdirs[N] / "root-verified.json"
        proof, root = read(proofpath), read(rootpath)
        assert proof["verified"] and proof["N"] == N
        assert proof["source_sha256"] == sha(proofsources[N])
        assert proof["fresh_root_report_sha256"] == sha(rootpath)
        assert root["verified"] and root["N"] == N
        assert F(root["r_strict_interval"][0]) > 0
        assert F(root["r_strict_interval"][1]) < F(constants["radius_upper"])
        for path, digest in proof["frozen_files"].items():
            assert sha(path) == digest
            assert path not in frozen or frozen[path] == digest
            frozen[path] = digest
        for path in (constantspath, proofpath, rootpath, proofsources[N]):
            frozen[str(path)] = sha(path)
        record["actual_same_root_interval_upper"] = root["r_strict_interval"][1]
        record["fresh_root_report_sha256"] = sha(rootpath)
        records.append(record)
        from copy import deepcopy
        for label, field, value in (
            ("quarter-radius-equality", "radius_upper", "1/4"),
            ("above-quarter-radius", "radius_upper", "251/1000"),
            ("wrong-registered-order", "N", N+1),
            ("wrong-minimum-boundary-count", "minimum_boundary_cells", 12),
            ("wrong-minimum-interior-count", "minimum_interior_cells", 7),
            ("wrong-maximum-boundary-count", "maximum_boundary_cells", N-7),
            ("omitted-required-family", "families", constants["families"][:-1]),
        ):
            changed = deepcopy(constants)
            changed[field] = value
            try:
                arithmetic(N, changed)
            except (AssertionError, ValueError, ZeroDivisionError):
                rejected.append(f"N{N}-{label}")
            else:
                raise AssertionError(("invalid own-order family budget accepted", N, label))
    for path in (Path(__file__), Path(arcs.__file__), HIGH / "exact_graph.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-N24-own-root-exact-boundary-internal-family-budget-v1",
        "orders": records, "negative_controls_rejected": rejected,
        "self_contained_seven_disk_lower_bound_origin_and_circle_capacity_source_bound": True,
        "circle_footprint_and_open_core_inequalities_use_own_order_only": True,
        "old_exact_root_theorems_reused_unchanged_not_claimed_recomputed_here": True,
        "auxiliary_simple_graph_transport_and_source_completeness_not_proved_here": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    print("N23/N24 own-root exact geometric family budgets accepted:",
          [record["necessary_boundary_internal_families"] for record in records], flush=True)


if __name__ == "__main__":
    main()
