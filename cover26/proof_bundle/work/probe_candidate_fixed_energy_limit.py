"""Exact diagnostic angular point passing the ORIGINAL fixed energy condition.

This is NOT a covering construction or a current source/model acceptance.
It illustrates why a sufficient fixed-kernel exclusion can remain inconclusive.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_quadratic_energy_minorant as energy
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import tighten
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


DIRECTION = [
    F(0), F(0), F(0), F(0), F(0), F(0),
    F(329882667, 10**9), F(329882667, 10**9),
    F(619533454, 10**9), F(899255342, 10**9), F(1), F(1),
    F(894789244, 10**9), F(617120098, 10**9), F(348470594, 10**9),
]


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--step", default="1/100000")
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    step = F(args.step)
    if not 0 < step <= F(1, 10000):
        raise ValueError("fixed-energy diagnostic step invalid")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("fixed-energy diagnosis changed zero-source resource/model identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("fixed-energy diagnosis changed the exact current radius")
    rows = binding.read(args.source / "PENDING-ANGLES.json")
    selected = [row for row in rows if row["index"] == 28]
    if len(selected) != 1:
        raise ValueError("fixed-energy diagnosis requires actual unresolved root28 DATA")
    row = selected[0]
    tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    reference = tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])[0]
    point = [value + step*direction for value, direction in zip(reference, DIRECTION)]
    closed_box = tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    full_point = energy.reference_gate(point, *closed_box, original["matrix"])[0]
    arcs = binding.force.load_trig(args.resource)[0]
    numerator = 0
    for i, j, weight in kernel["pairs"]:
        cosine, _ = arcs.sincos_turn(full_point[j] - full_point[i])
        numerator += 2 * weight * (arcs.SCALE - cosine[0])
    upper = F(numerator, kernel["energy_denominator"] * arcs.SCALE)
    lower, _ = energy.point_energy_gradient(kernel, full_point, arcs)
    cap = F(original["radius"])**2 * F(sum(kernel["weights"]), kernel["scale"])
    if not lower <= upper < cap:
        raise ValueError("diagnostic point did not pass the original fixed energy threshold")
    # A zero-volume exact point, not a claimed neighborhood or actual cover.
    if tighten(original["matrix"], point, point) != (point, point):
        raise AssertionError("fixed-energy diagnostic point lost its exact necessary domain")
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("current snapshot changed during fixed-energy diagnosis")
    report = {
        "schema": "N26-unaccepted-exact-original-fixed-energy-limit-diagnosis-v1",
        "verified": False,
        "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "resource_acceptance_sha256": fixed.RESOURCE_SHA,
        "source_OPEN_index": 28, "actual_source_closed_box": row,
        "rational_point_step": str(step), "rational_direction": list(map(str, DIRECTION)),
        "exact_point_turns": list(map(str, point)),
        "point_inside_entire_actual_root28_closed_box": True,
        "all_necessary_difference_constraints_checked_exactly": True,
        "original_fixed_92_rod_Schur_energy_lower": str(lower),
        "original_fixed_92_rod_Schur_energy_upper": str(upper),
        "original_same_root_rod_energy_threshold": str(cap),
        "strict_margin_below_fixed_energy_threshold": str(cap - upper),
        "a_uniform_fixed_kernel_energy_exclusion_cannot_cover_this_exact_point": True,
        "this_is_NOT_an_actual_rod_realization_or_continuous_disk_cover": True,
        "no_free_vertex_geometry_constructed_or_certified": True,
        "not_a_counterexample_to_the_covering_radius_or_original_LOCAL_barrier": True,
        "requires_stronger_necessary_geometry_or_alternative_valid_support_for_this_region": True,
        "complete_latest_original_model_source_history_replay_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (energy, codec, identity)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "exact_angular_point_passes_original_fixed_energy_condition": True,
        "margin_display": float(cap - upper),
        "not_an_actual_disk_cover_or_rod_realization": True,
        "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
