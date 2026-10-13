"""Unaccepted integrated-curvature/LOCAL covers using an exact root minorant.

Uniform root Taylor certificates may be restricted to contained closed slabs.
No old constant-hull verifier is used or relabelled as this new integrated mode.
"""

import argparse
from fractions import Fraction as F
import json
from math import isqrt
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_integrated_hull_curvature as integrated
import n26_signed_hull_local_cover as partition
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import tighten
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


def slab_bound(kernel, matrix, reference, root_box, slab_box, eta, radius, arcs):
    lower, upper = slab_box
    if (any(a < ra or c > rc for a, c, ra, rc in
            zip(lower, upper, root_box[0], root_box[1]))
            or any(a > c for a, c in zip(lower, upper))):
        raise ValueError("integrated diagnostic slab is not contained in its certified root")
    ref, lo, hi, _, _ = integrated.hull.hull_gate(reference, lower, upper, matrix)
    point, gradient = integrated.hull.outward_point_values(kernel, ref, arcs)
    support, dual_check = integrated.hull.support(
        ref, lo, hi, matrix, gradient, eta, {"q": 1, "terms": []})
    lower_energy = point + support
    weight_sum = F(sum(kernel["weights"]), kernel["scale"])
    upper_energy = F(radius)**2 * weight_sum
    normalized = max(F(0), lower_energy) / weight_sum
    grid = 10**100
    root_num = isqrt(normalized.numerator * grid**2 // normalized.denominator)
    lower_radius = F(root_num, grid)
    if not lower_radius**2 <= normalized < (lower_radius + F(1, grid))**2:
        raise AssertionError("integrated diagnostic radius conversion not outward")
    margin = lower_energy - upper_energy
    return {
        "boundary_energy_lower": str(lower_energy),
        "whole_original_rod_energy_upper": str(upper_energy),
        "strict_energy_margin": str(margin),
        "strict_radius_margin": str(lower_radius - F(radius)),
        "arithmetic_strict_slab_test_passed": margin > 0 and lower_radius > F(radius),
        "exact_zero_dual_support": str(support), **dual_check,
        "uses_freshly_checked_uniform_integral_root_certificate": True,
        "closed_slab_is_contained_in_certified_closed_root": True,
    }


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "curvature-diagnosis", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--local-window", default="1/2500000")
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    window = F(args.local_window)
    if window <= 0:
        raise ValueError("integrated diagnostic LOCAL window must be positive")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("integrated cover diagnosis changed zero-source arithmetic resource")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("integrated cover diagnosis changed the actual current radius")
    pending = {row["index"]: row for row in binding.read(args.source / "PENDING-ANGLES.json")}
    diagnosis = binding.read(args.curvature_diagnosis)
    if (diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["actual_current_audit_sha256"] != current_digest
            or diagnosis["modules"][linux(Path(integrated.__file__))]
            != binding.sha(integrated.__file__)):
        raise ValueError("integrated cover diagnosis changed original integral module/identity")
    ref = list(map(F, diagnosis["reference_turns"]))
    arcs = binding.force.load_trig(args.resource)[0]
    roots = []
    for suggestion in diagnosis["results"]:
        if not suggestion["exact_signed_integral_curvature_certified"]:
            continue
        index = suggestion["source_OPEN_index"]
        row = pending[index]
        if row != suggestion["actual_source_closed_box"]:
            raise ValueError("integrated cover diagnosis changed the actual entire root row")
        root_box = tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
        eta = list(map(F, suggestion["signed_eta"]))
        certificate = integrated.gate(
            kernel, original["matrix"], ref, *root_box, eta, arcs, suggestion["parts"])
        lower, upper = [list(part) for part in root_box]
        slabs = []
        for axis in suggestion["free_axes"]:
            for side, cut in (("left", ref[axis] - window),
                              ("right", ref[axis] + window)):
                if not lower[axis] < cut < upper[axis]:
                    continue
                a, c = list(lower), list(upper)
                if side == "left":
                    c[axis] = cut
                else:
                    a[axis] = cut
                box = tighten(original["matrix"], a, c)
                slab = {
                    "axis": axis, "side": side, "cut": str(cut),
                    "parent_closed_lower": list(map(str, lower)),
                    "parent_closed_upper": list(map(str, upper)),
                    "both_closed_halves_include_shared_cut": True,
                }
                if box is None:
                    slab.update(kind="EMPTY", arithmetic_obligation_passed=True)
                else:
                    check = slab_bound(
                        kernel, original["matrix"], ref, root_box, box, eta,
                        original["radius"], arcs)
                    slab.update(
                        kind="INTEGRATED-HULL-ENERGY",
                        sharp_lower=list(map(str, box[0])),
                        sharp_upper=list(map(str, box[1])),
                        arithmetic_result=check,
                        arithmetic_obligation_passed=check["arithmetic_strict_slab_test_passed"])
                slabs.append(slab)
                if side == "left":
                    lower[axis] = cut
                else:
                    upper[axis] = cut
                lower, upper = tighten(original["matrix"], lower, upper)
        central = {"closed_lower": list(map(str, lower)),
                   "closed_upper": list(map(str, upper))}
        try:
            local = partition.forest.local_proof(original, lower, upper)
        except ValueError as error:
            central.update(original_LOCAL_arithmetic_check_passed=False,
                           diagnostic_failure=str(error))
        else:
            central.update(original_LOCAL_arithmetic_check_passed=True,
                           original_LOCAL_result=local)
        item = {
            "source_OPEN_index": index, "actual_source_closed_box": row,
            "uniform_integral_root_curvature_certificate": certificate,
            "reference_turns": list(map(str, ref)),
            "sequential_closed_slabs": slabs, "central_closed_box": central,
            "all_arithmetic_cover_obligations_passed": all(
                slab["arithmetic_obligation_passed"] for slab in slabs
            ) and central["original_LOCAL_arithmetic_check_passed"],
        }
        first_parts, first_central = partition.partition(
            original["matrix"], row, item, tighten)
        other_parts, other_central = partition.partition(
            original["matrix"], row, item, partition.independently_contract)
        if first_parts != other_parts or first_central != other_central:
            raise AssertionError("integrated diagnosis independent closed partitions disagree")
        item["two_independent_closed_partition_checks_passed"] = True
        # Tiny candidate positive control uses the actual original tiny domain.
        tiny = [tuple(map(F, pair)) for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
        tlo, thi = tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])
        # The tiny candidate is outside some source roots, so its curvature
        # must be checked on its own Taylor segment domain, not inherited.
        integrated.gate(kernel, original["matrix"], ref, tlo, thi, eta, arcs,
                        suggestion["parts"])
        tiny_check = slab_bound(
            kernel, original["matrix"], ref, (tlo, thi), (tlo, thi), eta,
            original["radius"], arcs)
        if tiny_check["arithmetic_strict_slab_test_passed"]:
            raise AssertionError("integrated diagnosis excludes the feasible tiny candidate")
        item["feasible_tiny_candidate_not_strictly_excluded"] = True
        roots.append(item)
        print(json.dumps({
            "root": index, "slabs": len(slabs),
            "strict_arithmetic_slabs": sum(s["arithmetic_obligation_passed"] for s in slabs),
            "central_original_LOCAL_check": central["original_LOCAL_arithmetic_check_passed"],
            "all_arithmetic_cover_checks_passed": item["all_arithmetic_cover_obligations_passed"],
            "failed_slabs": [
                {"axis": s["axis"], "side": s["side"],
                 "margin_display": float(F(s["arithmetic_result"]["strict_energy_margin"]))}
                for s in slabs if not s["arithmetic_obligation_passed"]],
            "verified": False, "new_geometric_payments": 0}), flush=True)
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("current audit changed during integrated root-cover diagnosis")
    report = {
        "schema": "N26-unaccepted-integrated-Taylor-hull-original-LOCAL-cover-diagnosis-v1",
        "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "resource_acceptance_sha256": fixed.RESOURCE_SHA,
        "curvature_diagnosis_sha256": binding.sha(args.curvature_diagnosis),
        "local_window_turns": str(window), "roots": roots,
        "complete_arithmetic_cover_roots": sum(
            item["all_arithmetic_cover_obligations_passed"] for item in roots),
        "full_latest_model_source_history_and_ownership_replay_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "existing_constant_hull_acceptance_does_NOT_admit_this_integrated_mode": True,
        "needs_distinct_integrated_mode_controls_frozen_acceptance_and_actual_replay": True,
        "original_LOCAL_allowance_unchanged": "7/800000",
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (integrated, integrated.hull, partition, codec, identity)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"diagnosis_completed": True,
                      "complete_arithmetic_cover_roots": report["complete_arithmetic_cover_roots"],
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
