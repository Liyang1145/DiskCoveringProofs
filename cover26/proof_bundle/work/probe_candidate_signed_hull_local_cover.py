"""Unaccepted whole-root signed-energy/LOCAL cover diagnosis.

This suggests a new cover only. It never replaces the current accepted
per-root forest or its non-OPEN history, and pays zero roots and leaves.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_energy_local_forest as forest
import n26_current_candidate_layer_identity as identity
import n26_signed_hull_energy_minorant as hull
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import tighten
import probe_candidate_positive_curvature_hull as curvature_probe
import probe_candidate_signed_hull_energy as suggestions
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source",
                 "curvature-diagnosis", "arithmetic-controls", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--indices", type=int, nargs="+", default=[41, 45, 48])
    parser.add_argument("--local-window", default="1/10000000")
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    window = F(args.local_window)
    if window <= 0:
        raise ValueError("LOCAL window must be positive")
    resource = binding.read(args.resource / "VERIFIED.json")
    if (
        binding.sha(args.resource / "VERIFIED.json") != curvature_probe.RESOURCE_SHA
        or binding.sha(args.resource_replay) != curvature_probe.RESOURCE_SHA
        or binding.read(args.resource_replay) != resource
        or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
        or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
    ):
        raise ValueError("cover diagnosis changed the zero-source arithmetic context")
    for name in ("CONTEXT.json", "n26_typed_arithmetic_context.py"):
        if binding.sha(args.resource / name) != resource["files"][name]:
            raise ValueError("cover diagnosis changed fixed model/codec bytes")
    if binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]:
        raise ValueError("cover diagnosis executed a different typed codec")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    current_digest = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("cover diagnosis changed the exact current radius")
    controls = binding.read(args.arithmetic_controls)
    if (
        controls["arithmetic_controls_passed"] is not True
        or controls["new_geometric_payments"] != 0
        or controls["tested_signed_hull_module_sha256"] != binding.sha(hull.__file__)
        or controls["executed_test_sha256"] != binding.sha(Path(__file__).with_name(
            "test_signed_hull_energy_arithmetic.py"))
    ):
        raise ValueError("cover diagnosis lacks this actual lemma's arithmetic controls")
    diagnosis = binding.read(args.curvature_diagnosis)
    if (
        diagnosis["actual_current_audit_sha256"] != current_digest
        or diagnosis["executed_probe_sha256"] != binding.sha(curvature_probe.__file__)
        or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
    ):
        raise ValueError("cover diagnosis changed curvature suggestions or their source")
    reference = list(map(F, diagnosis["reference_turns"]))
    pending = {row["index"]: row for row in binding.read(args.source / "PENDING-ANGLES.json")}
    curvature = {row["source_OPEN_index"]: row for row in diagnosis["results"]}
    arcs = binding.force.load_trig(args.resource)[0]
    roots = []
    for root in args.indices:
        suggestion = curvature[root]
        row = pending[root]
        if (row != suggestion["actual_source_closed_box"]
                or not suggestion["exact_signed_diagonal_curvature_check_passed"]):
            raise ValueError("cover diagnosis changed an actual remaining root")
        eta = [F(suggestion["fixed_anchor_negative_allowance"])] * 10 + [
            -F(suggestion["last_five_positive_curvature"])] * 5
        initial = tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
        lower, upper = initial
        slabs = []
        for axis in range(10, 15):
            for side, cut in (("left", reference[axis] - window),
                              ("right", reference[axis] + window)):
                if not lower[axis] < cut < upper[axis]:
                    continue
                slab_lower, slab_upper = list(lower), list(upper)
                if side == "left":
                    slab_upper[axis] = cut
                else:
                    slab_lower[axis] = cut
                box = tighten(original["matrix"], slab_lower, slab_upper)
                slab = {
                    "axis": axis, "side": side, "cut": str(cut),
                    "parent_closed_lower": list(map(str, lower)),
                    "parent_closed_upper": list(map(str, upper)),
                    "both_closed_halves_include_shared_cut": True,
                }
                if box is None:
                    slab.update(kind="EMPTY", arithmetic_obligation_passed=True)
                else:
                    a, c = box
                    ref, lo, hi, _, _ = hull.hull_gate(
                        reference, a, c, original["matrix"])
                    _, gradient = hull.outward_point_values(kernel, ref, arcs)
                    dual, numerical = suggestions.suggest_dual(
                        kernel, original["matrix"], ref, lo, hi, gradient, eta)
                    cert = {
                        "reference_turns": list(map(str, reference)),
                        "signed_eta": list(map(str, eta)), "difference_dual": dual}
                    result = hull.bound(
                        kernel, original["matrix"], a, c, cert,
                        original["radius"], arcs)
                    slab.update(
                        kind="SIGNED-HULL-ENERGY",
                        sharp_lower=list(map(str, a)), sharp_upper=list(map(str, c)),
                        certificate=cert, arithmetic_result=result,
                        arithmetic_obligation_passed=result["arithmetic_strict_exclusion_test_passed"],
                        **numerical)
                slabs.append(slab)
                print(json.dumps({
                    "root": root, "axis": axis, "side": side,
                    "strict_arithmetic_slab": slab["arithmetic_obligation_passed"],
                    "margin_display": float(F(slab["arithmetic_result"][
                        "minimum_strict_energy_margin"])) if "arithmetic_result" in slab else None,
                    "verified": False, "new_geometric_payments": 0}), flush=True)
                if side == "left":
                    lower[axis] = cut
                else:
                    upper[axis] = cut
                lower, upper = tighten(original["matrix"], lower, upper)
        central = {"closed_lower": list(map(str, lower)),
                   "closed_upper": list(map(str, upper))}
        try:
            local = forest.local_proof(original, lower, upper)
        except ValueError as error:
            central.update(original_LOCAL_arithmetic_check_passed=False,
                           diagnostic_failure=str(error))
        else:
            central.update(original_LOCAL_arithmetic_check_passed=True,
                           original_LOCAL_result=local)
        complete = all(slab["arithmetic_obligation_passed"] for slab in slabs) and central[
            "original_LOCAL_arithmetic_check_passed"]
        roots.append({
            "source_OPEN_index": root, "actual_source_closed_box": row,
            "sequential_closed_slabs": slabs, "central_closed_box": central,
            "all_arithmetic_cover_obligations_passed": complete,
            "current_accepted_owned_forest_not_modified_or_replaced": True,
        })
        print(json.dumps({
            "root": root, "slabs": len(slabs),
            "slabs_arithmetic_passed": sum(slab["arithmetic_obligation_passed"] for slab in slabs),
            "central_original_LOCAL_check": central["original_LOCAL_arithmetic_check_passed"],
            "all_cover_arithmetic_checks_passed": complete,
            "verified": False, "current_candidate_whole_roots_removed": 0}), flush=True)
    if binding.sha(args.current_audit) != current_digest:
        raise ValueError("actual current snapshot changed during cover diagnosis")
    report = {
        "schema": "N26-unaccepted-signed-hull-energy-original-LOCAL-cover-diagnosis-v1",
        "verified": False, "actual_current_audit_sha256": current_digest,
        "actual_latest_candidate_layer_identity_only": layer,
        "resource_acceptance_sha256": curvature_probe.RESOURCE_SHA,
        "curvature_diagnosis_sha256": binding.sha(args.curvature_diagnosis),
        "arithmetic_controls_sha256": binding.sha(args.arithmetic_controls),
        "local_window_turns": str(window), "roots": roots,
        "all_arithmetic_cover_roots_passed": sum(
            row["all_arithmetic_cover_obligations_passed"] for row in roots),
        "full_latest_source_model_ownership_replay_not_performed": True,
        "no_accepted_per_root_non_OPEN_history_replaced": True,
        "current_candidate_whole_roots_removed": 0, "new_geometric_payments": 0,
        "original_52_coordinate_LOCAL_allowance_unchanged": "7/800000",
        "LOCAL_equality_region_not_declared_empty": True,
        "independent_full_owned_history_standalone_and_actual_replay_still_required": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (forest, identity, hull, codec, suggestions, binding)},
        "lemma_sha256": binding.sha(Path(__file__).with_name(
            "n26-signed-hull-energy-minorant-proof.md")),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "diagnosis_completed": True,
        "all_arithmetic_cover_roots_passed": report["all_arithmetic_cover_roots_passed"],
        "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
