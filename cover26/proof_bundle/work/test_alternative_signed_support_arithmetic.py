"""Independently reconstruct actual NEW-support signed leaves and guards."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_alternative_signed_hull_energy as signed
import n26_typed_arithmetic_context as codec
import probe_alternative_signed_hull_forest as producer
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


def check(original, arcs, item):
    leaf = item["actual_closed_leaf"]
    result = signed.bound(
        original["reference"], item["NEW_positive_support"], original["matrix"],
        leaf["lower"], leaf["upper"], item["NEW_signed_certificate"], original["radius"], arcs)
    if (result != item["signed_arithmetic_diagnosis"]["exact_arithmetic_result"]
            or not result["arithmetic_strict_target_test_passed"]
            or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0):
        raise ValueError("actual NEW signed closed-leaf certificate/result did not reconstruct")
    kernel = signed.alternative.kernel_gate(
        original["reference"], item["NEW_positive_support"]["reference"],
        item["NEW_positive_support"]["inverse"])
    if kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not None:
        raise AssertionError("NEW signed arithmetic forged the original fixed kernel identity flag")
    # Independent sine-square energy at actual feasible contracted corners and
    # their midpoint, not the cosine/gradient expression used by the minorant.
    lower, upper = list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))
    samples = (lower, upper, [(a+b)/2 for a, b in zip(lower, upper)])
    for point in samples:
        full = signed.hull.quadratic.reference_gate(
            point, lower, upper, original["matrix"])[0]
        numerator = 0
        for i, j, weight in kernel["pairs"]:
            _, sine = arcs.sincos_turn((full[j]-full[i])/2)
            numerator += 4*weight*max(sine[0]**2, sine[1]**2)
        energy_upper = F(numerator, kernel["energy_denominator"]*arcs.SCALE**2)
        if F(result["boundary_NEW_support_energy_lower"]) > energy_upper:
            raise AssertionError("NEW signed global lower bound exceeds independent feasible point energy")
    return result


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "diagnosis", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("NEW signed arithmetic controls changed zero-source model DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original = model["original"]
    diagnosis = binding.read(args.diagnosis)
    diagnosis_digest = binding.sha(args.diagnosis)
    if (diagnosis["schema"] != "N26-unaccepted-NEW-positive-rod-signed-hull-leaf-diagnosis-v1"
            or diagnosis["executed_probe_sha256"] != binding.sha(producer.__file__)
            or diagnosis["tested_signed_NEW_support_module_sha256"] != binding.sha(signed.__file__)
            or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["candidate_whole_roots_removed"] != 0):
        raise ValueError("NEW signed controls changed actual diagnostic producer, arithmetic or scope")
    arcs = binding.force.load_trig(args.resource)[0]
    selected = [item for item in diagnosis["results"] if item["proposed_strict_closed_leaf_only"]]
    results = [{"old_OPEN_leaf_index": item["old_OPEN_leaf_index"],
                "exact_reconstructed_NEW_signed_result": check(original, arcs, item)}
               for item in selected]
    if not selected:
        raise ValueError("NEW signed controls have no real strict closed leaf")
    first = selected[0]
    negative = []

    def reject(label, mutation):
        bad = deepcopy(first)
        mutation(bad)
        try:
            check(original, arcs, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid actual NEW signed support accepted: " + label)

    reject("NEW-signed-original-rod-edge-omitted",
           lambda bad: bad["NEW_positive_support"]["reference"]["edges"].pop())
    reject("NEW-signed-nonpositive-original-rod-weight",
           lambda bad: bad["NEW_positive_support"]["reference"]["weight_numerators"].__setitem__(0, "0"))
    reject("NEW-signed-new-support-relabeled-as-original-fixed",
           lambda bad: bad["NEW_positive_support"]["reference"].update(
               alternative_weights_are_DIAGNOSTIC_not_original_accepted_support=False))
    reject("NEW-signed-false-integer-ground-inverse",
           lambda bad: bad["NEW_positive_support"]["inverse"]["inverse_numerators"][0].__setitem__(
               0, str(int(bad["NEW_positive_support"]["inverse"]["inverse_numerators"][0][0])+1)))
    reject("NEW-signed-unknown-curvature-proof-field",
           lambda bad: bad["NEW_signed_certificate"].update(fake_acceptance=True))
    reject("NEW-signed-exact-positive-LDL-unsupported",
           lambda bad: bad["NEW_signed_certificate"].update(signed_eta=["-1000000000000"]*15))
    reject("NEW-signed-reference-outside-necessary-polytope",
           lambda bad: bad["NEW_signed_certificate"]["reference_turns"].__setitem__(0, "100"))
    reject("NEW-signed-negative-difference-dual",
           lambda bad: bad["NEW_signed_certificate"].update(
               difference_dual={"q": 1, "terms": [[0, 1, "-1"]]}))
    reject("NEW-signed-duplicate-difference-dual",
           lambda bad: bad["NEW_signed_certificate"].update(
               difference_dual={"q": 1, "terms": [[0, 1, "1"], [0, 1, "1"]]}))
    reject("NEW-signed-closed-leaf-domain-reversed",
           lambda bad: bad["actual_closed_leaf"]["lower"].__setitem__(0, "100"))
    reject("NEW-signed-arithmetic-radius-margin-forged",
           lambda bad: bad["signed_arithmetic_diagnosis"]["exact_arithmetic_result"].update(
               strict_radius_margin="1"))
    reject("NEW-signed-energy-upper-cap-forged",
           lambda bad: bad["signed_arithmetic_diagnosis"]["exact_arithmetic_result"].update(
               NEW_support_whole_original_rod_energy_upper="0"))
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    positives = []
    for item in selected:
        kernel = signed.alternative.kernel_gate(
            original["reference"], item["NEW_positive_support"]["reference"],
            item["NEW_positive_support"]["inverse"])
        result = signed.alternative.dirichlet.bound(
            [a for a, _ in tiny], [b for _, b in tiny], kernel, F(original["radius"])**2, arcs)
        if result["radius_conditional_whole_angle_box_excluded"]:
            raise AssertionError("NEW positive support excludes the known feasible tiny candidate")
        positives.append({"old_OPEN_leaf_index": item["old_OPEN_leaf_index"],
                          "NEW_positive_support_feasible_tiny_candidate_not_excluded": True})
    if binding.sha(args.diagnosis) != diagnosis_digest:
        raise ValueError("actual NEW signed diagnostic changed during independent controls")
    report = {
        "schema": "N26-independent-NEW-positive-rod-signed-hull-arithmetic-controls-v1",
        "all_actual_NEW_signed_closed_leaf_reconstructions_passed": True,
        "actual_strict_closed_leaf_count": len(results), "reconstructed_leaf_results": results,
        "independent_sine_square_feasible_corner_and_midpoint_checks": 3*len(results),
        "invalid_arithmetic_controls_rejected": negative,
        "NEW_positive_support_feasible_tiny_controls": positives,
        "original_fixed_kernel_identity_flag_NOT_forged": True,
        "diagnosis_sha256": diagnosis_digest,
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "complete_latest_source_model_history_geometry_gate_NOT_executed": True,
        "full_entire_source_root_cover_NOT_proved": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_NEW_signed_support_module_sha256": binding.sha(signed.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "NEW_signed_support_independent_arithmetic_controls_completed": True,
        "real_closed_leaves": len(results), "actual_rejections": len(negative),
        "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
