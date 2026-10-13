"""Independent exact original-rod support reconstruction, zero geometry payments."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_quadratic_energy_minorant as energy
import n26_reweighted_candidate_energy as alternative
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import tighten
import probe_candidate_positive_curvature_hull as fixed
import probe_candidate_reweighted_point_energy as producer
import verify_conditional_force_stage as binding


def check(original, arcs, row, diagnosis):
    if (diagnosis["schema"] !=
            "N26-unaccepted-alternative-original-92-rod-point-energy-diagnosis-v1"
            or diagnosis["verified"] is not False
            or diagnosis["new_geometric_payments"] != 0
            or diagnosis["candidate_whole_roots_removed"] != 0
            or diagnosis["source_OPEN_index"] != row["index"]
            or diagnosis["actual_source_closed_box"] != row
            or diagnosis["positive_weight_support_is_NEW_NOT_the_original_fixed_kernel"] is not True
            or diagnosis["whole_actual_root_cover_NOT_proved"] is not True
            or diagnosis["free_vertex_realization_and_continuous_disk_cover_NOT_constructed"] is not True):
        raise ValueError("alternative support diagnostic changed root, geometry or admission scope")
    reference = diagnosis["alternative_reference_DATA"]
    inverse = diagnosis["alternative_exact_inverse_certificate"]
    kernel = alternative.kernel_gate(original["reference"], reference, inverse)
    point = energy.reference_gate(
        diagnosis["exact_point_turns"], row["sharp_lower"], row["sharp_upper"], original["matrix"])[0]
    lower_num, upper_num = 0, 0
    for i, j, weight in kernel["pairs"]:
        _, sine = arcs.sincos_turn((point[j]-point[i])/2)
        squares = [sine[0]**2, sine[1]**2]
        lower_num += 4*weight*(0 if sine[0] <= 0 <= sine[1] else min(squares))
        upper_num += 4*weight*max(squares)
    denominator = kernel["energy_denominator"]*arcs.SCALE**2
    lower, upper = F(lower_num, denominator), F(upper_num, denominator)
    cap = F(original["radius"])**2 * F(sum(kernel["weights"]), kernel["scale"])
    old_lower = F(diagnosis["alternative_point_energy_lower"])
    old_upper = F(diagnosis["alternative_point_energy_upper"])
    if (not lower <= upper or not lower > cap or not old_lower > cap
            or max(lower, old_lower) > min(upper, old_upper)
            or F(diagnosis["alternative_same_root_energy_upper"]) != cap
            or F(diagnosis["alternative_point_energy_strict_margin"]) != old_lower-cap):
        raise ValueError("independent sine-square alternate energy/threshold did not reconstruct")
    return {
        "independent_sine_square_point_energy_lower": str(lower),
        "independent_sine_square_point_energy_upper": str(upper),
        "strict_alternative_energy_margin": str(lower-cap),
        "independent_sine_square_and_cosine_point_energy_intervals_overlap": True,
        "same_original_92_rods_and_new_exact_ground_inverse_reconstructed": True,
    }, kernel, point


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "diagnosis", "report"):
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
        raise ValueError("alternative support controls changed arithmetic DATA identity or scope")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original = model["original"]
    source_digest = binding.sha(args.source / "PENDING-ANGLES.json")
    if source_digest != binding.read(args.source / "VERIFIED.json")["files"]["PENDING-ANGLES.json"]:
        raise ValueError("alternative support controls changed actual current root DATA")
    diagnosis = binding.read(args.diagnosis)
    diagnosis_digest = binding.sha(args.diagnosis)
    if diagnosis["executed_probe_sha256"] != binding.sha(producer.__file__):
        raise ValueError("alternative support producer changed before independent reconstruction")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json")
               if row["index"] == diagnosis["source_OPEN_index"])
    arcs = binding.force.load_trig(args.resource)[0]
    result, kernel, point = check(original, arcs, row, diagnosis)
    negative = []

    def reject(label, mutation):
        bad = deepcopy(diagnosis)
        mutation(bad)
        try:
            check(original, arcs, row, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid actual alternative support accepted: " + label)

    reject("alternative-support-changes-an-original-rod",
           lambda bad: bad["alternative_reference_DATA"]["edges"][0].__setitem__(1, 61))
    reject("alternative-support-omits-an-original-rod",
           lambda bad: bad["alternative_reference_DATA"]["edges"].pop())
    reject("alternative-support-nonpositive-weight",
           lambda bad: bad["alternative_reference_DATA"]["weight_numerators"].__setitem__(0, "0"))
    reject("alternative-support-false-exact-inverse",
           lambda bad: bad["alternative_exact_inverse_certificate"]["inverse_numerators"][0].__setitem__(
               0, str(int(bad["alternative_exact_inverse_certificate"]["inverse_numerators"][0][0])+1)))
    reject("alternative-support-nonpositive-rational-scale",
           lambda bad: bad["alternative_reference_DATA"].update(rational_scale="0"))
    reject("alternative-support-radius-scope-promoted",
           lambda bad: bad["alternative_reference_DATA"].update(radius_scope="unconditional-U"))
    reject("alternative-support-relabeled-as-original-fixed-kernel",
           lambda bad: bad.update(positive_weight_support_is_NEW_NOT_the_original_fixed_kernel=False))
    reject("alternative-support-point-clipped-outside-source",
           lambda bad: bad["exact_point_turns"].__setitem__(0, "100"))
    reject("alternative-support-energy-margin-forged",
           lambda bad: bad.update(alternative_point_energy_strict_margin="1"))
    reject("alternative-point-promoted-to-whole-root",
           lambda bad: bad.update(whole_actual_root_cover_NOT_proved=False))
    reject("alternative-support-rod-realization-claimed",
           lambda bad: bad.update(free_vertex_realization_and_continuous_disk_cover_NOT_constructed=False))
    reject("alternative-support-paid-a-root",
           lambda bad: bad.update(new_geometric_payments=1))
    neighborhoods = []
    for window in (F(1, 1000), F(1, 10000), F(1, 100000), F(1, 1000000)):
        lower = [max(F(a), turn-window) for a, turn in zip(row["sharp_lower"], point[1:])]
        upper = [min(F(b), turn+window) for b, turn in zip(row["sharp_upper"], point[1:])]
        box = tighten(original["matrix"], lower, upper)
        if box is None:
            raise AssertionError("point-containing alternate support neighborhood became empty")
        bounded = alternative.bound(
            original["reference"], diagnosis["alternative_reference_DATA"],
            diagnosis["alternative_exact_inverse_certificate"],
            *box, original["radius"], arcs)
        neighborhoods.append({
            "window_turns": str(window),
            "closed_lower": list(map(str, box[0])), "closed_upper": list(map(str, box[1])),
            "proper_subbox_only_NOT_entire_source_root": box != tighten(
                original["matrix"], row["sharp_lower"], row["sharp_upper"]),
            "exact_alternative_support_bound": bounded,
        })
    if (binding.sha(args.diagnosis) != diagnosis_digest
            or binding.sha(args.source / "PENDING-ANGLES.json") != source_digest):
        raise ValueError("alternate support diagnosis or actual source DATA changed during controls")
    report = {
        "schema": "N26-independent-alternative-original-rod-support-arithmetic-controls-v1",
        **result, "invalid_arithmetic_controls_rejected": negative,
        "actual_point_neighborhoods": neighborhoods,
        "strict_proper_neighborhoods_arithmetically_excluded": sum(
            item["exact_alternative_support_bound"]["radius_conditional_whole_angle_box_excluded"]
            for item in neighborhoods),
        "diagnosis_sha256": diagnosis_digest,
        "source_OPEN_index": row["index"], "actual_source_closed_box": row,
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "whole_actual_root_cover_NOT_proved": True,
        "complete_actual_latest_model_source_history_geometry_admission_NOT_performed": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_alternative_module_sha256": binding.sha(alternative.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "independent_alternative_support_controls_completed": True,
        "actual_rejections": len(negative),
        "strict_proper_neighborhoods": report["strict_proper_neighborhoods_arithmetically_excluded"],
        "verified": False, "new_geometric_payments": 0, "whole_actual_root_NOT_paid": True}),
        flush=True)


if __name__ == "__main__":
    main()
