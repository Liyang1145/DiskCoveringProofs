"""Independent sine-square energy diagnostic; NOT a feasible cover certificate."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_quadratic_energy_minorant as energy
import n26_typed_arithmetic_context as codec
from n26_sharp_radius_constraints import tighten
import probe_candidate_fixed_energy_limit as producer
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


def check(original, kernel, arcs, actual_row, diagnosis):
    if (diagnosis["source_OPEN_index"] != actual_row["index"]
            or diagnosis["actual_source_closed_box"] != actual_row
            or diagnosis["verified"] is not False
            or diagnosis["new_geometric_payments"] != 0
            or diagnosis["this_is_NOT_an_actual_rod_realization_or_continuous_disk_cover"] is not True
            or diagnosis["no_free_vertex_geometry_constructed_or_certified"] is not True):
        raise ValueError("fixed-energy diagnostic changed target/domain or became a covering claim")
    turns = list(map(F, diagnosis["exact_point_turns"]))
    root_box = tighten(original["matrix"], actual_row["sharp_lower"], actual_row["sharp_upper"])
    point = energy.reference_gate(turns, *root_box, original["matrix"])[0]
    lower_num, upper_num = 0, 0
    for i, j, weight in kernel["pairs"]:
        _, sine = arcs.sincos_turn((point[j] - point[i]) / 2)
        lows = [sine[0]**2, sine[1]**2]
        if sine[0] <= 0 <= sine[1]:
            lows.append(0)
        lower_num += 4 * weight * min(lows)
        upper_num += 4 * weight * max(sine[0]**2, sine[1]**2)
    denominator = kernel["energy_denominator"] * arcs.SCALE**2
    lower, upper = F(lower_num, denominator), F(upper_num, denominator)
    cap = F(original["radius"])**2 * F(sum(kernel["weights"]), kernel["scale"])
    previous_lower = F(diagnosis["original_fixed_92_rod_Schur_energy_lower"])
    previous_upper = F(diagnosis["original_fixed_92_rod_Schur_energy_upper"])
    if (not lower <= upper < cap
            or not previous_lower <= previous_upper < cap
            or max(lower, previous_lower) > min(upper, previous_upper)
            or F(diagnosis["original_same_root_rod_energy_threshold"]) != cap
            or F(diagnosis["strict_margin_below_fixed_energy_threshold"]) != cap - previous_upper):
        raise ValueError("sine-square and cosine exact energy intervals/threshold do not agree")
    return {
        "independent_sine_square_energy_lower": str(lower),
        "independent_sine_square_energy_upper": str(upper),
        "strict_sine_square_margin_below_fixed_energy_threshold": str(cap - upper),
        "independent_sine_square_and_original_cosine_intervals_overlap": True,
        "exact_point_satisfies_actual_closed_box_and_every_necessary_difference_constraint": True,
    }


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
        raise ValueError("fixed-energy independent test changed zero-source model/resource")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    accepted = binding.read(args.source / "VERIFIED.json")
    if binding.sha(args.source / "PENDING-ANGLES.json") != accepted["files"]["PENDING-ANGLES.json"]:
        raise ValueError("fixed-energy test changed actual source root DATA")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json") if row["index"] == 28)
    diagnosis = binding.read(args.diagnosis)
    if diagnosis["executed_probe_sha256"] != binding.sha(producer.__file__):
        raise ValueError("fixed-energy independent test changed actual diagnostic executor")
    arcs = binding.force.load_trig(args.resource)[0]
    result = check(original, kernel, arcs, row, diagnosis)
    rejected = []

    def reject(name, mutation):
        bad = deepcopy(diagnosis)
        mutation(bad)
        try:
            check(original, kernel, arcs, row, bad)
        except (ValueError, KeyError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError("invalid fixed-energy diagnostic accepted: " + name)

    reject("wrong-source-root-index", lambda bad: bad.update(source_OPEN_index=29))
    reject("exact-point-outside-source-box", lambda bad: bad["exact_point_turns"].__setitem__(0, "100"))
    reject("source-closed-box-changed", lambda bad: bad["actual_source_closed_box"]["sharp_lower"].__setitem__(0, "0"))
    reject("original-energy-upper-fabricated", lambda bad: bad.update(
        original_fixed_92_rod_Schur_energy_upper="0"))
    reject("original-radius-energy-threshold-changed", lambda bad: bad.update(
        original_same_root_rod_energy_threshold="1"))
    reject("rod-realization-or-continuous-cover-claimed", lambda bad: bad.update(
        this_is_NOT_an_actual_rod_realization_or_continuous_disk_cover=False))
    reject("free-vertex-geometry-claimed", lambda bad: bad.update(
        no_free_vertex_geometry_constructed_or_certified=False))
    reject("diagnostic-paid-a-root", lambda bad: bad.update(new_geometric_payments=1))
    report = {
        "schema": "N26-independent-exact-fixed-energy-limit-diagnostic-controls-v1",
        **result, "invalid_diagnostic_controls_rejected": rejected,
        "source_OPEN_index": 28, "diagnosis_sha256": binding.sha(args.diagnosis),
        "exact_energy_condition_is_inconclusive_for_this_point_NOT_a_cover_counterexample": True,
        "complete_actual_latest_model_source_ownership_replay_NOT_performed": True,
        "verified": False, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0, "global_optimality_proved": False,
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if "energy_lower" not in key and "energy_upper" not in key
                      and "margin_below" not in key}, indent=2), flush=True)


if __name__ == "__main__":
    main()
