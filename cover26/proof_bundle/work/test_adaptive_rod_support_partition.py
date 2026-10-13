"""Synthetic closed-partition guards plus a REAL strict proper neighborhood.

This test never claims whole-root closure or complete latest source replay.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import n26_adaptive_rod_support_forest as forest
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "alternative-diagnosis",
                 "alternative-controls", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    accepted = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != accepted
            or accepted["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or accepted["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != accepted["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != accepted["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("adaptive partition controls changed fixed arithmetic DATA identity")
    model = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    arcs = binding.force.load_trig(args.resource)[0]
    diagnosis, controls = binding.read(args.alternative_diagnosis), binding.read(args.alternative_controls)
    if (controls["diagnosis_sha256"] != binding.sha(args.alternative_diagnosis)
            or controls["tested_alternative_module_sha256"] != binding.sha(forest.alternative.__file__)
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0):
        raise ValueError("adaptive partition controls changed independently tested alternative support")
    supports = [{
        "mode": "NEW-POSITIVE-SUPPORT", "reference": diagnosis["alternative_reference_DATA"],
        "inverse": diagnosis["alternative_exact_inverse_certificate"],
        "suggestion_point_turns": diagnosis["exact_point_turns"],
    }]
    neighborhood = next(item for item in controls["actual_point_neighborhoods"]
                        if item["exact_alternative_support_bound"][
                            "radius_conditional_whole_angle_box_excluded"])
    row = {**diagnosis["actual_source_closed_box"],
           "sharp_lower": neighborhood["closed_lower"], "sharp_upper": neighborhood["closed_upper"]}
    # Proper source SUBBOX only, deliberately not the actual whole source row.
    leaf = [{"kind": "ALTERNATIVE-ENERGY", "support_index": 0}]
    result, pending, ledger = forest.replay(original, kernel, arcs, row, leaf, supports)
    if (pending or result["counts"]["ALTERNATIVE-ENERGY"] != 1
            or not result["arithmetic_entire_root_strictly_empty"]
            or neighborhood["proper_subbox_only_NOT_entire_source_root"] is not True):
        raise AssertionError("new pure adaptive mode did not reconstruct the real strict proper subbox")
    full_row = diagnosis["actual_source_closed_box"]
    lower, upper = forest.tighten(original["matrix"], full_row["sharp_lower"], full_row["sharp_upper"])
    axis = next(axis for axis, (a, b) in enumerate(zip(lower, upper)) if a < b)
    nodes = [{"kind": "SPLIT", "axis": axis, "mid": str((lower[axis]+upper[axis])/2),
              "children": [1, 2]}, {"kind": "OPEN"}, {"kind": "OPEN"}]
    dfs = forest.partition(original["matrix"], full_row, nodes, forest.tighten, False)
    bfs = forest.partition(original["matrix"], full_row, nodes, forest.independently_contract, True)
    if dfs != bfs or len(dfs) != 2:
        raise AssertionError("adaptive split independent exact closed half domains disagree")
    negative = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid adaptive support mode/partition accepted: " + label)

    def changed_partition(mutation):
        bad = deepcopy(nodes)
        mutation(bad)
        forest.partition(original["matrix"], full_row, bad, forest.independently_contract, True)

    reject("adaptive-lost-shared-closed-half", lambda: changed_partition(
        lambda bad: bad[0].update(children=[1])))
    reject("adaptive-two-closed-halves-identified", lambda: changed_partition(
        lambda bad: bad[0].update(children=[1, 1])))
    reject("adaptive-unreachable-hidden-node", lambda: changed_partition(
        lambda bad: bad.append({"kind": "OPEN"})))
    reject("adaptive-boolean-child-index", lambda: changed_partition(
        lambda bad: bad[0].update(children=[True, 2])))
    reject("adaptive-unknown-mode", lambda: changed_partition(
        lambda bad: bad.__setitem__(1, {"kind": "UNPROVED-NEW-SUPPORT"})))
    reject("adaptive-nonempty-region-called-EMPTY", lambda: changed_partition(
        lambda bad: bad.__setitem__(1, {"kind": "EMPTY"})))
    reject("adaptive-split-has-unknown-proof-field", lambda: changed_partition(
        lambda bad: bad[0].update(fake_payment=True)))

    def changed_support(mutation):
        bad = deepcopy(supports)
        mutation(bad)
        forest.support_gate(original, bad)

    reject("adaptive-negative-original-rod-weight", lambda: changed_support(
        lambda bad: bad[0]["reference"]["weight_numerators"].__setitem__(0, "-1")))
    reject("adaptive-original-rod-edge-changed", lambda: changed_support(
        lambda bad: bad[0]["reference"]["edges"].pop()))
    reject("adaptive-new-support-relabelled-as-original-fixed", lambda: changed_support(
        lambda bad: bad[0].update(mode="ORIGINAL-FIXED-SUPPORT")))
    reject("adaptive-original-fixed-weights-substituted-for-new-support", lambda: changed_support(
        lambda bad: bad[0]["reference"].update(
            weight_numerators=original["reference"]["weight_numerators"])))
    reject("adaptive-support-hides-an-unknown-proof-field", lambda: changed_support(
        lambda bad: bad[0].update(forged_geometry_acceptance=True)))
    reject("adaptive-boolean-positive-support-index", lambda: forest.replay(
        original, kernel, arcs, row, [{"kind": "ALTERNATIVE-ENERGY", "support_index": False}], supports))
    reject("adaptive-out-of-range-positive-support-index", lambda: forest.replay(
        original, kernel, arcs, row, [{"kind": "ALTERNATIVE-ENERGY", "support_index": 1}], supports))
    reject("adaptive-strong-new-support-replaced-by-inconclusive-original-fixed", lambda: forest.replay(
        original, kernel, arcs, row, [{"kind": "ORIGINAL-ENERGY"}], supports))
    tiny = [pair for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    for fresh in forest.support_gate(original, supports):
        positive = forest.direct_bound(
            fresh, [a for a, _ in tiny], [b for _, b in tiny], original["radius"], arcs)
        if positive["radius_conditional_whole_angle_box_excluded"]:
            raise AssertionError("new adaptive positive support excludes the feasible tiny candidate")
    report = {
        "schema": "N26-adaptive-original-rod-support-partition-arithmetic-controls-v1",
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "actual_strict_proper_neighborhood_reconstructed_NOT_entire_source_root": True,
        "actual_strict_proper_neighborhood_result": result,
        "synthetic_full_source_partition_shared_closed_halves_reconstructed": True,
        "synthetic_and_actual_invalid_arithmetic_controls_rejected": negative,
        "new_support_feasible_tiny_candidate_NOT_excluded": True,
        "complete_latest_source_model_history_geometry_gate_NOT_executed": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "diagnosis_sha256": binding.sha(args.alternative_diagnosis),
        "alternative_controls_sha256": binding.sha(args.alternative_controls),
        "tested_forest_module_sha256": binding.sha(forest.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "adaptive_support_partition_arithmetic_controls_completed": True,
        "invalid_arithmetic_controls": len(negative), "verified": False,
        "new_geometric_payments": 0, "actual_proper_subbox_NOT_whole_root": True}), flush=True)


if __name__ == "__main__":
    main()
