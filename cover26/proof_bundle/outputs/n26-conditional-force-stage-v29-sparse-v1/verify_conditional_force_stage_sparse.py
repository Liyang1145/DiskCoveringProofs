"""Sparse-event stage acceptance with unchanged exact geometry semantics.

Absent current angular trees do not suppress rejection controls. A sealed,
genuinely recorded ancestor tree is replayed as a zero-payment regression.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_sparse_stage_controls as angular_control
import verify_conditional_force_stage as exact


SCHEMA = "N26-successive-radius-conditional-sparse-stage-acceptance-v2"
CHECKER = "verify_conditional_force_stage_sparse.py"


def input_gate(folder, area_folder):
    values = exact.input_gate(folder, area_folder)
    manifest = values[0]
    policy = manifest["sparse_event_control_policy"]
    if (
        policy["schema"] != "N26-sparse-stage-control-policy-v1"
        or policy["semantic_replayer_file"] != "verify_conditional_force_stage.py"
        or policy["acceptance_checker_file"] != CHECKER
        or policy["angular_control_is_not_a_new_stage_payment"] is not True
        or exact.sha(exact.__file__) != manifest["copied_files"][
            "verify_conditional_force_stage.py"]
        or exact.sha(angular_control.__file__) != manifest["copied_files"][
            "n26_sparse_stage_controls.py"]
        or exact.sha(__file__) != manifest["copied_files"][CHECKER]
    ):
        raise ValueError("sparse stage changed exact semantics, executor or control scope")
    fixture, paths = angular_control.select_control(folder)
    if exact.read(folder / "ANGULAR-REGRESSION-CONTROL.json") != fixture:
        raise ValueError("sparse angular control does not reconstruct from its actual source ancestry")
    regression = exact.read(folder / "CONTROL-SELECTOR-REGRESSION.json")
    if (
        regression["tested_control_helper_sha256"] != exact.sha(angular_control.__file__)
        or regression["executed_test_sha256"] != manifest["copied_files"][
            "test_sparse_stage_controls.py"]
        or regression["zero_current_force_tree_events_are_a_supported_structural_case"] is not True
        or regression["zero_split_force_tree_events_are_a_supported_structural_case"] is not True
        or regression["non_tree_events_never_used_as_angular_controls"] is not True
        or regression["synthetic_selector_only_not_an_actual_geometry_replay"] is not True
        or type(regression["new_geometric_payments"]) is not int
        or regression["new_geometric_payments"] != 0
    ):
        raise ValueError("sparse selector controls changed or were promoted to geometry")
    values[-1].extend(paths)
    return values, fixture


def verify(folder, area_folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values, fixture = input_gate(folder, area_folder)
    manifest, source, accepted, basis, old, multi, native, trace, inventory = values
    digests = {exact.combinatorics.linux(path): exact.sha(path) for path in inventory}
    candidate = exact.read(folder / "CANDIDATE-PATH.json")
    radius = F(manifest["radius_upper"])
    arcs = exact.force.load_trig(folder)[0]
    frontier, ledger, margins = exact.replay(
        folder, source, old, multi, native, trace, arcs, radius, candidate)
    controls = exact.base.regular_ring_controls(arcs)
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid sparse conditional stage accepted: " + label)

    bad = deepcopy(manifest)
    bad["radius_scope"] = "unconditional-original-U"
    reject("conditional-frontier-promoted-to-unconditional-U",
           lambda: exact.scope_gate(bad, accepted, source, basis))
    bad = deepcopy(manifest)
    bad["radius_upper"] = str(exact.force.U)
    reject("same-root-radius-endpoint-replaced-by-screen-threshold",
           lambda: exact.scope_gate(bad, accepted, source, basis))
    bad_source = deepcopy(source)
    bad_source["families"][0]["pending_subtrees"] += 1
    reject("conditional-source-family-changed",
           lambda: exact.scope_gate(manifest, accepted, bad_source, basis))
    bad = deepcopy(trace)
    bad["pending_prefixes"]["14"].pop()
    reject("lost-conditional-pending-sibling",
           lambda: exact.replay(folder, source, old, multi, native, bad, arcs, radius, candidate))
    bad_native = deepcopy(native)
    bad_native["runs"].pop()
    reject("missing-conditional-native-event",
           lambda: exact.replay(folder, source, old, multi, bad_native, trace, arcs, radius, candidate))
    bad = deepcopy(trace)
    next(row for row in bad["events"] if row["kind"] == "split")["all_child_count"] += 1
    reject("changed-conditional-complete-sibling-count",
           lambda: exact.replay(folder, source, old, multi, native, bad, arcs, radius, candidate))
    positive_tree, angular_negatives = angular_control.check_control(fixture, arcs)
    negatives.extend(angular_negatives)
    bad_candidate = deepcopy(candidate)
    bad_candidate["prefix"] = bad_candidate["prefix"][:-1]
    reject("candidate-full-terminal-replaced-by-ancestor",
           lambda: exact.replay(folder, source, old, multi, native, trace, arcs, radius, bad_candidate))
    if len(negatives) != 9:
        raise ValueError("sparse stage omitted an original rejection control")

    control_receipt = {
        "schema": "N26-replayed-sparse-stage-angular-control-v1",
        "fixture": fixture, "positive_tree_replay": positive_tree,
        "angular_negative_controls_rejected": angular_negatives,
        "new_geometric_payments_from_this_control": 0,
        "control_nodes_not_counted_as_current_stage_tree_nodes": True,
    }
    for name, data in (
        ("FRONTIER.json", frontier), ("LOWER-LEDGER.json", ledger),
        ("ANGULAR-CONTROL-REPLAY.json", control_receipt),
    ):
        exact.area.base.publish_or_match(folder / name, data)
    kinds = {kind: sum(row[kind] for row in frontier["families"]) for kind in exact.base.KINDS}
    files = [
        "MANIFEST.json", "TRACE.json", "NATIVE-VERIFIED.json", "FRONTIER.json",
        "LOWER-LEDGER.json", "ANGULAR-CONTROL-REPLAY.json", *manifest["copied_files"],
    ]
    report = {
        "schema": SCHEMA, "verified": True, "radius_scope": exact.SCOPE,
        "radius_upper": str(radius), "r_strict_interval": basis["r_strict_interval"],
        "screen_radius_threshold": str(exact.force.U),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "radius_basis_acceptance_sha256": manifest["radius_basis_acceptance_sha256"],
        "source_conditional_pending_subtrees": len(source["pending_states"]),
        "native_events_independently_replayed": len(trace["events"]), "event_counts": kinds,
        "new_strict_radius_conditional_whole_transport_subtrees_excluded":
            kinds["force"] + kinds["force_tree"] + kinds["area"],
        "new_combinatorially_empty_subtrees": kinds["empty"],
        "complete_angle_tree_nodes": sum(row["nodes"] for row in ledger if row["kind"] == "force_tree"),
        "all_incoming_angle_boxes_covered": True,
        "minimum_strict_force_margin_above_conservative_U": str(min(margins)) if margins else None,
        "U_force_area_and_screen_bounds_used_only_as_sufficient_conditions_on_Rstar_source": True,
        "inherited_source_is_unconditional_at_U": False,
        "feasible_regular_ring_regression_controls": controls,
        "families": frontier["families"],
        "pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "known_candidate_unique_complete_34_face_terminal": candidate["prefix"],
        "older_forests_and_original_native_queues_preserved": True,
        "original_U_frontier_nodes_removed_by_this_conditional_bundle": 0,
        "angular_regression_control_from_current_stage": fixture["from_current_stage"],
        "angular_regression_control_acceptance_sha256": fixture["control_acceptance_sha256"],
        "angular_regression_positive_tree_nodes": positive_tree["nodes"],
        "angular_regression_control_new_geometric_payments": 0,
        "original_exact_semantic_replayer_sha256": exact.sha(exact.__file__),
        "unrestricted_reduction_final_joint_acceptance": False, "formal_machine_geometry_proof": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "negative_controls_rejected": negatives,
        "files": {name: exact.sha(folder / name) for name in dict.fromkeys(files)},
        "source_files": digests, "executed_checker_file": CHECKER,
        "executed_checker_sha256": exact.sha(__file__),
    }
    if report["executed_checker_sha256"] != report["files"][CHECKER]:
        raise ValueError("sparse stage did not execute its own sealed acceptance checker")
    for text, digest in digests.items():
        if exact.sha(text) != digest:
            raise ValueError("sparse stage historical/control dependency changed")
    for name, digest in manifest["copied_files"].items():
        if exact.sha(folder / name) != digest:
            raise ValueError("sparse stage sealed input changed")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "source_files")}, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser()
    for name in ("input", "area-bundle", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    verify(args.input, args.area_bundle, args.report)


if __name__ == "__main__":
    main()
