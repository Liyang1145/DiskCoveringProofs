"""Actual grown-region OLD-v7 operator fixture; NOT newest-v8 continuation."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_checked_root28_grown_full134rod_intersections as interface
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as resource_definition
import test_checked_root28_grown_full134rod_intersections as independent
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-grown-full134rod-intersection-OLD-forest-fixture-controls-v1"
mixed = interface.mixed


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "source", "seed", "seed-controls",
                 "grown-diagnosis", "grown-controls", "grown-selection-controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != resource_definition.RESOURCE_SHA
            or binding.sha(args.resource_replay) != resource_definition.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True):
        raise ValueError("grown OLD fixture changed the verified arithmetic model DATA")
    context = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])
    original, kernel = context["original"], context["original_kernel"]
    seed, controls = binding.read(args.seed), binding.read(args.seed_controls)
    previous = interface.ancestor_interface.latest_controls.producer.previous
    seed_digest = binding.sha(args.seed)
    if (seed["schema"] != previous.producer.SCHEMA
            or seed["executed_producer_sha256"] != binding.sha(previous.producer.__file__)
            or controls["schema"] != previous.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(previous.__file__)
            or controls["diagnosis_sha256"] != seed_digest
            or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
            or controls["both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed"] is not True
            or len(controls["actual_rejection_controls_passed"]) != 20
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0):
        raise ValueError("grown OLD fixture lacks the actual checked preserved v7 forest")
    accepted = binding.read(args.source / "VERIFIED.json")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest or accepted["files"][name] != digest:
            raise ValueError("grown OLD fixture changed actual source/model/history DATA")
    diagnosis, region_controls, selection_controls = (
        binding.read(args.grown_diagnosis), binding.read(args.grown_controls),
        binding.read(args.grown_selection_controls),
    )
    digests = {path: binding.sha(path) for path in (
        args.seed, args.seed_controls, args.grown_diagnosis, args.grown_controls,
        args.grown_selection_controls, args.resource / "VERIFIED.json",
        args.resource_replay, args.source / "VERIFIED.json",
    )}
    if (diagnosis["executed_probe_sha256"] != binding.sha(interface.region_producer.__file__)
            or diagnosis["explicit_OLD_v7_stress_origin_forest_sha256"] != seed_digest
            or diagnosis["source_file_sha256"] != seed["source_file_sha256"]
            or region_controls["schema"] != interface.region_controls.SCHEMA
            or region_controls["executed_test_sha256"] != binding.sha(interface.region_controls.__file__)
            or region_controls["diagnosis_sha256"] != digests[args.grown_diagnosis]
            or len(region_controls["actual_root_subset_source_history_and_zero_payment_guards_rejected"]) != 10
            or selection_controls["executed_test_sha256"] != binding.sha(interface.selection_controls.__file__)
            or selection_controls["tested_pure_selection_module_sha256"] != binding.sha(interface.selection.__file__)
            or selection_controls["diagnosis_sha256"] != digests[args.grown_diagnosis]
            or selection_controls["actual_grown_region_controls_sha256"] != digests[args.grown_controls]
            or len(selection_controls["actual_selection_scope_bound_and_false_strictness_controls_rejected"]) != 8):
        raise ValueError("grown OLD fixture changed actual region/selection evidence")
    row = next(row for row in binding.read(args.source / "PENDING-ANGLES.json") if row["index"] == 28)
    if row != diagnosis["actual_source_closed_box"] or row != seed["actual_source_closed_box"]:
        raise ValueError("grown OLD fixture changed the actual entire source root")
    arcs = binding.force.load_trig(args.resource)[0]
    prior_result, prior_pending, prior_ledger = mixed.old.replay(
        original, kernel, arcs, row, seed["nodes"], seed["alternative_supports"])
    if (prior_result != seed["arithmetic_result"] or prior_pending != seed["pending_closed_leaf_boxes"]
            or prior_ledger != seed["arithmetic_ledger"]):
        raise ValueError("grown OLD fixture failed fresh entire prior partition/ledger replay")
    table = [{
        "mode": mixed.SUPPORT_MODE,
        "kernel_certificate": item["NEW_full134rod_stress_kernel_certificate"],
        "suggestion_point_turns": item["actual_feasible_reference_turns"],
    } for item in diagnosis["results"]]
    model = mixed.model_gate(original)
    kernels = mixed.full_support_gate(model, table)
    regions, audit = interface.selection.select(original, arcs, row, table, diagnosis)
    if (regions != selection_controls["actual_selected_widest_strict_closed_regions"]
            or audit != selection_controls["all_root_clipped_region_results_freshly_reconstructed"]):
        raise ValueError("grown OLD fixture cached selection failed fresh reconstruction")
    nodes, targets, decisions, scans = interface.ancestor_interface.intersections.refine(
        original, arcs, row, seed["nodes"], kernels, regions, 64)
    result, pending, ledger = mixed.replay(
        original, kernel, arcs, row, nodes, seed["alternative_supports"], table)
    fixture = {
        "nodes": nodes, "alternative_supports": seed["alternative_supports"],
        "full134rod_supports": table, "arithmetic_result": result,
        "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "fresh_actual_latest_OPEN_intersection_targets": targets,
        "fresh_closed_split_decisions": decisions,
    }
    retained = mixed.retention_gate(seed, fixture)
    _, _, _, checked, domains, parents = independent.reconstruct(
        original, kernel, arcs, row, seed, fixture, kernels, regions)
    if not checked or not pending:
        raise ValueError("grown proper-region OLD fixture omitted targets or erased all remainders")
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid grown OLD fixture accepted: "+label)

    for label, mutation in (
        ("grown-OLD-fixture-unreachable-remainder", lambda bad: bad["nodes"].append({"kind": "OPEN"})),
        ("grown-OLD-fixture-lost-closed-root-half", lambda bad: bad["nodes"][0].update(
            children=bad["nodes"][0]["children"][:1])),
        ("grown-OLD-fixture-closed-root-halves-identified", lambda bad: bad["nodes"][0].update(
            children=[bad["nodes"][0]["children"][0]]*2)),
    ):
        bad = deepcopy(fixture)
        mutation(bad)
        reject(label, lambda bad=bad: interface.independent_domains.all_domains(original, row, bad["nodes"]))
    for label, mutation in (
        ("grown-OLD-fixture-entire-target-escaped", lambda bad: bad[
            "fresh_actual_latest_OPEN_intersection_targets"][0]["actual_closed_upper"].__setitem__(0, "100")),
        ("grown-OLD-fixture-source-nonOPEN-laundered", lambda bad: bad[
            "fresh_actual_latest_OPEN_intersection_targets"][0]["source_actual_OPEN_leaf"].update(kind="LOCAL")),
        ("grown-OLD-fixture-target-omitted", lambda bad: bad[
            "fresh_actual_latest_OPEN_intersection_targets"].pop()),
        ("grown-OLD-fixture-target-repeated", lambda bad: bad[
            "fresh_actual_latest_OPEN_intersection_targets"].append(deepcopy(targets[0]))),
    ):
        bad = deepcopy(fixture)
        mutation(bad)
        reject(label, lambda bad=bad: interface.independent_domains.target_gate(
            bad, seed, regions, domains, parents))
    nonopen = next(index for index, node in enumerate(seed["nodes"]) if node["kind"] != "OPEN")
    bad = deepcopy(fixture)
    bad["nodes"][nonopen] = {"kind": "OPEN"}
    reject("grown-OLD-fixture-previous-nonOPEN-reset", lambda: mixed.retention_gate(seed, bad))
    # Real v7 producer metadata must remain inadmissible as a v8 seed. No
    # synthetic v8 acceptance is produced just to exercise the pure operator.
    reject("grown-OLD-fixture-used-as-latest-v8", lambda: interface.ancestor_interface.latest_gate(
        seed, controls, seed, args, digests))
    for path, digest in digests.items():
        if binding.sha(path) != digest:
            raise ValueError("grown OLD fixture actual evidence changed during tests")
    for name, digest in seed["source_file_sha256"].items():
        if binding.sha(args.source / name) != digest:
            raise ValueError("grown OLD fixture source/history DATA changed during tests")
    report = {
        "schema": SCHEMA, "verified": False, "actual_OLD_v7_forest_sha256": seed_digest,
        "actual_grown_diagnosis_sha256": digests[args.grown_diagnosis],
        "actual_grown_controls_sha256": digests[args.grown_controls],
        "actual_grown_selection_controls_sha256": digests[args.grown_selection_controls],
        "old_nodes_support_prefixes_and_strict_ledgers_retained": list(retained),
        "actual_grown_region_OLD_fixture_strict_targets_independently_checked": len(checked),
        "actual_grown_region_OLD_fixture_closed_splits": len(decisions),
        "remaining_OPEN_OLD_fixture_regions": len(pending), "region_scans": scans,
        "both_closed_halves_shared_boundaries_and_all_remainders_reconstructed": True,
        "independent_sine_square_secant_and_square_completion_checks": 3*len(checked),
        "actual_grown_operator_OLD_fixture_guards_rejected": rejected,
        "fixture_is_NOT_latest_v8_successor_or_current_source_history_geometry_acceptance": True,
        "all_original_and_NEWEST_running_histories_UNMODIFIED": True,
        "no_newest_successor_tree_or_geometry_payment_serialized_here": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_distinct_grown_interface_sha256": binding.sha(interface.__file__),
        "tested_own_independent_arithmetic_checker_sha256": binding.sha(independent.__file__),
        "tested_pure_operator_sha256": binding.sha(interface.ancestor_interface.intersections.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "grown_full134rod_operator_actual_OLD_fixture_controls_completed": True,
        "strict_targets": len(checked), "fresh_closed_splits": len(decisions),
        "remaining_OPEN_OLD_fixture_regions": len(pending),
        "actual_rejections": len(rejected), "NOT_latest_v8_successor": True,
        "verified": False, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
