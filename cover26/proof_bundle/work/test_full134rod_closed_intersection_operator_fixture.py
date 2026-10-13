"""Actual OLD v7 operator fixture, expressly NOT a newest-v8 successor."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import n26_checked_full134rod_closed_intersections as operator
import probe_balanced_full134rod_neighborhoods as inputs
import test_balanced_full134rod_neighborhoods as neighborhood_controls
import test_checked_root28_full134rod_intersections as independent
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-full134rod-closed-intersection-operator-OLD-fixture-controls-v1"
mixed = operator.mixed


def main():
    parser = argparse.ArgumentParser()
    for name in (
        "resource", "resource-replay", "current-audit", "source", "seed", "seed-controls",
        "ancestor-seed", "old-full-diagnosis", "old-full-controls", "prior-diagnosis",
        "prior-controls", "correlated-diagnosis", "correlated-controls",
        "old-minimax-diagnosis", "old-minimax-controls", "balanced-diagnosis",
        "balanced-controls", "neighborhood-diagnosis", "neighborhood-controls", "report",
    ):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, row, arcs, digests, _, stresses = inputs.data_gate(args)
    diagnosis, controls = binding.read(args.neighborhood_diagnosis), binding.read(args.neighborhood_controls)
    for path in (args.neighborhood_diagnosis, args.neighborhood_controls):
        digests[path] = binding.sha(path)
    neighborhood_controls.payment_scope_gate(diagnosis)
    if (diagnosis["schema"] != inputs.SCHEMA
            or diagnosis["executed_probe_sha256"] != binding.sha(inputs.__file__)
            or diagnosis["checked_v7_forest_sha256"] != digests[args.seed]
            or controls["schema"] != neighborhood_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(neighborhood_controls.__file__)
            or controls["diagnosis_sha256"] != digests[args.neighborhood_diagnosis]
            or len(controls["actual_closed_subset_and_no_payment_rejection_controls_passed"]) != 8):
        raise ValueError("OLD operator fixture lacks actual proper-region controls")
    table = [{
        "mode": mixed.SUPPORT_MODE,
        "kernel_certificate": item["NEW_full134rod_stress_kernel_certificate"],
        "suggestion_point_turns": item["actual_fixed_feasible_anchor_turns"],
    } for item in stresses["results"]]
    kernels = mixed.full_support_gate(model, table)
    old = {item["actual_checked_v7_OPEN_leaf"]["index"]: (index, item)
           for index, item in enumerate(stresses["results"])}
    regions = []
    for item in diagnosis["results"]:
        support_index, old_item = old[item["actual_checked_v7_OPEN_leaf"]["index"]]
        if item["NEW_full134rod_stress_kernel_certificate"] != table[support_index]["kernel_certificate"]:
            raise ValueError("OLD operator fixture changed a proper-region kernel")
        trial = next(trial for trial in item["trials"] if trial["requested_closed_half_width"] == "1/1000")
        target = neighborhood_controls.neighborhood_gate(original, old_item, trial)
        regions.append({**target, "full_support_index": support_index,
                        "certificate": deepcopy(trial["NEW_stress_correlated_certificate"])})
    nodes, targets, decisions, scans = operator.refine(
        original, arcs, row, seed["nodes"], kernels, regions, 64)
    record = {"nodes": nodes, "alternative_supports": seed["alternative_supports"],
              "full134rod_supports": table,
              "fresh_actual_latest_OPEN_intersection_targets": targets,
              "fresh_closed_split_decisions": decisions}
    original_kernel = inputs.stress_producer.old.prior_producer.previous.producer.codec.gate(
        binding.read(args.resource / "CONTEXT.json")["typed_context"])["original_kernel"]
    result, pending, ledger = mixed.replay(
        original, original_kernel, arcs, row, nodes, seed["alternative_supports"], table)
    record["arithmetic_ledger"] = ledger
    retained = mixed.retention_gate(seed, record)
    domains, parents = independent.all_domains(original, row, nodes)
    checked = independent.target_gate(record, seed, regions, domains, parents)
    if not checked or not pending:
        raise ValueError("OLD proper-region fixture omitted strict targets or erased all remainders")
    for target, node, leaf in checked:
        independent.independent_energy.arithmetic_control(
            original, kernels[node["full_support_index"]], leaf, {
                "NEW_correlated_quadratic_certificate": node["certificate"],
                "NEW_correlated_exact_closed_leaf_result": target["fresh_exact_whole_closed_target_result"],
            }, arcs)
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid OLD operator fixture accepted: "+label)

    reject("operator-boolean-target-budget", lambda: operator.refine(
        original, arcs, row, seed["nodes"], kernels, regions, True))
    reject("operator-zero-target-budget", lambda: operator.refine(
        original, arcs, row, seed["nodes"], kernels, regions, 0))
    leaf = next(leaf for leaf in seed["pending_closed_leaf_boxes"])
    reject("operator-closed-region-coordinate-omitted", lambda: operator.intersection(
        original["matrix"], leaf, regions[0]["lower"][:-1], regions[0]["upper"]))
    reject("operator-reversed-closed-region", lambda: operator.intersection(
        original["matrix"], leaf, ["100"]*15, ["-100"]*15))
    for label, mutation in (
        ("operator-hidden-unreachable-remainder", lambda bad: bad["nodes"].append({"kind": "OPEN"})),
        ("operator-one-closed-half-lost", lambda bad: bad["nodes"][0].update(
            children=bad["nodes"][0]["children"][:1])),
    ):
        bad = deepcopy(record)
        mutation(bad)
        reject(label, lambda bad=bad: independent.all_domains(original, row, bad["nodes"]))
    for label, mutation in (
        ("operator-paid-region-summary-omitted", lambda bad: bad[
            "fresh_actual_latest_OPEN_intersection_targets"].pop()),
        ("operator-actual-target-domain-escaped", lambda bad: bad[
            "fresh_actual_latest_OPEN_intersection_targets"][0]["actual_closed_upper"].__setitem__(0, "100")),
    ):
        bad = deepcopy(record)
        mutation(bad)
        reject(label, lambda bad=bad: independent.target_gate(bad, seed, regions, domains, parents))
    inputs.stress_producer.old.prior_producer.previous.producer.unchanged_inputs(args, digests, seed)
    report = {
        "schema": SCHEMA, "verified": False, "seed_OLD_v7_sha256": digests[args.seed],
        "old_v7_nodes_supports_and_strict_ledgers_retained": list(retained),
        "actual_OLD_fixture_strict_closed_intersections_independently_checked": len(checked),
        "actual_OLD_fixture_closed_splits": len(decisions),
        "all_actual_closed_shared_boundaries_and_OPEN_remainders_reconstructed": True,
        "independent_sine_square_secant_and_square_completion_checks": 3*len(checked),
        "actual_operator_rejection_controls_passed": rejected,
        "region_scans": scans, "remaining_OPEN_fixture_regions": len(pending),
        "fixture_NOT_latest_v8_successor_or_current_source_geometry_acceptance": True,
        "all_original_and_NEWEST_running_histories_UNMODIFIED": True,
        "source_file_sha256": seed["source_file_sha256"],
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_intersection_operator_sha256": binding.sha(operator.__file__),
        "tested_independent_domain_and_target_checker_sha256": binding.sha(independent.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "OLD_fixture_operator_independent_controls_completed": True,
        "strict_intersections": len(checked), "fresh_closed_splits": len(decisions),
        "remaining_OPEN_fixture_regions": len(pending), "actual_rejections": len(rejected),
        "NOT_actual_latest_v8_successor": True, "verified": False, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
