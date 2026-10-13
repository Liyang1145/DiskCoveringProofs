"""Own independent entire grown successor controls, not a relabelled test."""

from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_checked_root28_grown_full134rod_intersections as producer
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-v8-grown-full134rod-intersection-forest-controls-v1"
mixed = producer.mixed
domain_checker = producer.independent_domains


def record_scope_gate(record, latest, row, args, digests, layer, table, regions, evidence):
    if (record["schema"] != producer.SCHEMA
            or record["executed_producer_sha256"] != binding.sha(producer.__file__)
            or record["source_OPEN_index"] != 28 or record["actual_source_closed_box"] != row
            or record["source_file_sha256"] != latest["source_file_sha256"]
            or record["actual_current_audit_sha256"] != digests[args.current_audit]
            or record["actual_latest_candidate_layer_identity_only"] != layer
            or record["actual_checked_latest_v8_forest_sha256"] != digests[args.latest_forest]
            or record["actual_checked_latest_v8_controls_sha256"] != digests[args.latest_controls]
            or record["all_input_sha256"] != {linux(path): digest for path, digest in digests.items()}
            or record["old_stress_origins_are_region_DATA_ONLY_not_the_latest_forest_seed"] is not True
            or record["narrow_unexecuted_interface_NOT_relabelled_as_this_distinct_own_producer"] is not True
            or record["grown_region_evidence_and_fresh_selection"] != evidence
            or record["checked_grown_source_root_regions_DATA_only"] != regions
            or record["full134rod_supports"] != table
            or record["all_old_nonOPEN_nodes_original_LOCAL_support_prefixes_and_ledgers_preserved"] is not True
            or record["both_closed_halves_shared_boundaries_and_all_remainders_retained"] is not True
            or record["actual_successor_independent_arithmetic_controls_still_required"] is not True
            or record["complete_latest_source_model_history_geometry_admission_NOT_performed"] is not True
            or type(record["max_fresh_strict_targets"]) is not int
            or not 1 <= record["max_fresh_strict_targets"] <= 4096
            or len(record["fresh_actual_latest_OPEN_intersection_targets"]) > record["max_fresh_strict_targets"]
            or record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["global_lower_bound_proved"] is not False
            or record["global_optimality_proved"] is not False or record["n27_started"] is not False):
        raise ValueError("grown successor changed its own executor, actual latest lineage or unpaid scope")
    for module in producer.modules():
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("grown successor executed arithmetic changed")
    retained = mixed.retention_gate(latest, record)
    if record["old_latest_nodes_supports_and_strict_ledgers_retained"] != list(retained):
        raise ValueError("grown successor reported retention does not match actual old proof history")
    return retained


def reconstruct(original, kernel, arcs, row, latest, record, kernels, regions):
    domains, parents = domain_checker.all_domains(original, row, record["nodes"])
    checked = domain_checker.target_gate(record, latest, regions, domains, parents)
    result, pending, ledger = mixed.replay(
        original, kernel, arcs, row, record["nodes"],
        record["alternative_supports"], record["full134rod_supports"])
    if (result != record["arithmetic_result"] or pending != record["pending_closed_leaf_boxes"]
            or ledger != record["arithmetic_ledger"]):
        raise ValueError("grown successor failed independent entire actual partition/ledger reconstruction")
    for target, node, leaf in checked:
        fresh = domain_checker.independent_energy.arithmetic_control(
            original, kernels[node["full_support_index"]], leaf, {
                "NEW_correlated_quadratic_certificate": node["certificate"],
                "NEW_correlated_exact_closed_leaf_result": target["fresh_exact_whole_closed_target_result"],
            }, arcs)
        if fresh["arithmetic_strict_target_test_passed"] is not True:
            raise ValueError("grown successor target lacks independent strict entire closed-region arithmetic")
    return result, pending, ledger, checked, domains, parents


def rejection_controls(original, row, latest, record, args, digests, layer, table, regions,
                       evidence, domains, parents, checked):
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual grown successor accepted: "+label)

    def bad_scope(label, mutation):
        bad = deepcopy(record)
        mutation(bad)
        reject(label, lambda: record_scope_gate(
            bad, latest, row, args, digests, layer, table, regions, evidence))

    for label, mutation in (
        ("grown-successor-OLD-v7-used-as-latest-v8", lambda bad: bad.update(
            actual_checked_latest_v8_forest_sha256=digests[args.seed])),
        ("grown-successor-fixture-controls-used-as-latest", lambda bad: bad.update(
            actual_checked_latest_v8_controls_sha256=digests[args.mode_controls])),
        ("grown-successor-old-origin-promoted-to-current-forest-seed", lambda bad: bad.update(
            old_stress_origins_are_region_DATA_ONLY_not_the_latest_forest_seed=False)),
        ("grown-successor-narrow-producer-relabelled", lambda bad: bad.update(
            executed_producer_sha256=binding.sha(producer.ancestor_interface.__file__))),
        ("grown-successor-current-audit-binding-changed", lambda bad: bad.update(actual_current_audit_sha256="0"*64)),
        ("grown-successor-independent-region-controls-lost", lambda bad: bad[
            "grown_region_evidence_and_fresh_selection"].update(grown_independent_controls_sha256="0"*64)),
        ("grown-successor-unchecked-wide-region-substituted", lambda bad: bad[
            "checked_grown_source_root_regions_DATA_only"][0]["upper"].__setitem__(0, "100")),
        ("grown-successor-old92support-prefix-reset", lambda bad: bad["alternative_supports"].pop(0)),
        ("grown-successor-full134rod-support-prefix-lost", lambda bad: bad["full134rod_supports"].pop()),
        ("grown-successor-old-strict-ledger-reset", lambda bad: bad["arithmetic_ledger"].pop(0)),
        ("grown-successor-closed-remainders-discarded", lambda bad: bad.update(
            both_closed_halves_shared_boundaries_and_all_remainders_retained=False)),
        ("grown-successor-arithmetic-paid-as-current-geometry", lambda bad: bad.update(verified=True, new_geometric_payments=1)),
        ("grown-successor-proper-subsets-paid-as-whole-root", lambda bad: bad.update(candidate_whole_roots_removed=1)),
        ("grown-successor-entire-source-history-admission-laundered", lambda bad: bad.update(
            complete_latest_source_model_history_geometry_admission_NOT_performed=False)),
        ("grown-successor-global-optimality-laundered", lambda bad: bad.update(global_optimality_proved=True)),
    ):
        bad_scope(label, mutation)
    old_nonopen = next(index for index, node in enumerate(latest["nodes"]) if node["kind"] != "OPEN")
    bad_scope("grown-successor-latest-nonOPEN-node-reset", lambda bad: bad["nodes"].__setitem__(old_nonopen, {"kind": "OPEN"}))
    for label, mutation in (
        ("grown-successor-unreachable-hidden-remainder", lambda bad: bad.append({"kind": "OPEN"})),
        ("grown-successor-one-closed-root-half-lost", lambda bad: bad[0].update(children=bad[0]["children"][:1])),
        ("grown-successor-closed-root-halves-identified", lambda bad: bad[0].update(children=[bad[0]["children"][0]]*2)),
    ):
        bad = deepcopy(record["nodes"])
        mutation(bad)
        reject(label, lambda bad=bad: domain_checker.all_domains(original, row, bad))
    if checked:
        for label, mutation in (
            ("grown-successor-entire-target-domain-escaped", lambda bad: bad[
                "fresh_actual_latest_OPEN_intersection_targets"][0]["actual_closed_lower"].__setitem__(0, "-100")),
            ("grown-successor-actual-OPEN-source-laundered-as-LOCAL", lambda bad: bad[
                "fresh_actual_latest_OPEN_intersection_targets"][0]["source_actual_OPEN_leaf"].update(kind="LOCAL")),
            ("grown-successor-NEW-target-summary-omitted", lambda bad: bad[
                "fresh_actual_latest_OPEN_intersection_targets"].pop()),
            ("grown-successor-NEW-target-summary-repeated", lambda bad: bad[
                "fresh_actual_latest_OPEN_intersection_targets"].append(deepcopy(
                    bad["fresh_actual_latest_OPEN_intersection_targets"][0]))),
        ):
            bad = deepcopy(record)
            mutation(bad)
            reject(label, lambda bad=bad: domain_checker.target_gate(bad, latest, regions, domains, parents))
    return rejected


def main():
    args = producer.arguments(test=True)
    if args.report.exists():
        raise FileExistsError(args.report)
    executed_digest = binding.sha(__file__)
    original, kernel, latest, row, arcs, digests, layer, table, kernels, regions, evidence = producer.data_gate(args)
    record, digest = binding.read(args.diagnosis), binding.sha(args.diagnosis)
    retained = record_scope_gate(record, latest, row, args, digests, layer, table, regions, evidence)
    result, pending, ledger, checked, domains, parents = reconstruct(
        original, kernel, arcs, row, latest, record, kernels, regions)
    rejected = rejection_controls(
        original, row, latest, record, args, digests, layer, table, regions,
        evidence, domains, parents, checked)
    producer.unchanged_inputs(
        args, {**digests, args.diagnosis: digest}, latest, record["modules"],
        binding.sha(producer.__file__))
    if binding.sha(__file__) != executed_digest:
        raise ValueError("grown successor independent tester changed during execution")
    report = {
        "schema": SCHEMA, "verified": False, "diagnosis_sha256": digest,
        "actual_checked_latest_v8_forest_sha256": digests[args.latest_forest],
        "actual_checked_latest_v8_controls_sha256": digests[args.latest_controls],
        "grown_region_evidence_and_fresh_selection": evidence,
        "source_file_sha256": latest["source_file_sha256"],
        "actual_latest_nodes_supports_and_strict_ledgers_retained": list(retained),
        "entire_old_and_new_actual_closed_partitions_and_exact_ledgers_reconstructed": True,
        "independent_BFS_all_nodes_and_actual_latest_OPEN_parent_walks_checked": True,
        "fresh_grown_full134rod_strict_whole_closed_targets_independently_checked": len(checked),
        "independent_sine_square_correlated_completion_and_secant_checks": 3*len(checked),
        "both_closed_halves_shared_boundaries_and_all_remainders_reconstructed": True,
        "actual_latest_lineage_grown_region_subset_history_and_payment_guards_rejected": rejected,
        "latest_arithmetic_result": result, "retained_OPEN_leaves": len(pending),
        "entire_root_arithmetic_cover_completed": not pending,
        "arithmetic_only_NOT_complete_latest_source_model_history_geometry_acceptance": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": executed_digest,
        "tested_own_producer_sha256": binding.sha(producer.__file__),
        "tested_modules": {Path(module.__file__).name: binding.sha(module.__file__)
                           for module in producer.modules()},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_latest_v8_grown_full134rod_successor_independent_controls_completed": True,
        "fresh_strict_targets": len(checked), "retained_OPEN_leaves": len(pending),
        "actual_rejections": len(rejected), "verified": False, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
