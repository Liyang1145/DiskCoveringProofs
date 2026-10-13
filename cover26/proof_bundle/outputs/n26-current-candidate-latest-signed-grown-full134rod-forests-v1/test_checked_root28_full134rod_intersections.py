"""Independent latest-v8 ancestry, entire partitions and NEW134rod bounds."""

from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_checked_root28_full134rod_intersections as producer
import test_full134rod_correlated_support as independent_energy
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-v8-full134rod-intersection-forest-controls-v1"
mixed = producer.mixed


def all_domains(original, row, nodes):
    """Own breadth-first closed-domain walk, not the producer's cutter."""
    queue = [(0, list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"])))]
    domains, parents = {}, {}
    for index, lower, upper in queue:
        if index in domains or type(index) is not int or not 0 <= index < len(nodes):
            raise ValueError("independent mixed partition has repeated or hidden ownership")
        box = mixed.old.prior.prior.independently_contract(original["matrix"], lower, upper)
        domains[index] = box
        node = nodes[index]
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("independent mixed partition lost an exact EMPTY region")
            continue
        if node["kind"] != "SPLIT":
            continue
        axis, cut, children = node["axis"], F(node["mid"]), node["children"]
        if (type(axis) is not int or not 0 <= axis < len(box[0])
                or not box[0][axis] < cut < box[1][axis]
                or not isinstance(children, list) or len(children) != 2
                or children[0] == children[1]):
            raise ValueError("independent mixed split lost a strict closed shared boundary")
        left_upper, right_lower = list(box[1]), list(box[0])
        left_upper[axis], right_lower[axis] = cut, cut
        for child, lo, hi in (
            (children[0], list(box[0]), left_upper),
            (children[1], right_lower, list(box[1])),
        ):
            if type(child) is not int or child in parents or child == 0:
                raise ValueError("independent mixed split repeated a child")
            parents[child] = index
            queue.append((child, lo, hi))
    if set(domains) != set(range(len(nodes))):
        raise ValueError("independent mixed partition has an unreachable remainder")
    return domains, parents


def record_scope_gate(record, latest, row, args, digests, layer, table, regions):
    if (record["schema"] != producer.SCHEMA
            or record["executed_producer_sha256"] != binding.sha(producer.__file__)
            or record["source_OPEN_index"] != 28 or record["actual_source_closed_box"] != row
            or record["source_file_sha256"] != latest["source_file_sha256"]
            or record["actual_current_audit_sha256"] != digests[args.current_audit]
            or record["actual_latest_candidate_layer_identity_only"] != layer
            or record["actual_checked_latest_v8_forest_sha256"] != digests[args.latest_forest]
            or record["actual_checked_latest_v8_controls_sha256"] != digests[args.latest_controls]
            or record["all_input_sha256"] != {linux(path): digest for path, digest in digests.items()}
            or record["ancestor_v7_is_region_evidence_ONLY_not_the_continuation_seed"] is not True
            or record["full134rod_supports"] != table
            or record["checked_proper_ancestor_regions_DATA_only"] != regions
            or record["all_old_nonOPEN_nodes_and_original_LOCAL_preserved"] is not True
            or record["both_closed_halves_shared_boundaries_and_all_remainders_retained"] is not True
            or record["latest_arithmetic_successor_independent_controls_still_required"] is not True
            or record["complete_latest_source_model_history_geometry_admission_NOT_performed"] is not True
            or type(record["max_fresh_strict_targets"]) is not int
            or not 1 <= record["max_fresh_strict_targets"] <= 4096
            or len(record["fresh_actual_latest_OPEN_intersection_targets"]) > record["max_fresh_strict_targets"]
            or record["verified"] is not False or record["new_geometric_payments"] != 0
            or record["candidate_whole_roots_removed"] != 0
            or record["global_lower_bound_proved"] is not False
            or record["global_optimality_proved"] is not False or record["n27_started"] is not False):
        raise ValueError("mixed intersection successor changed actual latest lineage or unpaid scope")
    for module in producer.modules():
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("mixed intersection executed module changed")
    retained = mixed.retention_gate(latest, record)
    if record["old_latest_nodes_supports_and_strict_ledgers_retained"] != list(retained):
        raise ValueError("mixed intersection reported retention differs from actual latest history")
    return retained


def target_gate(record, latest, regions, domains, parents):
    full_indices = {index for index, node in enumerate(record["nodes"]) if node["kind"] == mixed.KIND}
    seen, checked = set(), []
    for target in record["fresh_actual_latest_OPEN_intersection_targets"]:
        index, region_index = target["actual_target_index"], target["region_index"]
        source = target["source_actual_OPEN_leaf"]
        source_index = source["index"]
        if (type(index) is not int or index not in full_indices or index in seen
                or type(region_index) is not int or not 0 <= region_index < len(regions)
                or type(source_index) is not int or source_index not in domains
                or source["kind"] != "OPEN" or domains[source_index] is None):
            raise ValueError("mixed intersection repeated or forged an actual OPEN source/target")
        seen.add(index)
        source_box, actual = domains[source_index], domains[index]
        if (source_box != (list(map(F, source["lower"])), list(map(F, source["upper"])))
                or actual != (list(map(F, target["actual_closed_lower"])),
                              list(map(F, target["actual_closed_upper"])))
                or type(target["whole_source_OPEN_leaf"]) is not bool
                or target["whole_source_OPEN_leaf"] != (source_box == actual)):
            raise ValueError("mixed intersection changed an actual entire closed source or target domain")
        # Walk the actual final parent tree independently. The source must
        # descend from a real OPEN region of the checked latest v8, never
        # from a paid ancestor or an old fixture with equal root count.
        cursor = source_index
        while cursor >= len(latest["nodes"]):
            cursor = parents[cursor]
        if latest["nodes"][cursor] != {"kind": "OPEN"}:
            raise ValueError("mixed intersection reset an actual latest nonOPEN ancestor")
        cursor = index
        while cursor != source_index:
            if cursor == 0 or cursor not in parents:
                raise ValueError("mixed target is not a descendant of its actual OPEN source")
            cursor = parents[cursor]
        region, node = regions[region_index], record["nodes"][index]
        if (target["full_support_index"] != region["full_support_index"]
                or node["full_support_index"] != region["full_support_index"]
                or node["certificate"] != region["certificate"]
                or any(not F(a) <= lo <= hi <= F(b) for a, b, lo, hi in zip(
                    region["lower"], region["upper"], *actual))
                or any(not lo <= a <= b <= hi for lo, hi, a, b in zip(*source_box, *actual))):
            raise ValueError("mixed intersection laundered a proper subset as a whole source payment")
        checked.append((target, node, {
            "index": index, "kind": mixed.KIND,
            "lower": list(map(str, actual[0])), "upper": list(map(str, actual[1])),
        }))
    if seen != full_indices:
        raise ValueError("mixed intersection omitted an actual new whole closed-leaf target")
    split_indices = {index for index, node in enumerate(record["nodes"])
                     if node["kind"] == "SPLIT"
                     and (index >= len(latest["nodes"]) or latest["nodes"][index]["kind"] == "OPEN")}
    seen_splits = set()
    for decision in record["fresh_closed_split_decisions"]:
        index = decision["old_OPEN_node"]
        if index in seen_splits or index not in split_indices:
            raise ValueError("mixed intersection repeated or forged a new closed split")
        seen_splits.add(index)
        node = record["nodes"][index]
        if (decision["axis"] != node["axis"] or decision["closed_shared_cut"] != node["mid"]
                or decision["children"] != node["children"]
                or type(decision["target_side"]) is not int or decision["target_side"] not in (0, 1)
                or decision["both_closed_halves_and_all_nonempty_remainders_retained"] is not True):
            raise ValueError("mixed intersection omitted a closed half, cut or OPEN remainder")
    if seen_splits != split_indices:
        raise ValueError("mixed intersection omitted an actual new closed split")
    return checked


def main():
    args = producer.arguments(test=True)
    if args.report.exists():
        raise FileExistsError(args.report)
    original, kernel, latest, row, arcs, digests, layer, table, kernels, regions = producer.data_gate(args)
    record, digest = binding.read(args.diagnosis), binding.sha(args.diagnosis)
    retained = record_scope_gate(record, latest, row, args, digests, layer, table, regions)
    domains, parents = all_domains(original, row, record["nodes"])
    checked = target_gate(record, latest, regions, domains, parents)
    result, pending, ledger = mixed.replay(
        original, kernel, arcs, row, record["nodes"],
        record["alternative_supports"], record["full134rod_supports"])
    if (result != record["arithmetic_result"] or pending != record["pending_closed_leaf_boxes"]
            or ledger != record["arithmetic_ledger"]):
        raise ValueError("mixed intersection entire actual partition/ledger did not reconstruct")
    for target, node, leaf in checked:
        fresh = independent_energy.arithmetic_control(
            original, kernels[node["full_support_index"]], leaf, {
                "NEW_correlated_quadratic_certificate": node["certificate"],
                "NEW_correlated_exact_closed_leaf_result": target["fresh_exact_whole_closed_target_result"],
            }, arcs)
        if fresh["arithmetic_strict_target_test_passed"] is not True:
            raise ValueError("independent whole closed intersection was not actually strict")
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual latest mixed intersection accepted: "+label)

    def bad_record(label, mutation):
        bad = deepcopy(record)
        mutation(bad)
        reject(label, lambda: record_scope_gate(
            bad, latest, row, args, digests, layer, table, regions))

    for label, mutation in (
        ("mixed-latest-v8-digest-replaced-by-old-v7", lambda bad: bad.update(
            actual_checked_latest_v8_forest_sha256=digests[args.seed])),
        ("mixed-latest-independent-controls-replaced-by-fixture", lambda bad: bad.update(
            actual_checked_latest_v8_controls_sha256=digests[args.mode_controls])),
        ("mixed-old-v7-promoted-to-continuation-seed", lambda bad: bad.update(
            ancestor_v7_is_region_evidence_ONLY_not_the_continuation_seed=False)),
        ("mixed-current-audit-binding-changed", lambda bad: bad.update(actual_current_audit_sha256="0"*64)),
        ("mixed-full134rod-support-table-truncated", lambda bad: bad["full134rod_supports"].pop()),
        ("mixed-old92support-prefix-truncated", lambda bad: bad["alternative_supports"].pop(0)),
        ("mixed-previous-paid-ledger-truncated", lambda bad: bad["arithmetic_ledger"].pop(0)),
        ("mixed-closed-remainders-declared-dispensable", lambda bad: bad.update(
            both_closed_halves_shared_boundaries_and_all_remainders_retained=False)),
        ("mixed-arithmetic-promoted-to-geometric-payment", lambda bad: bad.update(verified=True, new_geometric_payments=1)),
        ("mixed-proper-intersections-paid-as-whole-root", lambda bad: bad.update(candidate_whole_roots_removed=1)),
        ("mixed-entire-source-history-admission-laundered", lambda bad: bad.update(
            complete_latest_source_model_history_geometry_admission_NOT_performed=False)),
        ("mixed-global-optimality-laundered", lambda bad: bad.update(global_optimality_proved=True)),
    ):
        bad_record(label, mutation)
    old_nonopen = next(index for index, node in enumerate(latest["nodes"]) if node["kind"] != "OPEN")
    bad_record("mixed-latest-nonOPEN-proof-reset", lambda bad: bad["nodes"].__setitem__(old_nonopen, {"kind": "OPEN"}))
    bad_latest = binding.read(args.seed)
    reject("mixed-fixture-used-as-latest-v8-producer-output", lambda: producer.latest_gate(
        bad_latest, binding.read(args.latest_controls), bad_latest, args, digests))
    for label, mutation in (
        ("mixed-hidden-unreachable-remainder", lambda bad: bad.append({"kind": "OPEN"})),
        ("mixed-one-closed-root-half-lost", lambda bad: bad[0].update(children=bad[0]["children"][:1])),
        ("mixed-two-closed-root-halves-identified", lambda bad: bad[0].update(children=[bad[0]["children"][0]]*2)),
    ):
        bad = deepcopy(record["nodes"])
        mutation(bad)
        reject(label, lambda bad=bad: all_domains(original, row, bad))
    if checked:
        for label, mutation in (
            ("mixed-target-closed-coordinate-escaped", lambda bad: bad[
                "fresh_actual_latest_OPEN_intersection_targets"][0]["actual_closed_lower"].__setitem__(0, "-100")),
            ("mixed-target-source-falsely-declared-nonOPEN", lambda bad: bad[
                "fresh_actual_latest_OPEN_intersection_targets"][0]["source_actual_OPEN_leaf"].update(kind="LOCAL")),
            ("mixed-actual-new-target-summary-omitted", lambda bad: bad[
                "fresh_actual_latest_OPEN_intersection_targets"].pop()),
            ("mixed-actual-new-target-repeated", lambda bad: bad[
                "fresh_actual_latest_OPEN_intersection_targets"].append(deepcopy(
                    bad["fresh_actual_latest_OPEN_intersection_targets"][0]))),
        ):
            bad = deepcopy(record)
            mutation(bad)
            reject(label, lambda bad=bad: target_gate(bad, latest, regions, domains, parents))
    producer.unchanged_inputs(
        args, {**digests, args.diagnosis: digest}, latest,
        record["modules"], binding.sha(producer.__file__))
    report = {
        "schema": SCHEMA, "verified": False,
        "diagnosis_sha256": digest,
        "actual_checked_latest_v8_forest_sha256": digests[args.latest_forest],
        "actual_checked_latest_v8_controls_sha256": digests[args.latest_controls],
        "source_file_sha256": latest["source_file_sha256"],
        "actual_latest_nodes_supports_and_strict_ledgers_retained": list(retained),
        "entire_old_and_new_actual_closed_partitions_and_exact_ledgers_reconstructed": True,
        "independent_BFS_every_node_closed_domain_and_latest_OPEN_parent_walk_checked": True,
        "fresh_NEW_full134rod_strict_whole_closed_targets_independently_checked": len(checked),
        "independent_sine_square_correlated_completion_and_secant_checks": 3*len(checked),
        "both_closed_halves_shared_boundaries_and_all_remainders_reconstructed": True,
        "actual_latest_lineage_subset_history_and_payment_rejection_controls_passed": rejected,
        "latest_arithmetic_result": result, "retained_OPEN_leaves": len(pending),
        "entire_root_arithmetic_cover_completed": not pending,
        "arithmetic_only_NOT_complete_latest_source_history_geometry_acceptance": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_producer_sha256": binding.sha(producer.__file__),
        "tested_modules": {Path(module.__file__).name: binding.sha(module.__file__)
                           for module in producer.modules()},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_latest_v8_mixed_full134rod_intersection_controls_completed": True,
        "fresh_strict_targets": len(checked), "retained_OPEN_leaves": len(pending),
        "actual_rejections": len(rejected), "verified": False, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
