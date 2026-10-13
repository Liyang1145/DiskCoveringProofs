"""Independent entire root25 successor domains and NEW134rod strict targets."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import continue_root25_preserved_full134rod_regions as producer
import test_checked_root28_full134rod_intersections as domains
import test_full134rod_correlated_support as energy
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-root25-v3-preserved-full134rod-region-successor-controls-v1"
mixed = producer.mixed


def scope(record, seed, row, digests, layer, table):
    if (
        record["schema"] != producer.SCHEMA
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["source_OPEN_index"] != 25 or record["actual_source_closed_box"] != row
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_checked_latest_root25_v3_sha256"] != binding.sha(producer.SEED)
        or record["actual_checked_latest_root25_v3_controls_sha256"] != binding.sha(producer.SEED_TESTS)
        or record["actual_candidate_identity_DATA_only"] != layer
        or record["actual_proof_time_current_sha256"] != binding.sha(producer.CURRENT)
        or record["all_input_sha256"] != digests or record["full134rod_supports"] != table
        or record["old_v3_tree_NOT_reset_and_no_root28_tree_or_payment_imported"] is not True
        or record["all_closed_halves_shared_boundaries_and_nonempty_remainders_retained"] is not True
        or record["three_full134rod_stresses_are_universal_arithmetic_DATA_ONLY"] is not True
        or record["separate_independent_arithmetic_controls_still_required"] is not True
        or record["entire_latest_source_model_history_geometry_admission_NOT_performed"] is not True
        or record["original_52_coordinate_LOCAL_allowance_unchanged"] != "7/800000"
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in (
            "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("root25 new successor changed actual whole-root/lineage/model or zero-payment scope")
    for module in producer.modules():
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("root25 successor executed a changed arithmetic implementation")
    retained = mixed.retention_gate(seed, record)
    if list(retained) != record["old_nodes_supports_and_strict_ledgers_preserved_identically"]:
        raise ValueError("root25 actual old proof/ledger retention differs")
    return retained


def targets_gate(record, seed, all_domains, parents):
    regions = record["selected_widest_actually_strict_closed_regions"]
    full_leaves = {i for i, node in enumerate(record["nodes"]) if node["kind"] == mixed.KIND}
    seen = set()
    for item in record["fresh_actual_OPEN_intersection_targets"]:
        index, region_index = item["actual_target_index"], item["region_index"]
        source = item["source_actual_OPEN_leaf"]
        source_index = source["index"]
        if (
            type(index) is not int or index not in full_leaves or index in seen
            or type(region_index) is not int or not 0 <= region_index < len(regions)
            or source_index not in all_domains or source["kind"] != "OPEN"
        ):
            raise ValueError("root25 new target has invalid, duplicate or paid-source ownership")
        seen.add(index)
        actual, parent_box = all_domains[index], all_domains[source_index]
        if (
            actual is None or parent_box is None
            or parent_box != (list(map(F, source["lower"])), list(map(F, source["upper"])))
            or actual != (list(map(F, item["actual_closed_lower"])), list(map(F, item["actual_closed_upper"])))
            or type(item["whole_source_OPEN_leaf"]) is not bool
            or item["whole_source_OPEN_leaf"] != (actual == parent_box)
        ):
            raise ValueError("root25 proper target was changed or promoted to its whole parent")
        region = regions[region_index]
        if (
            item["full_support_index"] != region["full_support_index"]
            or record["nodes"][index] != {
                "kind": mixed.KIND, "full_support_index": region["full_support_index"],
                "certificate": region["certificate"]}
            or any(not F(a) <= x <= y <= F(b) for a, b, x, y in zip(
                region["lower"], region["upper"], *actual))
        ):
            raise ValueError("root25 target changed its strict region/certificate containment")
        cursor = source_index
        while cursor >= len(seed["nodes"]):
            if cursor not in parents:
                raise ValueError("root25 target source has no original source ancestor")
            cursor = parents[cursor]
        if seed["nodes"][cursor] != {"kind": "OPEN"}:
            raise ValueError("root25 new proof reset an actual old paid ancestor")
        cursor = index
        while cursor != source_index:
            if cursor not in parents:
                raise ValueError("root25 strict target is not descended from its actual recorded source")
            cursor = parents[cursor]
    if seen != full_leaves or not seen:
        raise ValueError("root25 target ledger omitted or invented a strict leaf")
    for decision in record["fresh_closed_split_decisions"]:
        node = record["nodes"][decision["old_OPEN_node"]]
        if node != {
            "kind": "SPLIT", "axis": decision["axis"], "mid": decision["closed_shared_cut"],
            "children": decision["children"],
        } or decision["both_closed_halves_and_all_nonempty_remainders_retained"] is not True:
            raise ValueError("root25 fresh split/shared-boundary ledger differs from actual tree")
    return len(seen)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, old_kernel, seed, row, table, kernels, _, digests, layer = producer.inputs()
    record, digest = binding.read(args.diagnosis), binding.sha(args.diagnosis)
    retained = scope(record, seed, row, digests, layer, table)
    arcs = binding.force.load_trig(producer.RESOURCE)[0]
    actual_domains, parents = domains.all_domains(original, row, record["nodes"])
    target_count = targets_gate(record, seed, actual_domains, parents)
    for region in record["selected_widest_actually_strict_closed_regions"]:
        kernel = kernels[region["full_support_index"]]
        result = mixed.correlated.bound(
            kernel, original["matrix"], region["lower"], region["upper"],
            region["certificate"], original["radius"], arcs)
        if result["arithmetic_strict_target_test_passed"] is not True:
            raise ValueError("root25 selected grown region is not actually strict")
    for index, item in enumerate(record["fresh_actual_OPEN_intersection_targets"]):
        kernel = kernels[item["full_support_index"]]
        node = record["nodes"][item["actual_target_index"]]
        shape = {"lower": item["actual_closed_lower"], "upper": item["actual_closed_upper"]}
        trial = {"NEW_correlated_quadratic_certificate": node["certificate"],
                 "NEW_correlated_exact_closed_leaf_result": item["fresh_exact_whole_closed_target_result"]}
        result = energy.arithmetic_control(original, kernel, shape, trial, arcs)
        if result["arithmetic_strict_target_test_passed"] is not True:
            raise ValueError("root25 independently reconstructed full target is not strict")
        print(json.dumps({"root25_NEW_targets_independently_reconstructed": index+1,
                          "target_count": target_count, "formal_payments": 0}), flush=True)
    result, pending, ledger = mixed.replay(
        original, old_kernel, arcs, row, record["nodes"], record["alternative_supports"], table)
    if (
        result != record["arithmetic_result"] or pending != record["pending_closed_leaf_boxes"]
        or ledger != record["arithmetic_ledger"]
    ):
        raise ValueError("root25 entire newest arithmetic forest/strict ledger differs")
    rejected = []
    def reject(name, action):
        try:
            action()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(name)
        else:
            raise AssertionError("invalid actual root25 successor accepted: "+name)
    for field, value in (
        ("source_OPEN_index", 28), ("new_geometric_payments", 1),
        ("global_lower_bound_proved", True), ("global_optimality_proved", True),
        ("original_52_coordinate_LOCAL_allowance_unchanged", "1/1000"),
        ("entire_latest_source_model_history_geometry_admission_NOT_performed", False),
    ):
        bad = {**record, field: value}
        reject(field, lambda bad=bad: scope(bad, seed, row, digests, layer, table))
    bad = {**record, "nodes": deepcopy(record["nodes"])}
    split = next(node for node in bad["nodes"] if node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("lost-shared-closed-half", lambda: domains.all_domains(original, row, bad["nodes"]))
    reject("hidden-unreachable-remainder",
           lambda: domains.all_domains(original, row, record["nodes"]+[{"kind": "OPEN"}]))
    old_paid = next(i for i, node in enumerate(seed["nodes"]) if node["kind"] not in ("OPEN", "SPLIT"))
    bad = {**record, "nodes": deepcopy(record["nodes"])}
    bad["nodes"][old_paid] = {"kind": "OPEN"}
    reject("old-paid-leaf-reset", lambda: mixed.retention_gate(seed, bad))
    reject("old-support-prefix-truncated", lambda: mixed.retention_gate(
        seed, {**record, "alternative_supports": record["alternative_supports"][1:]}))
    reject("old-strict-ledger-truncated", lambda: mixed.retention_gate(
        seed, {**record, "arithmetic_ledger": record["arithmetic_ledger"][1:]}))
    for name, mutate in (
        ("proper-target-promoted-to-whole-parent",
         lambda items: items[0].update(whole_source_OPEN_leaf=not items[0]["whole_source_OPEN_leaf"])),
        ("new-target-omitted", lambda items: items.pop()),
        ("new-target-repeated", lambda items: items.append(deepcopy(items[0]))),
        ("new-target-source-owner-changed", lambda items: items[0]["source_actual_OPEN_leaf"].update(index=0)),
    ):
        bad = {**record, "fresh_actual_OPEN_intersection_targets":
               deepcopy(record["fresh_actual_OPEN_intersection_targets"])}
        mutate(bad["fresh_actual_OPEN_intersection_targets"])
        reject(name, lambda bad=bad: targets_gate(bad, seed, actual_domains, parents))
    if len(rejected) != 15:
        raise ValueError("root25 successor invalid ownership/retention control inventory changed")
    for path, expected in {**digests, linux(args.diagnosis): digest}.items():
        if binding.sha(path) != expected:
            raise ValueError("root25 successor arithmetic inputs changed during independent controls")
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "diagnosis_sha256": digest, "actual_latest_v3_seed_sha256": binding.sha(producer.SEED),
        "actual_latest_v3_controls_sha256": binding.sha(producer.SEED_TESTS),
        "all_original_and_new_closed_domains_and_shared_boundaries_independently_reconstructed": True,
        "all_previous_nonOPEN_nodes_support_prefixes_and_strict_ledgers_retained": list(retained),
        "all_actual_new_full134rod_targets_independently_reconstructed": target_count,
        "independent_feasible_sine_square_and_positive_square_completion_checks": 3*target_count,
        "latest_arithmetic_result": result, "retained_OPEN_leaves": len(pending),
        "entire_root_arithmetic_cover_completed": not pending,
        "actual_invalid_scope_split_retention_and_target_ownership_controls_rejected": rejected,
        "arithmetic_only_NOT_latest_source_model_geometry_or_current_admission": True,
        "original_52_coordinate_LOCAL_allowance_unchanged": "7/800000",
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_producer_sha256": binding.sha(producer.__file__),
        "tested_mixed_arithmetic_sha256": binding.sha(mixed.__file__),
        "tested_independent_domain_walk_sha256": binding.sha(domains.__file__),
        "tested_independent_correlated_arithmetic_sha256": binding.sha(energy.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("latest_arithmetic_result",
                                     "actual_invalid_scope_split_retention_and_target_ownership_controls_rejected")}),
          flush=True)


if __name__ == "__main__":
    main()
