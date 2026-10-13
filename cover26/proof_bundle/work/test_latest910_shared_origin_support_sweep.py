"""Independent shared16 support identities and every NEW whole910 branch bound."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_latest910_shared_origin_source as source
import probe_latest910_shared_origin_support_sweep as producer
import test_checked_root28_full134rod_intersections as domains
import test_full134rod_two_origin_kernel as kernel_controls
import test_latest_root25_two_origin_whole_leaves as arithmetic
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-latest910-checked-shared-fresh-origin-support-sweep-controls-v1"


def scope(record, seed):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_paired910_diagnosis_sha256"] != source.SEED_SHA
        or record["actual_paired910_controls_sha256"] != source.CONTROL_SHA
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["latest910_global_nodes_and590_prior_strict_rows_UNMODIFIED"] is not True
        or record["all74_prior_whole_exclusions_ANDcomplete2641_forest_retained"] is not True
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("shared fresh support sweep source/executor or unpaid arithmetic scope changed")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis", type=Path, required=True)
    parser.add_argument("--diagnosis-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual completed shared fresh support diagnostic and fresh controls required")
    record = binding.read(args.diagnosis)
    for text, digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("shared fresh support diagnostic actual prerequisite changed")
    original, model, seed, seed_controls, row, pending, bases, kernels, references, arcs, inventory = source.inputs()
    scope(record, seed)
    targets = source.target_gate(record, seed, pending)
    actual_domains, parents = domains.all_domains(original, row, seed["nodes"])
    identities, checked, strict_whole = {}, [], set()
    for item in record["actual_shared_fresh_whole_leaf_trials"]:
        leaf, proved = item["actual_latest910_whole_OPEN_leaf"], set()
        index = leaf["index"]
        if actual_domains[index] != (list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))):
            raise ValueError("shared fresh support target omitted a whole actual original closed domain")
        for trial in item["all_actual_origin_branch_trials"]:
            support_index, owner = trial["shared_fresh_support_index"], trial["origin_center_label"]
            kernel = kernels[support_index]
            if owner != kernel["origin_center_label"]:
                raise ValueError("shared fresh support bound substituted another original owner")
            if support_index not in identities:
                identities[support_index] = kernel_controls.independent_identity(bases[support_index], kernel)
            if trial["certificate"] is None:
                if trial["arithmetic_result"] is not None or trial["whole_actual_origin_branch_strict"] is not False:
                    raise ValueError("failed shared-support LDL proposal forged as a strict branch")
                checked.append({
                    "whole_leaf_index": index, "origin_center_label": owner,
                    "shared_fresh_support_index": support_index, "no_exact_LDL_certificate": True,
                    "strict_entire_branch": False,
                })
                continue
            if trial["arithmetic_result"] is None:
                raise ValueError("shared fresh support exact branch lacks its result")
            result = arithmetic.independent_arithmetic(original, kernel, leaf, trial, arcs)
            strict = result["arithmetic_strict_entire_origin_branch"]
            if strict != trial["whole_actual_origin_branch_strict"]:
                raise ValueError("independent shared fresh support branch strictness differs")
            if strict:
                proved.add(owner)
            checked.append({
                "whole_leaf_index": index, "origin_center_label": owner,
                "shared_fresh_support_index": support_index, "strict_entire_branch": strict,
                "strict_radius_margin": result["strict_radius_margin"],
            })
            print(json.dumps({
                "independent_shared_fresh_actual_whole_leaf": index, "origin_owner": owner,
                "shared_fresh_support": support_index, "strict_entire_branch": strict,
            }), flush=True)
        if item["BOTH_whole_origin_branches_strict"] != (proved == {16, 25}):
            raise ValueError("independent shared fresh support complete-owner classification differs")
        if proved == {16, 25}:
            strict_whole.add(index)
            proofs = item["strict_origin_branch_proofs"]
            if not any(arithmetic.root_positive(original, kernels[proof["shared_fresh_support_index"]]) for proof in proofs):
                raise ValueError("shared fresh support union falsely excludes the known exact covering root")
    if strict_whole != targets:
        raise ValueError("independent shared fresh support entire-leaf payment set differs")
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid shared fresh support control accepted: "+label)

    reject("arithmetic-sweep-promoted-to-global", lambda: scope({**record, "global_optimality_proved": True}, seed))
    reject("latest910-source-reset-to918", lambda: scope({
        **record, "actual_paired910_diagnosis_sha256": source.ancestor.SEED_SHA}, seed))
    bad_seed = {**seed, "arithmetic_ledger": seed["arithmetic_ledger"][1:]}
    reject("old590-strict-row-lost", lambda: source.scope(bad_seed, seed_controls))
    bad_seed = {**seed, "fresh_joint_origin_supports": seed["fresh_joint_origin_supports"][:-1]}
    reject("checked16-support-table-truncated", lambda: source.scope(bad_seed, seed_controls))
    if record["actual_shared_fresh_whole_leaf_trials"]:
        bad = deepcopy(record)
        bad["actual_shared_fresh_whole_leaf_trials"].append(deepcopy(bad["actual_shared_fresh_whole_leaf_trials"][0]))
        reject("actual-latest910-target-duplicated", lambda: source.target_gate(bad, seed, pending))
        bad = deepcopy(record)
        leaf = bad["actual_shared_fresh_whole_leaf_trials"][0]["actual_latest910_whole_OPEN_leaf"]
        leaf["upper"][0] = str((F(leaf["lower"][0])+F(leaf["upper"][0]))/2)
        reject("proper-subbox-forged-as-whole910-leaf", lambda: source.target_gate(bad, seed, pending))
        bad = deepcopy(record)
        item = bad["actual_shared_fresh_whole_leaf_trials"][0]
        item["all_actual_origin_branch_trials"] = [
            trial for trial in item["all_actual_origin_branch_trials"] if trial["origin_center_label"] == 16]
        reject("whole-origin25-owner-omitted", lambda: source.target_gate(bad, seed, pending))
        bad = deepcopy(record)
        trial = bad["actual_shared_fresh_whole_leaf_trials"][0]["all_actual_origin_branch_trials"][0]
        trial["shared_fresh_support_index"] = -1
        reject("invalid-shared-fresh-support-owner-index", lambda: source.target_gate(bad, seed, pending))
    for text, digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("shared fresh support source changed during independent arithmetic")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("shared fresh support diagnosis changed during independent arithmetic")
    inventory.update(record["input_sha256"])
    for module in (domains, kernel_controls, arithmetic):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(args.diagnosis): args.diagnosis_sha256, linux(__file__): binding.sha(__file__)})
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "diagnosis_sha256": args.diagnosis_sha256,
        "actual_paired910_diagnosis_sha256": source.SEED_SHA, "actual_paired910_controls_sha256": source.CONTROL_SHA,
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "used_shared_fresh_support_inverse_and_square_completions": [
            {"shared_fresh_support_index": index, "identity": identity} for index, identity in sorted(identities.items())],
        "all_actual_new_whole_origin_branch_bounds_including_failures_independently_recomputed": checked,
        "actual_new_strict_whole_leaf_indices": sorted(strict_whole),
        "prospective_arithmetic_remaining_OPEN_after_independent_join": 910-len(strict_whole),
        "all2999_closed_domains_and590_prior_strict_rows_and16_shared_supports_retained": True,
        "all74_prior_whole_exclusions_and2641_complete_origin_forest_retained": True,
        "old_mathematics_explicit_qualified_REUSE_NOT_fresh_all_history_replay": True,
        "known_exact_covering_root_not_excluded_by_any_new_complete_origin_kernel_union": True,
        "actual_scope_retention_owner_subset_and_support_rejection_controls": rejected,
        "paired910_global_tree_UNMODIFIED_separate_checked_history_join_STILL_required": True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "independent_shared_fresh910_sweep_completed_NOT_admission": True,
        "new_BOTH_branch_whole_leaf_exclusions": len(strict_whole),
        "prospective_remaining_OPEN_PENDING_independent_join": 910-len(strict_whole),
        "actual_rejection_controls": len(rejected),
    }), flush=True)


if __name__ == "__main__":
    main()
