"""Independent fresh kernels, ALL actual branch bounds and whole918 domains."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_latest918_joint_stress_source as source
import probe_latest918_joint_origin_stress_batch as producer
import test_checked_root28_full134rod_intersections as domains
import test_full134rod_two_origin_kernel as independent_kernel
import test_latest_root25_two_origin_whole_leaves as independent_energy
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-latest918-joint-origin-fresh-stress-batch-controls-v1"


def scope(record, seed):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_paired918_diagnosis_sha256"] != source.SEED_SHA
        or record["actual_paired918_controls_sha256"] != source.CONTROL_SHA
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["all66_prior_whole_exclusions_and_complete2641_branch_forest_retained"] is not True
        or record["latest918_global_nodes_and582_strict_ledger_rows_UNMODIFIED"] is not True
        or record["verified"] is not False
        or record["new_geometric_payments"] != 0 or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("fresh joint918 source, executor or unpaid arithmetic scope changed")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis", type=Path, required=True)
    parser.add_argument("--diagnosis-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual exact completed joint918 diagnosis and new controls required")
    record = binding.read(args.diagnosis)
    for text, digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("joint918 diagnostic actual prerequisite changed")
    original, model, bases, seed, seed_controls, row, pending, arcs, inventory = source.inputs()
    scope(record, seed)
    targets = source.target_gate(record, seed, pending)
    actual_domains, parents = domains.all_domains(original, row, seed["nodes"])
    checked, identities, independently_strict = [], [], set()
    for item in record["actual_joint_stress_whole_leaf_trials"]:
        leaf, proofs, root_possible = item["actual_latest918_whole_OPEN_leaf"], set(), []
        index = leaf["index"]
        if actual_domains[index] != (list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))):
            raise ValueError("fresh joint918 trial clipped an independently reconstructed whole domain")
        for trial in item["actual_origin_branch_trials"]:
            owner = trial["origin_center_label"]
            base = producer.energy.scalar.full.kernel_gate(model, trial["fresh_positive134rod_kernel_certificate"])
            kernel = producer.energy.origin.kernel_gate(
                base, original["data"][3], owner, trial["fresh_origin_multiplier"])
            identities.append({
                "whole_leaf_index": index, "origin_center_label": owner,
                "actual_fresh_augmented_inverse_and_square_completion": independent_kernel.independent_identity(base, kernel),
            })
            certificate, result = trial["whole_origin_branch_certificate"], trial["whole_origin_branch_arithmetic_result"]
            if certificate is None:
                if result is not None or trial["fresh_exact_whole_origin_branch_strict"] is not False:
                    raise ValueError("rejected fresh LDL suggestion forged as an exact branch result")
                checked.append({"whole_leaf_index": index, "origin_center_label": owner,
                                "strict_entire_branch": False, "no_exact_LDL_certificate": True})
                continue
            if result is None or certificate["reference_turns"] != trial["joint_reference_turns"]:
                raise ValueError("fresh joint918 bound lost its actual checked reference or result")
            actual = independent_energy.independent_arithmetic(
                original, kernel, leaf, {"certificate": certificate, "arithmetic_result": result}, arcs)
            strict = actual["arithmetic_strict_entire_origin_branch"]
            if strict != trial["fresh_exact_whole_origin_branch_strict"]:
                raise ValueError("independent fresh joint918 branch classification differs")
            checked.append({
                "whole_leaf_index": index, "origin_center_label": owner,
                "strict_entire_branch": strict, "strict_radius_margin": actual["strict_radius_margin"],
            })
            if strict:
                proofs.add(owner)
            root_possible.append(independent_energy.root_positive(original, kernel))
            print(json.dumps({"independent_fresh_joint918_whole_leaf": index, "origin_owner": owner,
                              "whole_branch_strict": strict, "formal_geometric_payments": 0}), flush=True)
        if item["BOTH_whole_origin_branches_strict"] != (proofs == {16, 25}):
            raise ValueError("independent fresh918 proof counted a single owner as a whole leaf")
        if proofs == {16, 25}:
            independently_strict.add(index)
            if not any(root_possible):
                raise ValueError("fresh full two-origin kernel union falsely excludes the known exact covering root")
    if independently_strict != targets:
        raise ValueError("independent exact fresh918 whole-leaf payment set differs")
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid fresh joint918 control accepted: "+label)

    bad = {**record, "global_optimality_proved": True}
    reject("arithmetic-batch-promoted-to-global-optimality", lambda: scope(bad, seed))
    bad = {**record, "actual_paired918_diagnosis_sha256": source.original_source.SEED_SHA}
    reject("actual918-source-reset-to-984-ancestor", lambda: scope(bad, seed))
    bad_seed = deepcopy(seed)
    bad_seed["arithmetic_ledger"].pop(0)
    reject("prior582-strict-row-lost", lambda: source.scope(bad_seed, seed_controls))
    bad_seed = deepcopy(seed)
    bad_seed["nodes"][2539] = {"kind": "OPEN"}
    reject("prior-complete-two-origin-leaf-reset", lambda: source.scope(bad_seed, seed_controls))
    if record["actual_joint_stress_whole_leaf_trials"]:
        bad = deepcopy(record)
        bad["actual_joint_stress_whole_leaf_trials"].append(deepcopy(bad["actual_joint_stress_whole_leaf_trials"][0]))
        reject("fresh-whole-leaf-target-duplicated", lambda: source.target_gate(bad, seed, pending))
        bad = deepcopy(record)
        bad["actual_joint_stress_whole_leaf_trials"][0]["actual_origin_branch_trials"].pop()
        reject("one-origin-owner-omitted", lambda: source.target_gate(bad, seed, pending))
        bad = deepcopy(record)
        target = bad["actual_joint_stress_whole_leaf_trials"][0]["actual_latest918_whole_OPEN_leaf"]
        target["upper"][0] = str((F(target["lower"][0])+F(target["upper"][0]))/2)
        reject("proper-subbox-forged-as-whole-latest918-OPEN", lambda: source.target_gate(bad, seed, pending))
        trial = record["actual_joint_stress_whole_leaf_trials"][0]["actual_origin_branch_trials"][0]
        bad_certificate = deepcopy(trial["fresh_positive134rod_kernel_certificate"])
        bad_certificate["inverse_numerators"][0][0] = str(int(bad_certificate["inverse_numerators"][0][0])+1)
        reject("fresh60ground-inverse-corrupted", lambda: producer.energy.scalar.full.kernel_gate(model, bad_certificate))
        bad_certificate = deepcopy(trial["fresh_positive134rod_kernel_certificate"])
        bad_certificate["weight_numerators"][0] = 0
        reject("fresh134-physical-weight-zero", lambda: producer.energy.scalar.full.kernel_gate(model, bad_certificate))
        base = producer.energy.scalar.full.kernel_gate(model, trial["fresh_positive134rod_kernel_certificate"])
        reject("negative-origin-multiplier", lambda: producer.energy.origin.kernel_gate(
            base, original["data"][3], trial["origin_center_label"], F(-1)))
        kernel = producer.energy.origin.kernel_gate(
            base, original["data"][3], trial["origin_center_label"], trial["fresh_origin_multiplier"])
        if kernel["origin_multiplier"] > 0:
            bad_kernel = {**kernel, "boundary_origin_constant": F(0)}
            reject("origin-boundary-constant-dropped", lambda: producer.energy.kernel_scope(bad_kernel))
            bad_kernel = {**kernel, "radius_squared_budget_weight": kernel["original_physical_rod_weight_sum"]}
            reject("virtual-origin-radius-budget-dropped", lambda: producer.energy.kernel_scope(bad_kernel))
    for text, digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("fresh joint918 source changed during independent arithmetic")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual joint918 diagnosis changed during independent arithmetic")
    inventory.update(record["input_sha256"])
    for module in (domains, independent_kernel, independent_energy):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(args.diagnosis): args.diagnosis_sha256, linux(__file__): binding.sha(__file__)})
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "diagnosis_sha256": args.diagnosis_sha256,
        "actual_paired918_diagnosis_sha256": source.SEED_SHA,
        "actual_paired918_controls_sha256": source.CONTROL_SHA,
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "independent_fresh134ground_augmented_origin_inverse_and_square_completions": identities,
        "all_actual_fresh_whole_origin_branch_bounds_including_failures_independently_recomputed": checked,
        "actual_new_strict_whole_leaf_indices": sorted(independently_strict),
        "prospective_arithmetic_remaining_OPEN_after_independent_join": 918-len(independently_strict),
        "all2999_closed_domains_AND582_prior_strict_rows_independently_retained": True,
        "all66_prior_whole_exclusions_AND2641_complete_origin_forest_retained": True,
        "all_old_mathematics_explicit_qualified_REUSE_NOT_fresh_replay": True,
        "known_exact_covering_root_not_excluded_by_new_complete_origin_kernel_unions": True,
        "actual_scope_owner_subset_retention_inverse_weight_and_budget_rejection_controls": rejected,
        "latest918_global_tree_UNMODIFIED_separate_checked_arithmetic_join_STILL_required": True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "independent_fresh_joint918_batch_completed_NOT_admission": True,
        "new_BOTH_branch_whole_leaf_indices": sorted(independently_strict),
        "prospective_remaining_OPEN_PENDING_independent_join": 918-len(independently_strict),
        "actual_rejection_controls": len(rejected),
    }), flush=True)


if __name__ == "__main__":
    main()
