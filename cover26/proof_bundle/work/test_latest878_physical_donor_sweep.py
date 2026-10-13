"""Independent PHYSICAL mode, all actual whole878 bounds and immutable attempts."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_latest878_physical_donor_source as source
import probe_latest878_physical_donor_sweep as producer
import test_checked_root28_full134rod_intersections as domains
import test_full134rod_correlated_support as arithmetic
import n26_full134rod_two_origin_kernel as origin
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-latest878-fresh-physical134-donor-whole-leaf-sweep-controls-v1"


def scope(record, seed, supports):
    if (
        record["schema"] != producer.SCHEMA or record["source_OPEN_index"] != 25
        or record["actual_paired878_diagnosis_sha256"] != source.SEED_SHA
        or record["actual_paired878_controls_sha256"] != source.CONTROL_SHA
        or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
        or record["source_file_sha256"] != seed["source_file_sha256"]
        or record["actual_fresh_physical_only_supports"] != supports
        or record["latest878_global_nodes_and622_strict_rows_UNMODIFIED"] is not True
        or record["all106_old_whole_exclusions_ANDall_origin_proof_histories_retained"] is not True
        or record["no_origin_owner_requirement_no_virtual_mu_no_origin_certificate_relabelling"] is not True
        or record["executed_producer_sha256"] != binding.sha(producer.__file__)
        or record["verified"] is not False or record["new_geometric_payments"] != 0
        or record["candidate_whole_roots_removed"] != 0
        or any(record[field] is not False for field in
               ("global_lower_bound_proved", "global_optimality_proved", "n27_started"))
    ):
        raise ValueError("physical-only sweep actual source, donor table, executor or scope differs")


def checkpoint_gate(record):
    actual = {item["actual_latest878_whole_OPEN_leaf"]["index"]: item
              for item in record["actual_physical_only_whole_leaf_trials"]}
    seen, inventory = set(), {}
    for item in record["actual_immutable_attempt_checkpoints"]:
        index = item["whole_leaf_index"]
        if index in seen or index not in actual or binding.sha(item["path"]) != item["sha256"]:
            raise ValueError("physical checkpoint repeated, missing or changed")
        seen.add(index)
        checkpoint = binding.read(item["path"])
        if (
            checkpoint["schema"] != producer.CHECKPOINT_SCHEMA
            or checkpoint["actual_paired878_seed_sha256"] != source.SEED_SHA
            or checkpoint["actual_paired878_controls_sha256"] != source.CONTROL_SHA
            or checkpoint["actual_whole_leaf_trial"] != actual[index]
            or checkpoint["executed_producer_sha256"] != record["executed_producer_sha256"]
            or checkpoint["verified"] is not False or checkpoint["new_geometric_payments"] != 0
            or checkpoint["global_optimality_proved"] is not False
        ):
            raise ValueError("physical checkpoint does not bind the actual whole-domain failed/strict attempt")
        inventory[item["path"]] = item["sha256"]
    if seen != set(actual):
        raise ValueError("physical-only sweep omitted an actual immutable attempt")
    return inventory


def root_positive(original, kernel):
    base = source.ancestor.ancestor.original_source.model_source.base
    geometry, _, _, _ = base.root_geometry(*original["data"][:3])
    lower = F(0)
    for i, j, weight in kernel["pairs"]:
        dot = base.iv.add(base.iv.mul(geometry[i][0], geometry[j][0]),
                          base.iv.mul(geometry[i][1], geometry[j][1]))
        lower += F(2*weight, kernel["energy_denominator"])*(1-dot[1])
    return lower <= original["radius"]**2*F(sum(kernel["weights"]), kernel["scale"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis", type=Path, required=True)
    parser.add_argument("--diagnosis-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists() or binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("actual completed physical-only diagnosis and new independent output required")
    record = binding.read(args.diagnosis)
    for text, digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("physical-only actual prerequisite changed")
    original, model, seed, prior_controls, row, pending, supports, kernels, references, arcs, inventory = source.inputs()
    scope(record, seed, supports)
    targets = source.ownership(record, seed, pending)
    checkpoint_inventory = checkpoint_gate(record)
    actual_domains, parents = domains.all_domains(original, row, seed["nodes"])
    checked, strict_whole, used, sample = [], set(), set(), None
    for item in record["actual_physical_only_whole_leaf_trials"]:
        leaf, index, proved = item["actual_latest878_whole_OPEN_leaf"], item["actual_latest878_whole_OPEN_leaf"]["index"], False
        if actual_domains[index] != (list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))):
            raise ValueError("physical-only target clipped an independently reconstructed entire source")
        for trial in item["actual_physical_donor_trials"]:
            donor = trial["physical_donor_index"]
            kernel = kernels[donor]
            used.add(donor)
            if trial["certificate"] is None:
                if trial["arithmetic_result"] is not None or trial["strict_entire_physical_only_leaf"] is not False:
                    raise ValueError("physical-only rejected LDL suggestion promoted to an exact result")
                checked.append({"whole_leaf_index": index, "physical_donor_index": donor,
                                "no_exact_LDL_certificate": True, "strict_entire_physical_leaf": False})
                continue
            control = {
                "NEW_correlated_quadratic_certificate": trial["certificate"],
                "NEW_correlated_exact_closed_leaf_result": trial["arithmetic_result"],
            }
            result = arithmetic.arithmetic_control(original, kernel, leaf, control, arcs)
            W = F(sum(kernel["weights"]), kernel["scale"])
            if F(result["NEW_full134rod_energy_upper_at_same_root"]) != original["radius"]**2*W:
                raise ValueError("physical-only bound used an origin virtual radius budget")
            strict = result["arithmetic_strict_target_test_passed"]
            if strict != trial["strict_entire_physical_only_leaf"]:
                raise ValueError("independent physical-only whole-domain strict classification differs")
            if strict and (F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0):
                raise ValueError("independent physical-only bound lacks strict energy AND radius margins")
            proved |= strict
            if sample is None:
                sample = kernel, leaf, control, donor
            checked.append({
                "whole_leaf_index": index, "physical_donor_index": donor,
                "strict_entire_physical_leaf": strict, "strict_radius_margin": result["strict_radius_margin"],
            })
            print(json.dumps({
                "independent_actual_physical_whole_leaf": index, "physical_donor_index": donor,
                "strict_entire_physical_leaf": strict, "no_origin_owner_or_virtual_mu": True,
            }), flush=True)
        if item["strict_whole_physical_leaf"] != proved:
            raise ValueError("independent physical-only strict whole-leaf subset differs")
        if proved:
            strict_whole.add(index)
    if strict_whole != targets:
        raise ValueError("independent physical-only entire-domain payment set differs")
    if any(not root_positive(original, kernels[donor]) for donor in used):
        raise ValueError("new physical-only kernel falsely excludes the known exact covering root")
    rejected = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid physical-only source/arithmetic control accepted: "+label)

    reject("physical-only-batch-promoted-to-global", lambda: scope({**record, "global_optimality_proved": True}, seed, supports))
    reject("actual878-source-reset-to910", lambda: scope({
        **record, "actual_paired878_diagnosis_sha256": source.ancestor.SEED_SHA}, seed, supports))
    reject("old622-strict-row-omitted", lambda: source.scope({
        **seed, "arithmetic_ledger": seed["arithmetic_ledger"][1:]}, prior_controls))
    reject("old16-origin-donor-history-truncated", lambda: source.scope({
        **seed, "fresh_joint_origin_supports": seed["fresh_joint_origin_supports"][:-1]}, prior_controls))
    if record["actual_physical_only_whole_leaf_trials"]:
        bad = deepcopy(record)
        bad["actual_physical_only_whole_leaf_trials"].append(deepcopy(bad["actual_physical_only_whole_leaf_trials"][0]))
        reject("whole878-target-duplicated", lambda: source.ownership(bad, seed, pending))
        bad = deepcopy(record)
        leaf = bad["actual_physical_only_whole_leaf_trials"][0]["actual_latest878_whole_OPEN_leaf"]
        leaf["upper"][0] = str((F(leaf["lower"][0])+F(leaf["upper"][0]))/2)
        reject("proper-subbox-forged-as-whole878-OPEN", lambda: source.ownership(bad, seed, pending))
        bad = deepcopy(record)
        bad["actual_physical_only_whole_leaf_trials"][0]["actual_physical_donor_trials"][0]["physical_donor_index"] = -1
        reject("unbound-negative-physical-donor-index", lambda: source.ownership(bad, seed, pending))
        bad = {**record, "actual_immutable_attempt_checkpoints": record["actual_immutable_attempt_checkpoints"][:-1]}
        reject("actual-attempt-checkpoint-omitted", lambda: checkpoint_gate(bad))
    if sample is not None:
        kernel, leaf, trial, donor = sample
        old = seed["fresh_joint_origin_supports"][donor]
        augmented = origin.kernel_gate(kernel, original["data"][3], old["origin_center_label"], old["origin_multiplier"])
        reject("old-augmented-origin-kernel-forged-as-physical-only", lambda: source.suggestion.exact.quadratic_data(
            augmented, original["matrix"], leaf["lower"], leaf["upper"], trial["NEW_correlated_quadratic_certificate"], arcs))
        bad_certificate = {**trial["NEW_correlated_quadratic_certificate"], "origin_multiplier": "0"}
        reject("origin-certificate-field-added-to-physical-mode", lambda: source.suggestion.exact.quadratic_data(
            kernel, original["matrix"], leaf["lower"], leaf["upper"], bad_certificate, arcs))
        bad_kernel_certificate = deepcopy(supports[donor]["kernel_certificate"])
        bad_kernel_certificate["weight_numerators"][0] = 0
        reject("physical134-donor-weight-zero", lambda: source.suggestion.exact.full.kernel_gate(model, bad_kernel_certificate))
        bad_kernel_certificate = deepcopy(supports[donor]["kernel_certificate"])
        bad_kernel_certificate["inverse_numerators"][0][0] = str(int(bad_kernel_certificate["inverse_numerators"][0][0])+1)
        reject("physical60ground-inverse-corrupted", lambda: source.suggestion.exact.full.kernel_gate(model, bad_kernel_certificate))
    for text, digest in record["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("physical-only source changed during independent calculations")
    for text, digest in checkpoint_inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("actual immutable physical attempt changed during independent calculations")
    if binding.sha(args.diagnosis) != args.diagnosis_sha256:
        raise ValueError("physical-only diagnosis changed during independent calculations")
    inventory.update(record["input_sha256"])
    inventory.update(checkpoint_inventory)
    for module in (arithmetic, domains, origin):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(args.diagnosis): args.diagnosis_sha256, linux(__file__): binding.sha(__file__)})
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "diagnosis_sha256": args.diagnosis_sha256,
        "actual_paired878_diagnosis_sha256": source.SEED_SHA,
        "actual_paired878_controls_sha256": source.CONTROL_SHA,
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "all_actual_new_whole_physical_bounds_including_failures_independently_recomputed": checked,
        "new_strict_whole_leaf_indices": sorted(strict_whole),
        "prospective_arithmetic_remaining_OPEN_after_independent_join": 878-len(strict_whole),
        "all2999_closed_domains622_old_strict_rows_and106old_exclusions_retained": True,
        "all_old_supports_and_complete_origin_branch_ANDforest_histories_retained": True,
        "all16_physical_donor_inverse_identities_freshly_checked": True,
        "physical_donors_used": sorted(used),
        "known_exact_covering_root_not_excluded_by_any_used_physical_kernel": True,
        "no_origin_owner_or_virtual_mu_used_in_new_physical_mode": True,
        "actual_immutable_whole_attempt_checkpoints_rechecked": len(checkpoint_inventory),
        "actual_scope_retention_owner_subset_checkpoint_and_mode_rejection_controls": rejected,
        "old_mathematics_explicit_qualified_REUSE_NOT_fresh_all_history_replay": True,
        "paired878_tree_UNMODIFIED_separate_checked_arithmetic_join_STILL_required": True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "independent_physical_only878_sweep_completed_NOT_admission": True,
        "new_strict_whole_leaves": len(strict_whole),
        "prospective_remaining_OPEN_PENDING_independent_join": 878-len(strict_whole),
        "actual_rejection_controls": len(rejected),
    }), flush=True)


if __name__ == "__main__":
    main()
