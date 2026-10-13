"""Fresh physical-only whole-domain bounds on the16 checked physical stresses."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_latest878_physical_donor_source as source
import probe_joint_remaining_origin25_primal as reference_recovery
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-latest878-fresh-physical134-donor-whole-leaf-sweep-v1"
PROOF = Path("work/n26-latest878-physical-donor-whole-leaf-sweep-proof.md")
CHECKPOINT_SCHEMA = "N26-unaccepted-latest878-physical-donor-actual-whole-leaf-attempt-checkpoint-v1"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--checkpoint-directory", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=128)
    parser.add_argument("--parts", type=int, default=16)
    parser.add_argument("--support-tries", type=int, default=2)
    args = parser.parse_args()
    if (
        args.report.exists() or args.checkpoint_directory.exists()
        or not 1 <= args.limit <= 878 or not 1 <= args.parts <= 64 or not 1 <= args.support_tries <= 16
    ):
        raise ValueError("fresh bounded physical-only report and immutable checkpoint directory required")
    original, model, seed, controls, row, pending, supports, kernels, references, arcs, inventory = source.inputs()
    ranks = source.ancestor.ancestor.original_source.rank_leaves(original, kernels, pending)
    by_index = {leaf["index"]: leaf for leaf in pending}
    # That routine uses only the original outer root's broad-coordinate set;
    # its work domains here are EXCLUSIVELY the actual paired878 OPEN leaves.
    for module in (source, source.suggestion, reference_recovery):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(PROOF): binding.sha(PROOF), linux(__file__): binding.sha(__file__)})
    args.checkpoint_directory.mkdir(parents=False)
    results, strict, checkpoints = [], [], []
    midpoint_supports = [
        (
            np.array([i for i, j, weight in kernel["pairs"]]),
            np.array([j for i, j, weight in kernel["pairs"]]),
            np.array([float(F(weight, kernel["inverse_denominator"]*sum(kernel["weights"])))
                      for i, j, weight in kernel["pairs"]]),
        )
        for kernel in kernels
    ]
    print(json.dumps({
        "actual_paired878_all622_old_strict_rows_and106_old_exclusions_reconstructed": True,
        "actual16_physical_only_donor_kernels_freshly_checked": True,
        "actual_whole_OPEN_leaf_attempt_limit": args.limit,
        "no_origin_covering_owner_or_virtual_weight_used_in_new_physical_proofs": True,
        "top_numerically_ranked_whole878_OPEN_indices_NOT_proofs": [item["actual_OPEN_leaf_index"] for item in ranks[:5]],
    }), flush=True)
    for number, ranked in enumerate(ranks[:args.limit], 1):
        leaf = by_index[ranked["actual_OPEN_leaf_index"]]
        # Each further support is freshly ranked at this WHOLE leaf midpoint.
        # Neither midpoint/corner scores nor the chosen reference prove a bound.
        middle = np.array([0., *[float((F(a)+F(b))/2) for a, b in zip(leaf["lower"], leaf["upper"])]])
        numerical = []
        for donor, (left, right, weights) in enumerate(midpoint_supports):
            score = float(2*(1-np.cos(2*np.pi*(middle[right]-middle[left])))@weights)
            numerical.append((score, donor))
        numerical.sort(reverse=True)
        first = ranked["suggested_existing_full_support_index"]
        order = [first, *[donor for value, donor in numerical if donor != first]][:args.support_tries]
        trials, selected = [], None
        for donor in order:
            reference, recovery = reference_recovery.exact_turns(original, leaf, references[donor])
            certificate, result, choices = source.suggestion.suggest(
                kernels[donor], original["matrix"], list(map(F, leaf["lower"])), list(map(F, leaf["upper"])),
                reference, original["radius"], arcs, args.parts)
            proved = result is not None and result["arithmetic_strict_target_test_passed"] is True
            trial = {
                "physical_donor_index": donor, "certificate": certificate, "arithmetic_result": result,
                "strict_entire_physical_only_leaf": proved,
                "exact_original_whole_domain_reference_recovery": recovery,
                "numerical_diagonal_tangent_dual_suggestions_NOT_proofs": choices,
            }
            trials.append(trial)
            print(json.dumps({
                "actual_latest878_whole_leaf": leaf["index"], "physical_donor_index": donor,
                "strict_entire_physical_only_leaf": proved,
                "exact_energy_margin_display": float(F(result["strict_energy_margin"])) if result else None,
                "no_origin_split_or_virtual_mu": True, "formal_geometric_payments": 0,
            }), flush=True)
            if proved:
                selected = trial
                strict.append(leaf["index"])
                break
        item = {
            "actual_latest878_whole_OPEN_leaf": leaf, "actual_physical_donor_trials": trials,
            "strict_whole_physical_leaf": selected is not None, "selected_strict_physical_proof": selected,
        }
        results.append(item)
        checkpoint = args.checkpoint_directory/f"leaf-{leaf['index']:05d}.json"
        with checkpoint.open("x", encoding="utf-8", newline="\n") as target:
            target.write(json.dumps({
                "schema": CHECKPOINT_SCHEMA, "verified": False,
                "actual_paired878_seed_sha256": source.SEED_SHA,
                "actual_paired878_controls_sha256": source.CONTROL_SHA,
                "actual_whole_leaf_trial": item,
                "executed_producer_sha256": inventory[linux(__file__)],
                "new_geometric_payments": 0, "global_optimality_proved": False,
            }, indent=2)+"\n")
        checkpoints.append({"whole_leaf_index": leaf["index"], "path": linux(checkpoint), "sha256": binding.sha(checkpoint)})
        print(json.dumps({
            "completed_actual_physical_whole_leaf_attempts": number, "of": args.limit,
            "new_strict_whole_physical_leaves": len(strict),
            "immutable_actual_attempt_checkpoint_saved": True,
            "paired878_unchanged_pending_independent_join": True,
        }), flush=True)
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("physical donor source changed during actual whole-domain arithmetic")
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "actual_paired878_diagnosis_sha256": source.SEED_SHA,
        "actual_paired878_controls_sha256": source.CONTROL_SHA,
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "actual_fresh_physical_only_supports": supports,
        "actual_physical_only_whole_leaf_trials": results,
        "actual_immutable_attempt_checkpoints": checkpoints,
        "new_strict_whole_leaf_indices": sorted(strict),
        "prospective_arithmetic_remaining_OPEN_after_independent_join": 878-len(strict),
        "latest878_global_nodes_and622_strict_rows_UNMODIFIED": True,
        "all106_old_whole_exclusions_ANDall_origin_proof_histories_retained": True,
        "no_origin_owner_requirement_no_virtual_mu_no_origin_certificate_relabelling": True,
        "all_NEW_full134_physical_only_certificates_and_W_only_bounds_freshly_computed": True,
        "new_independent_actual_physical_mode_arithmetic_and_retention_STILL_required": True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_producer_sha256": binding.sha(__file__),
    }
    source.ownership(report, seed, pending)
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "physical_only878_primary_completed_NOT_admission": True,
        "new_strict_whole_leaves": len(strict),
        "prospective_remaining_OPEN_PENDING_independent_join": 878-len(strict),
    }), flush=True)


if __name__ == "__main__":
    main()
