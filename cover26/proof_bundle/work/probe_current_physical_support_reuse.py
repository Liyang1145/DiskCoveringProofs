"""Fresh whole CURRENT OPEN bounds, reusing19 supports without appending them."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_current_physical_reuse_source as source
import probe_joint_remaining_origin25_primal as reference_recovery
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-current-root25-physical-support-reuse-whole-leaf-sweep-v1"
CHECKPOINT_SCHEMA = "N26-unaccepted-current-root25-physical-reuse-whole-attempt-checkpoint-v1"
PROOF = Path("work/n26-current-physical-support-reuse-proof.md")


def main():
    parser = argparse.ArgumentParser()
    source.arguments(parser)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--checkpoint-directory", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=256)
    parser.add_argument("--parts", type=int, default=16)
    parser.add_argument("--support-tries", type=int, default=3)
    args = parser.parse_args()
    if (
        args.report.exists() or args.checkpoint_directory.exists()
        or not 1 <= args.limit <= args.expected_open or not 1 <= args.parts <= 64
        or not 1 <= args.support_tries <= 19
    ):
        raise ValueError("fresh CURRENT physical reuse report/checkpoints and bounded attempt budget required")
    original, model, seed, control, row, pending, supports, kernels, references, arcs, inventory = source.inputs(args)
    ranks = source.INITIAL.rank_leaves(original, kernels, pending)
    by_index = {leaf["index"]: leaf for leaf in pending}
    for module in (source, source.earlier.suggestion, reference_recovery):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(PROOF): binding.sha(PROOF), linux(__file__): binding.sha(__file__)})
    args.checkpoint_directory.mkdir(parents=False)
    midpoint_supports = [
        (np.array([i for i,j,w in kernel["pairs"]]), np.array([j for i,j,w in kernel["pairs"]]),
         np.array([float(F(w,kernel["inverse_denominator"]*sum(kernel["weights"]))) for i,j,w in kernel["pairs"]]))
        for kernel in kernels
    ]
    trials, strict, checkpoints, failed = [], [], [], []
    print(json.dumps({
        "actual_explicit_CURRENT_pair_reconstructed": True, "current_OPEN": len(pending),
        "old_strict_rows": len(seed["arithmetic_ledger"]), "actual_unchanged_physical_supports": len(kernels),
        "fresh_whole_leaf_attempt_limit": args.limit, "no_support_append_or_old_payment_repeat": True,
        "top_numerical_ranking_NOT_proofs": [item["actual_OPEN_leaf_index"] for item in ranks[:5]],
    }), flush=True)
    for number, ranked in enumerate(ranks[:args.limit], 1):
        leaf = by_index[ranked["actual_OPEN_leaf_index"]]
        middle = np.array([0., *[float((F(a)+F(b))/2) for a,b in zip(leaf["lower"],leaf["upper"])]])
        scores = sorted([
            (float(2*(1-np.cos(2*np.pi*(middle[right]-middle[left])))@weights), i)
            for i,(left,right,weights) in enumerate(midpoint_supports)
        ], reverse=True)
        first = ranked["suggested_existing_full_support_index"]
        order = [first, *[i for value,i in scores if i != first]][:args.support_tries]
        attempts, selected = [], None
        for support in order:
            reference, recovery = reference_recovery.exact_turns(original, leaf, references[support])
            certificate, result, choices = source.earlier.suggestion.suggest(
                kernels[support], original["matrix"], list(map(F,leaf["lower"])), list(map(F,leaf["upper"])),
                reference, original["radius"], arcs, args.parts)
            proved = result is not None and result["arithmetic_strict_target_test_passed"] is True
            attempt = {
                "full_support_index": support, "certificate": certificate, "arithmetic_result": result,
                "strict_entire_physical_leaf": proved,
                "exact_whole_source_reference_recovery": recovery,
                "numerical_diagonal_tangent_dual_suggestions_NOT_proofs": choices,
            }
            attempts.append(attempt)
            if proved:
                selected = attempt
                strict.append(leaf["index"])
                break
        if selected is None:
            failed.append(leaf["index"])
        item = {
            "actual_current_whole_OPEN_leaf": leaf, "actual_physical_support_trials": attempts,
            "strict_whole_physical_leaf": selected is not None, "selected_strict_physical_proof": selected,
        }
        trials.append(item)
        checkpoint = args.checkpoint_directory/f"leaf-{leaf['index']:05d}.json"
        with checkpoint.open("x",encoding="utf-8",newline="\n") as target:
            target.write(json.dumps({
                "schema": CHECKPOINT_SCHEMA, "verified": False,
                "actual_current_seed_sha256": args.seed_sha256,
                "actual_current_controls_sha256": args.seed_controls_sha256,
                "actual_whole_leaf_trial": item, "executed_producer_sha256": inventory[linux(__file__)],
                "new_geometric_payments": 0, "global_optimality_proved": False,
            },indent=2)+"\n")
        checkpoints.append({"whole_leaf_index":leaf["index"],"path":linux(checkpoint),"sha256":binding.sha(checkpoint)})
        if number % 16 == 0 or number == args.limit or selected is None:
            print(json.dumps({
                "actual_whole_CURRENT_leaf_attempts": number, "of": args.limit,
                "new_strict_whole_leaves": len(strict), "retained_failed_whole_leaves": len(failed),
                "last_whole_leaf": leaf["index"],
                "last_exact_energy_margin_display": float(F(attempts[-1]["arithmetic_result"]["strict_energy_margin"]))
                    if attempts[-1]["arithmetic_result"] else None,
                "all_actual_attempts_saved_NOT_geometric_payments": True,
            }),flush=True)
    for text,digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("CURRENT physical source changed during actual whole-domain calculations")
    report = {
        "schema":SCHEMA,"verified":False,"source_OPEN_index":25,
        "actual_current_seed_file":linux(args.seed),"actual_current_seed_sha256":args.seed_sha256,
        "actual_current_controls_file":linux(args.seed_controls),"actual_current_controls_sha256":args.seed_controls_sha256,
        "actual_current_OPEN_count":args.expected_open,
        "actual_source_closed_box":row,"source_file_sha256":seed["source_file_sha256"],
        "actual_existing_full134_support_table_sha256_source_is_current_seed":True,
        "actual_current_whole_leaf_trials":trials,"actual_immutable_attempt_checkpoints":checkpoints,
        "new_strict_whole_leaf_indices":sorted(strict),"actual_failed_whole_leaf_indices":sorted(failed),
        "prospective_remaining_OPEN_after_independent_join":len(pending)-len(strict),
        "method_parameters":{"parts":args.parts,"support_tries":args.support_tries,
                             "reference_strategy":"exact_projection_of_current_support_reference"},
        "old_current_global_nodes_supports_and_strict_rows_UNMODIFIED":True,
        "existing19_physical_supports_REUSED_NOT_appended_or_relabelled":True,
        "all_NEW_actual_whole_physical_bounds_freshly_computed":True,
        "old_mathematics_explicit_qualified_REUSE_NOT_fresh_all_old_leaf_replay":True,
        "new_independent_actual_physical_bounds_and_retention_STILL_required":True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission":True,
        "new_geometric_payments":0,"candidate_whole_roots_removed":0,
        "global_lower_bound_proved":False,"global_optimality_proved":False,"n27_started":False,
        "input_sha256":inventory,"executed_producer_sha256":binding.sha(__file__),
    }
    source.ownership(report,seed,pending)
    with args.report.open("x",encoding="utf-8",newline="\n") as target:
        target.write(json.dumps(report,indent=2)+"\n")
    print(json.dumps({
        "CURRENT_physical_reuse_primary_completed_NOT_admission":True,
        "new_strict_whole_leaves":len(strict),"retained_failed_whole_leaves":len(failed),
        "prospective_remaining_OPEN_PENDING_independent_join":len(pending)-len(strict),
    }),flush=True)


if __name__ == "__main__":
    main()
