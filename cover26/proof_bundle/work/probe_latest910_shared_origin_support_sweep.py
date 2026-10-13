"""Batch WHOLE910 OPEN bounds using the16 actual newly checked fresh stresses."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_latest910_shared_origin_source as source
import probe_joint_remaining_origin25_primal as reference_recovery
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-latest910-checked-shared-fresh-origin-support-sweep-v1"
PROOF = Path("work/n26-latest910-shared-origin-support-sweep-proof.md")


def rank(original, row, pending, kernels):
    broad = [i for i, (a, b) in enumerate(zip(row["sharp_lower"], row["sharp_upper"])) if F(b)-F(a) > F(1, 10**7)]
    if len(broad) > 10:
        raise ValueError("shared support numerical ranking refuses unbounded corner allocation")
    masks = np.arange(1 << len(broad))
    bits = np.array([((masks >> j) & 1) for j in range(len(broad))]).T
    prepared = []
    for index, kernel in enumerate(kernels):
        prepared.append({
            "support": index, "owner": kernel["origin_center_label"],
            "left": np.array([i for i, j, w in kernel["pairs"]]),
            "right": np.array([j for i, j, w in kernel["pairs"]]),
            "weights": np.array([float(F(w, kernel["energy_denominator"])) for i, j, w in kernel["pairs"]]),
            "constant": float(kernel["boundary_origin_constant"]),
            "budget": float(kernel["radius_squared_budget_weight"]),
        })
    result = []
    for number, leaf in enumerate(pending, 1):
        lo = np.array(list(map(float, map(F, leaf["lower"]))))
        hi = np.array(list(map(float, map(F, leaf["upper"]))))
        points = np.tile((lo+hi)/2, (len(masks), 1))
        points[:, broad] = lo[broad]+bits*(hi-lo)[broad]
        points = np.column_stack((np.zeros(len(points)+1), np.vstack((points, (lo+hi)/2))))
        branches = {16: [], 25: []}
        for item in prepared:
            values = item["constant"]+2*(1-np.cos(2*np.pi*(points[:, item["right"]]-points[:, item["left"]])))@item["weights"]
            score = float(min(values)/item["budget"])-float(original["radius"]**2)
            branches[item["owner"]].append({
                "shared_fresh_support_index": item["support"], "sampled_corner_score_NOT_lower_bound": score,
            })
        for owner in branches:
            branches[owner].sort(key=lambda item: item["sampled_corner_score_NOT_lower_bound"], reverse=True)
        result.append({
            "actual_latest910_OPEN_leaf_index": leaf["index"], "suggested_owner_supports": branches,
            "both_branches_sampled_score_NOT_lower_bound": min(
                branches[owner][0]["sampled_corner_score_NOT_lower_bound"] for owner in (16, 25)),
        })
        if number % 200 == 0:
            print(json.dumps({"shared_fresh_support_numerical_ranking_ONLY": number, "of": len(pending)}), flush=True)
    return sorted(result, key=lambda item: item["both_branches_sampled_score_NOT_lower_bound"], reverse=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=32)
    parser.add_argument("--parts", type=int, default=16)
    parser.add_argument("--branch-tries", type=int, default=2)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.limit <= 256 or not 1 <= args.parts <= 64 or not 1 <= args.branch_tries <= 8:
        raise ValueError("fresh bounded shared-support sweep required")
    original, model, seed, controls, row, pending, bases, kernels, references, arcs, inventory = source.inputs()
    rankings = rank(original, row, pending, kernels)
    by_index = {leaf["index"]: leaf for leaf in pending}
    results, strict = [], []
    print(json.dumps({
        "actual_paired910_and_all590_old_strict_rows_reconstructed": True,
        "actual16_checked_fresh_origin_supports_reconstructed": True,
        "fresh_whole_leaf_limit": args.limit,
        "top_numerically_ranked_actual910_OPEN_indices_NOT_proofs": [
            item["actual_latest910_OPEN_leaf_index"] for item in rankings[:args.limit]],
    }), flush=True)
    for number, ranked in enumerate(rankings[:args.limit], 1):
        leaf = by_index[ranked["actual_latest910_OPEN_leaf_index"]]
        trials, proofs = [], []
        for owner in (16, 25):
            for choice in ranked["suggested_owner_supports"][owner][:args.branch_tries]:
                support_index = choice["shared_fresh_support_index"]
                reference, recovery = reference_recovery.exact_turns(original, leaf, references[support_index])
                certificate, result, choices = source.energy.suggest(
                    kernels[support_index], original["matrix"],
                    list(map(F, leaf["lower"])), list(map(F, leaf["upper"])),
                    reference, original["radius"], arcs, args.parts)
                proved = result is not None and result["arithmetic_strict_entire_origin_branch"] is True
                trial = {
                    "origin_center_label": owner, "shared_fresh_support_index": support_index,
                    "certificate": certificate, "arithmetic_result": result,
                    "whole_actual_origin_branch_strict": proved,
                    "exact_original_whole_domain_reference_recovery": recovery,
                    "numerical_curvature_tangent_dual_suggestions_NOT_proofs": choices,
                }
                trials.append(trial)
                print(json.dumps({
                    "actual_latest910_whole_leaf": leaf["index"], "origin_owner": owner,
                    "checked_shared_fresh_support": support_index, "strict_entire_branch": proved,
                    "exact_energy_margin_display": float(F(result["strict_energy_margin"])) if result else None,
                    "formal_geometric_payments": 0,
                }), flush=True)
                if proved:
                    proofs.append(trial)
                    break
        whole = {proof["origin_center_label"] for proof in proofs} == {16, 25}
        results.append({
            "actual_latest910_whole_OPEN_leaf": leaf, "all_actual_origin_branch_trials": trials,
            "strict_origin_branch_proofs": proofs, "BOTH_whole_origin_branches_strict": whole,
        })
        if whole:
            strict.append(leaf["index"])
        print(json.dumps({
            "completed_shared_fresh_whole_leaf_attempts": number, "of": args.limit,
            "new_BOTH_branch_whole_leaf_exclusions": len(strict),
            "paired910_tree_UNMODIFIED_pending_independent_join": True,
        }), flush=True)
    for module in (source, source.energy, reference_recovery):
        inventory[linux(module.__file__)] = binding.sha(module.__file__)
    inventory.update({linux(PROOF): binding.sha(PROOF), linux(__file__): binding.sha(__file__)})
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("shared fresh support source changed during exact whole-domain calculations")
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "actual_paired910_diagnosis_sha256": source.SEED_SHA, "actual_paired910_controls_sha256": source.CONTROL_SHA,
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "actual_shared_fresh_whole_leaf_trials": results, "actual_new_strict_whole_leaf_indices": sorted(strict),
        "prospective_arithmetic_remaining_OPEN_after_independent_join": 910-len(strict),
        "latest910_global_nodes_and590_prior_strict_rows_UNMODIFIED": True,
        "all74_prior_whole_exclusions_ANDcomplete2641_forest_retained": True,
        "fresh16_support_table_REUSED_without_relabelling_or_counting_old_leaves_again": True,
        "all_new_actual_whole_domain_bounds_freshly_computed_NOT_point_samples": True,
        "new_independent_exact_whole_bounds_owner_partition_and_retention_STILL_required": True,
        "arithmetic_only_NOT_latest_source_model_geometry_current_admission": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "input_sha256": inventory, "executed_producer_sha256": binding.sha(__file__),
    }
    source.target_gate(report, seed, pending)
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "shared_fresh910_primary_completed_NOT_admission": True,
        "new_BOTH_branch_whole_leaf_exclusions": len(strict),
        "prospective_remaining_OPEN_PENDING_independent_join": 910-len(strict),
    }), flush=True)


if __name__ == "__main__":
    main()
