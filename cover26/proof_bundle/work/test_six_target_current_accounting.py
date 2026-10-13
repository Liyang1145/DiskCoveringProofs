"""Actual six-target source accounting controls, NOT real geometry/current."""

from copy import deepcopy
import json
from pathlib import Path

import n26_six_target_current_accounting as accounting
import n26_current_candidate_layer_identity as identity
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-current28-six-target-current-accounting-controls-v1.json")
    if output.exists():
        raise FileExistsError("preserve completed six-target accounting controls")
    folder = Path("outputs/n26-current28-six-target-source-geometry-v1")
    manifest = binding.read(folder/"MANIFEST.json")
    parent_path = binding.local_path(manifest["parent_current"])
    final_path = binding.local_path(manifest["parent_final"])
    parent, parent_digest, final_digest = binding.read(parent_path), binding.sha(parent_path), binding.sha(final_path)
    source, frontier = binding.read(folder/"SOURCE-FRONTIER.json"), binding.read(folder/"FRONTIER.json")
    ledger, constants = binding.read(folder/"LOWER-LEDGER.json"), binding.read(folder/"FAMILY-CONSTANTS.json")
    proofs = {key: binding.sha(folder/name) for key, name in {
        "cap": "UNIT-CAP-PROOF.md", "generic": "GENERIC-SLACK-PROOF.md",
        "bridge": "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md", "ear": "CLOSED-EAR-PROOF.md",
        "six": "SIX-CORE-TARGET-FILLED-EAR-PROOF.md",
    }.items()}
    layer = identity.gate(parent, parent_digest, binding.local_path(manifest["actual_candidate_source"]))
    result = accounting.partition_gate(parent, source, frontier, ledger, constants, proofs)
    partition_controls, receipt_controls, current_controls = [], [], []
    def rejected(target, name, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            target.append(name)
            print(json.dumps({"six_target_accounting_control_rejected": name,
                              "new_formal_geometric_payments": 0}), flush=True)
        else:
            raise AssertionError("invalid six-target actual source/accounting shape accepted: "+name)
    def changed_ledger():
        rows = list(ledger)
        rows[0] = deepcopy(rows[0])
        return rows
    controls = [
        ("missing-actual-paid-prefix", source, frontier, ledger[1:], constants, proofs),
        ("duplicate-whole-prefix-owner", source, frontier, ledger+ledger[:1], constants, proofs),
    ]
    changed = changed_ledger()
    changed[0]["source_index"] = -1
    controls.append(("wrong-source-prefix-owner", source, frontier, changed, constants, proofs))
    changed = changed_ledger()
    changed[0]["all_original_physical_count_and_shadow_case_distributions"].pop()
    controls.append(("missing-original-physical-count-case", source, frontier, changed, constants, proofs))
    changed = changed_ledger()
    changed[0]["all_original_physical_count_and_shadow_case_distributions"][0][
        "all_shadow_label_placements_checked"] -= 1
    controls.append(("missing-shadow-placement", source, frontier, changed, constants, proofs))
    changed = changed_ledger()
    changed[0]["exact_six_core_target_identities"]["exact_horizontal_margin_above_U"] = "0"
    controls.append(("six-target-strict-projection-margin-lost", source, frontier, changed, constants, proofs))
    changed = changed_ledger()
    changed[0]["selected_strongest_filled_patch"]["actual_enclosed_nonowner_labels"].pop()
    controls.append(("filled-patch-interior-label-deleted", source, frontier, changed, constants, proofs))
    changed = changed_ledger()
    changed[0]["outside_budget_INCLUDES_introduced_outside_vertices_AND_future_labels"] = False
    controls.append(("already-introduced-outside-labels-hidden", source, frontier, changed, constants, proofs))
    changed = dict(frontier, pending_states=frontier["pending_states"][1:])
    controls.append(("unpaid-sibling-deleted", source, changed, ledger, constants, proofs))
    changed = dict(frontier, pending_states=frontier["pending_states"]+frontier["pending_states"][:1])
    controls.append(("unpaid-sibling-duplicated", source, changed, ledger, constants, proofs))
    changed = dict(frontier, pending_states=[row for row in frontier["pending_states"] if not row["terminal"]])
    controls.append(("raw-complete-candidate-omitted", source, changed, ledger, constants, proofs))
    changed = dict(source, inherited_source_is_unconditional_at_U=True)
    controls.append(("conditional-source-promoted-to-U", changed, frontier, ledger, constants, proofs))
    changed = dict(constants, external_n8_theorem_assumed=False)
    controls.append(("external-original-nonowner-premise-hidden", source, frontier, ledger, changed, proofs))
    changed = dict(proofs)
    changed.pop("six")
    controls.append(("written-continuous-six-target-proof-unbound", source, frontier, ledger, constants, changed))
    for name, s, f, l, c, p in controls:
        rejected(partition_controls, name, lambda s=s, f=f, l=l, c=c, p=p:
                 accounting.partition_gate(parent, s, f, l, c, p))
    synthetic = {
        "schema": accounting.ACCEPTANCE_SCHEMA, "verified": True,
        "radius_scope": accounting.SCOPE, "inherited_source_is_unconditional_at_U": False,
        "executed_checker_file": accounting.CHECKER,
        "executed_checker_sha256": binding.sha(folder/accounting.CHECKER),
        "files": {accounting.CHECKER: binding.sha(folder/accounting.CHECKER)},
        "actual_parent_current_sha256": parent_digest, "actual_parent_final_sha256": final_digest,
        "actual_candidate_layer_identity": layer, "radius_upper": source["radius_upper"],
        "r_strict_interval": parent["r_strict_interval"],
        "screen_radius_threshold_for_NEW_six_target_rule": str(accounting.U),
        "complete_parent_dependency_inventory_rehashed_BEFORE_AND_AFTER": True,
        "prior_completed_parent_semantic_proof_chain_still_bound_NOT_replaced_by_DATA": True,
        "all_original_candidate_terminals_owned_roots_histories_and_LOCAL_retained": True,
        "all_original_counts_AND_shadow_label_placements_freshly_checked_both_ways": True,
        "corner_shadow_is_embedded_LIMIT_NOT_26_positive_area_Voronoi_cells": True,
        "written_continuous_cover_embedding_and_six_target_proofs_used_NOT_inferred_from_finite_tests": True,
        "old643_scope_NOT_used_as_acceptance_of_additional4903": True,
        "fresh_independent_universal_bridge_scalar_identities": 12,
        "historical_closed_types_retained": 87, "historical_proof_receipts_retained_and_associated": 215,
        "source_actual_current_frontier": 11183,
        "geometry_accepted_filtered_frontier_REQUIRES_CURRENT_AND_FINAL": 5637,
        "strict_new_six_target_whole_source_prefixes": 5546,
        "actual_geometric_scope_negative_controls_rejected": ["synthetic-only-"+str(i) for i in range(6)],
        "source_files": parent["files"],
        "ENTIRE_actual_source_prefixes_six_target_geometry_and_case_partition_replayed_here":
            binding.read(folder/"SOURCE-MATHEMATICAL-SEMANTICS.json"),
    }
    for field in (
        "actual_current_nodes_removed_by_this_OWN_acceptance",
        "new_formal_geometric_payments_by_this_OWN_acceptance",
        "candidate_whole_roots_removed", "original_U_frontier_nodes_removed",
    ):
        synthetic[field] = 0
    for field in (
        "unrestricted_reduction_final_joint_acceptance", "frozen_geometric_reduction_proved",
        "full_catalog_complete", "global_lower_bound_proved", "global_optimality_proved", "n27_started",
    ):
        synthetic[field] = False
    def receipt(changed, published=None):
        accounting.receipt_gate(parent, parent_digest, final_digest, changed,
                                changed if published is None else published, changed,
                                binding.sha(folder/accounting.CHECKER), layer)
    receipt(synthetic)
    for name, field, value in (
        ("unverified-synthetic-receipt", "verified", False),
        ("old643-scope-substituted", "old643_scope_NOT_used_as_acceptance_of_additional4903", False),
        ("wrong-own-checker", "executed_checker_file", "verify_closed_ear_source_geometry.py"),
        ("wrong-proof-time-parent", "actual_parent_current_sha256", "0"*64),
        ("partial-source-scan", "source_actual_current_frontier", 5546),
        ("phantom-candidate-root-payment", "candidate_whole_roots_removed", 1),
        ("shadow-cells-substituted-for-original-cells", "corner_shadow_is_embedded_LIMIT_NOT_26_positive_area_Voronoi_cells", False),
        ("finite-samples-substituted-for-continuous-proof", "written_continuous_cover_embedding_and_six_target_proofs_used_NOT_inferred_from_finite_tests", False),
        ("global-optimality-overclaim", "global_optimality_proved", True),
        ("older-candidate-owner-identity-substituted", "actual_candidate_layer_identity", {}),
    ):
        changed = dict(synthetic)
        changed[field] = value
        rejected(receipt_controls, name, lambda changed=changed: receipt(changed))
    changed = dict(synthetic, source_files=dict(parent["files"]))
    changed["source_files"].pop(next(iter(changed["source_files"])))
    rejected(receipt_controls, "old-proof-dependency-dropped", lambda: receipt(changed))
    changed = dict(synthetic, verified=False)
    rejected(receipt_controls, "different-own-and-publication", lambda: receipt(synthetic, changed))
    proposed = {
        **parent, "schema": accounting.CURRENT_SCHEMA,
        "six_target_actual_own_publication_and_current_semantic_reports_equal": True,
        "six_target_full_current_semantic_exit_code": 0,
        "independent_exact_six_target_source_accounting": result,
        "six_target_actual_prior_candidate_layer_identity": layer,
        "Rstar_conditional_frontier_pending_subtrees": 5637,
        "Rstar_conditional_frontier_families": frontier["families"],
        "six_target_new_strict_whole_source_prefixes": 5546,
        "six_target_source_conditional_pending_subtrees": 11183,
        "six_target_candidate_whole_roots_removed": 0,
    }
    accounting.current_gate(proposed, parent, result, layer)
    for name, field, value in (
        ("stale-unfiltered-frontier", "Rstar_conditional_frontier_pending_subtrees", 11183),
        ("smaller-candidate-objective-substituted", "candidate_angle_unresolved_closed_boxes", 16),
        ("original-U-frontier-deleted", "original_U_current_pending_subtrees_unchanged", 0),
        ("LOCAL-allowance-discarded", "original_52_coordinate_local_allowance_unchanged", "0"),
        ("candidate-identity-reset", "six_target_actual_prior_candidate_layer_identity", {}),
        ("wrong-family-counts", "Rstar_conditional_frontier_families", parent["Rstar_conditional_frontier_families"]),
        ("old-proof-receipt-lost", "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked", 214),
        ("raw-candidate-path-discarded", "current_candidate_type_paths", 0),
    ):
        changed = dict(proposed)
        changed[field] = value
        rejected(current_controls, name, lambda changed=changed:
                 accounting.current_gate(changed, parent, result, layer))
    report = {
        "schema": "N26-six-target-current-independent-accounting-controls-v1",
        "verified": False, "new_formal_geometric_payments": 0,
        "tested_accounting_sha256": binding.sha(accounting.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "actual_parent_current_sha256": parent_digest,
        "actual_source_frontier_sha256": binding.sha(folder/"SOURCE-FRONTIER.json"),
        "actual_independent_six_target_source_partition": result,
        "actual_invalid_partition_shadow_and_witness_controls_rejected": partition_controls,
        "synthetic_invalid_geometry_receipt_controls_rejected": receipt_controls,
        "synthetic_invalid_current_scope_controls_rejected": current_controls,
        "synthetic_receipts_NOT_actual_geometry_or_current_acceptance": True,
        "actual_full_geometry_and_current_mains_NOT_executed_by_controls": True,
        "actual_formal_frontier_STILL": 11183, "actual_candidate_whole_roots_STILL": 25,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_six_target_current_accounting_controls_completed": True,
        "actual_partition_controls": len(partition_controls),
        "synthetic_receipt_controls": len(receipt_controls), "synthetic_current_controls": len(current_controls),
        "actual_geometry_or_current_admission": False, "new_formal_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
