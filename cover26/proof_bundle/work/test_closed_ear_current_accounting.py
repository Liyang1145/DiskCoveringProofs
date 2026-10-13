"""Actual-source pure accounting controls; NEVER a geometry acceptance."""

from copy import deepcopy
import json
from pathlib import Path

import n26_closed_ear_current_accounting as accounting
import n26_current_candidate_layer_identity as identity
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-current28-closed-ear-current-accounting-controls-v1.json")
    if output.exists():
        raise FileExistsError("preserve actual controls and use a distinct version if implementation changes")
    folder = Path("outputs/n26-current28-closed-ear-source-geometry-v1")
    manifest = binding.read(folder/"MANIFEST.json")
    parent_path = binding.local_path(manifest["parent_current"])
    final_path = binding.local_path(manifest["parent_final"])
    parent, parent_digest, final_digest = binding.read(parent_path), binding.sha(parent_path), binding.sha(final_path)
    source = binding.read(folder/"SOURCE-FRONTIER.json")
    frontier, ledger = binding.read(folder/"FRONTIER.json"), binding.read(folder/"LOWER-LEDGER.json")
    constants = binding.read(folder/"FAMILY-CONSTANTS.json")
    proofs = {key: binding.sha(folder/name) for key, name in {
        "cap": "UNIT-CAP-PROOF.md", "generic": "GENERIC-SLACK-PROOF.md",
        "bridge": "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md", "ear": "CLOSED-EAR-PROOF.md",
    }.items()}
    layer = identity.gate(parent, parent_digest, binding.local_path(manifest["actual_candidate_source"]))
    result = accounting.partition_gate(parent, source, frontier, ledger, constants, proofs)
    source_controls, receipt_controls, current_controls = [], [], []

    def rejected(target, name, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            target.append(name)
            print(json.dumps({"independent_ear_control_rejected": name,
                              "new_geometric_payments": 0}), flush=True)
        else:
            raise AssertionError("independent ear accounting accepted "+name)

    def changed_ledger():
        rows = list(ledger)
        rows[0] = deepcopy(rows[0])
        return rows

    # These controls operate on the ACTUAL complete source and case ledger.
    controls = []
    controls.append(("missing-actual-whole-prefix-payment", source, frontier, ledger[1:], constants))
    controls.append(("duplicate-actual-whole-prefix-payment", source, frontier, ledger+ledger[:1], constants))
    rows = changed_ledger()
    rows[0]["source_index"] = -1
    controls.append(("wrong-source-index-owner", source, frontier, rows, constants))
    rows = changed_ledger()
    rows[0]["original_physical_count_and_all_shadow_label_placement_cases"].pop()
    controls.append(("missing-original-or-shadow-placement-case", source, frontier, rows, constants))
    rows = changed_ledger()
    rows[0]["original_physical_count_and_all_shadow_label_placement_cases"][0][
        "four_DISTINCT_ORIGINAL_nonowners_required"] = 3
    controls.append(("three-instead-of-four-core-owners", source, frontier, rows, constants))
    rows = changed_ledger()
    rows[0]["closed_embedded_limit_patch"]["consecutive_boundary_triangle"][2] += 1
    controls.append(("different-filled-boundary-triangle", source, frontier, rows, constants))
    changed = dict(source, inherited_source_is_unconditional_at_U=True)
    controls.append(("conditional-source-promoted-to-U", changed, frontier, ledger, constants))
    changed = dict(constants, external_n8_theorem_assumed=False)
    controls.append(("external-original-nonowner-bound-hidden", source, frontier, ledger, changed))
    changed = {**source, "pending_states": list(source["pending_states"])}
    index = ledger[0]["source_index"]
    changed["pending_states"][index] = dict(changed["pending_states"][index])
    changed["pending_states"][index]["next"] += 1
    controls.append(("different-actual-introduced-label-count", changed, frontier, ledger, constants))
    changed = {**frontier, "pending_states": list(frontier["pending_states"])}
    changed["pending_states"][0] = dict(changed["pending_states"][0], prefix=[-1])
    controls.append(("changed-unpaid-sibling", source, changed, ledger, constants))
    changed = dict(frontier, pending_states=frontier["pending_states"][1:])
    controls.append(("missing-unpaid-sibling", source, changed, ledger, constants))
    changed = dict(frontier, pending_states=frontier["pending_states"]+frontier["pending_states"][:1])
    controls.append(("duplicated-unpaid-sibling", source, changed, ledger, constants))
    changed = dict(frontier, pending_states=[row for row in frontier["pending_states"] if not row["terminal"]])
    controls.append(("raw-complete-candidate-terminal-removed", source, changed, ledger, constants))
    rows = changed_ledger()
    rows[0]["exact_projection_margin_above_U"] = "0"
    controls.append(("lost-strict-entire-ear-projection-margin", source, frontier, rows, constants))
    for name, changed_source, changed_frontier, changed_payments, changed_constants in controls:
        rejected(source_controls, name, lambda s=changed_source, f=changed_frontier,
                 p=changed_payments, c=changed_constants: accounting.partition_gate(
                     parent, s, f, p, c, proofs))
    # Deliberately SYNTHETIC shapes only test rejection logic. No actual own
    # geometry or complete-current main is launched or attested by these tests.
    synthetic = {
        "schema": accounting.ACCEPTANCE_SCHEMA, "verified": True,
        "radius_scope": accounting.SCOPE, "inherited_source_is_unconditional_at_U": False,
        "executed_checker_file": accounting.CHECKER,
        "executed_checker_sha256": binding.sha(folder/accounting.CHECKER),
        "files": {accounting.CHECKER: binding.sha(folder/accounting.CHECKER)},
        "actual_parent_current_sha256": parent_digest, "actual_parent_final_sha256": final_digest,
        "actual_candidate_layer_identity": layer,
        "complete_parent_dependency_inventory_rehashed_BEFORE_AND_AFTER": True,
        "prior_completed_parent_semantic_proof_chain_still_bound_NOT_replaced_by_DATA": True,
        "all_original_candidate_terminal_states_owned_roots_histories_and_LOCAL_retained": True,
        "all_original_physical_counts_and_shadow_label_placements_covered": True,
        "corner_copy_is_embedded_LIMIT_not_26_distinct_original_Voronoi_cells": True,
        "written_continuous_dual_starring_and_ear_proofs_are_used_NOT_inferred_from_finite_tests": True,
        "fresh_independent_universal_bridge_scalar_identities": 12,
        "historical_closed_types_retained": 87, "historical_proof_receipts_retained_and_associated": 215,
        "source_actual_current_frontier": 11183,
        "geometry_accepted_filtered_frontier_REQUIRES_CURRENT_AND_FINAL": 10540,
        "strict_new_closed_ear_whole_source_prefixes": 643,
        "r_strict_interval": parent["r_strict_interval"], "radius_upper": parent["r_strict_interval"][1],
        "screen_radius_threshold_for_NEW_ear_rule": str(accounting.U),
        "source_files": parent["files"],
        "ENTIRE_actual_source_prefixes_geometry_and_case_partition_replayed_here":
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
    def check_receipt(changed, publication=None):
        accounting.receipt_gate(
            parent, parent_digest, final_digest, changed,
            changed if publication is None else publication, changed,
            binding.sha(folder/accounting.CHECKER), layer)
    check_receipt(synthetic)
    receipt_changes = [
        ("unverified-shape", "verified", False),
        ("other-acceptance-schema", "schema", "DATA-only"),
        ("original-U-scope", "radius_scope", "unconditional-original-U"),
        ("different-proof-time-parent", "actual_parent_current_sha256", "0"*64),
        ("partial-source-only", "source_actual_current_frontier", 640),
        ("phantom-candidate-root-payment", "candidate_whole_roots_removed", 1),
        ("shadow-limit-not-justified", "corner_copy_is_embedded_LIMIT_not_26_distinct_original_Voronoi_cells", False),
        ("sampled-geometry-substitute", "written_continuous_dual_starring_and_ear_proofs_are_used_NOT_inferred_from_finite_tests", False),
        ("global-completion-overclaim", "global_optimality_proved", True),
        ("different-actual-owned-source", "actual_candidate_layer_identity", {}),
    ]
    for name, field, value in receipt_changes:
        changed = dict(synthetic)
        changed[field] = value
        rejected(receipt_controls, name, lambda changed=changed: check_receipt(changed))
    changed = dict(synthetic, source_files=dict(parent["files"]))
    changed["source_files"].pop(next(iter(changed["source_files"])))
    rejected(receipt_controls, "old-current-dependency-dropped", lambda: check_receipt(changed))
    changed = dict(synthetic, verified=False)
    rejected(receipt_controls, "different-actual-publication", lambda: check_receipt(synthetic, changed))
    proposed = {
        **parent, "schema": accounting.CURRENT_SCHEMA,
        "closed_ear_actual_published_and_complete_current_semantic_replays_equal": True,
        "closed_ear_full_current_semantic_exit_code": 0,
        "independent_exact_closed_ear_source_accounting": result,
        "closed_ear_actual_prior_candidate_layer_identity": layer,
        "closed_ear_candidate_whole_roots_removed": 0,
        "Rstar_conditional_frontier_pending_subtrees": 10540,
        "Rstar_conditional_frontier_families": frontier["families"],
        "closed_ear_new_strict_whole_source_prefixes": 643,
        "closed_ear_source_conditional_pending_subtrees": 11183,
    }
    accounting.current_gate(proposed, parent, result, layer)
    for name, field, value in (
        ("stale-unfiltered-current-frontier", "Rstar_conditional_frontier_pending_subtrees", 11183),
        ("false-smaller-candidate-objective", "candidate_angle_unresolved_closed_boxes", 16),
        ("changed-original-U-frontier", "original_U_current_pending_subtrees_unchanged", 0),
        ("discarded-LOCAL-allowance", "original_52_coordinate_local_allowance_unchanged", "0"),
        ("candidate-source-identity-reset", "closed_ear_actual_prior_candidate_layer_identity", {}),
        ("wrong-family-partition", "Rstar_conditional_frontier_families", parent["Rstar_conditional_frontier_families"]),
        ("missing-old-proof-receipt", "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked", 214),
        ("candidate-raw-path-removed", "current_candidate_type_paths", 0),
    ):
        changed = dict(proposed)
        changed[field] = value
        rejected(current_controls, name, lambda changed=changed: accounting.current_gate(
            changed, parent, result, layer))
    report = {
        "schema": "N26-closed-ear-current-independent-accounting-controls-v1",
        "verified": False, "new_geometric_payments": 0,
        "tested_accounting_sha256": binding.sha(accounting.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "actual_parent_current_sha256": parent_digest,
        "actual_source_frontier_sha256": binding.sha(folder/"SOURCE-FRONTIER.json"),
        "actual_independent_source_partition": result,
        "actual_invalid_source_case_and_partition_controls_rejected": source_controls,
        "synthetic_invalid_receipt_and_scope_controls_rejected": receipt_controls,
        "synthetic_invalid_current_scope_controls_rejected": current_controls,
        "synthetic_receipts_NOT_actual_geometry_or_current_acceptance": True,
        "actual_own_geometry_and_current_main_NOT_executed_by_controls": True,
        "all_existing_current_candidate_histories_proofs_and_ledgers_UNMODIFIED": True,
        "actual_formal_frontier_STILL": 11183, "actual_candidate_whole_roots_STILL": 25,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_independent_source_accounting_controls_completed": True,
        "source_and_shadow_controls": len(source_controls), "receipt_controls": len(receipt_controls),
        "current_scope_controls": len(current_controls), "actual_geometry_admission": False,
        "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
