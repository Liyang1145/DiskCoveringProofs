"""Explicit SYNTHETIC current/receipt controls using REAL16-root geometry DATA.

No synthetic current, parent or geometry acceptance is written to disk.
The sole report is unverified unit evidence with ZERO formal payments.
Complete real frozen geometry/current/final execution remains mandatory.
"""

from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_identity_after_midarc as identity
import n26_midarc_current_accounting as accounting
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-midarc-current-identity-and-accounting-controls-v1.json")
    if output.exists():
        raise FileExistsError(output)
    six_current_path = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
    base, base_digest = binding.read(six_current_path), binding.sha(six_current_path)
    candidate = Path("outputs/n26-current-candidate-mixed-curvature-covers-v1")
    source_report = binding.read(candidate / "VERIFIED.json")
    source_pub_path = Path("outputs/n26-current-candidate-mixed-curvature-covers-published-replay-v1.json")
    if (
        binding.read(source_pub_path) != source_report
        or binding.sha(source_pub_path) != binding.sha(candidate / "VERIFIED.json")
        or source_report["unresolved_closed_angle_boxes"] != 16
    ):
        raise ValueError("midarc header controls require ACTUAL completed mixed16-root geometry source DATA")
    source_control_path = Path("outputs/n26-midarc-SIX-filtered-source-accounting-controls-v1.json")
    source_control = binding.read(source_control_path)
    if source_control["verified"] is not False or source_control["new_formal_geometric_payments"] != 0:
        raise ValueError("midarc current tests require explicit unaccepted source accounting controls")
    result = source_control["actual_independent_NEW680_source_partition"]
    original_proof_path = Path("work/n26-six-core-target-filled-ear-proof.md")
    paths = [
        candidate / "VERIFIED.json", candidate / "PENDING-ANGLES.json",
        candidate / "REMAINING-ROOT-HISTORY.json", candidate / identity.previous.previous.CHECKER,
        original_proof_path,
    ]
    inventory = {linux(path): binding.sha(path) for path in paths}
    parent_path = Path("outputs/SYNTHETIC-mixed16-current-header-NOT-written.json")
    parent_digest, current_digest, final_digest = "b"*64, "c"*64, "d"*64
    parent = {
        **base, "schema": identity.previous.CURRENT_SCHEMA, "files": inventory,
        "candidate_angle_unresolved_closed_boxes": 16,
        "actual_current_candidate_acceptance": linux(candidate / "VERIFIED.json"),
        "actual_current_candidate_pending_angles": linux(candidate / "PENDING-ANGLES.json"),
        "actual_current_candidate_remaining_history": linux(candidate / "REMAINING-ROOT-HISTORY.json"),
        "mixed_curvature_actual_published_replay_matched_and_semantics_replayed_here": True,
        "mixed_curvature_source_is_actual_latest_candidate_layer": True,
        "all_newest_owned_histories_retained_identically": True,
        "remaining_latest_partial_root_histories": 1,
        "SYNTHETIC_mixed_parent_header_NOT_real_current_or_final": True,
    }
    parent_key = str(parent_path.resolve())

    def reader(path):
        return parent if str(binding.local_path(path).resolve()) == parent_key else binding.read(path)

    def hasher(path):
        return parent_digest if str(binding.local_path(path).resolve()) == parent_key else binding.sha(path)

    layer = identity.previous.gate(parent, parent_digest, candidate, reader=reader, hasher=hasher)
    families = deepcopy(parent["Rstar_conditional_frontier_families"])
    for family, counts in zip(families, result["independent_family_conservation"]):
        family.update({
            "midarc_filled_patch_NEW_whole_subtrees": counts["strict_NEW_midarc_whole_subtrees"],
            "pending_subtrees": counts["retained_subtrees"],
            "unresolved_terminal_subtrees": counts["all_raw_terminals_retained"],
            "family_exhausted": counts["retained_subtrees"] == 0,
        })
    current = {key: value for key, value in parent.items() if key not in identity.POINTERS}
    current.update({
        "schema": identity.CURRENT_SCHEMA, "files": {**inventory, linux(parent_path): parent_digest},
        "prior_current_audit_sha256": parent_digest, "midarc_parent_audit_file": linux(parent_path),
        "midarc_actual_own_publication_and_current_semantic_reports_equal": True,
        "midarc_full_current_semantic_exit_code": 0, "midarc_candidate_whole_roots_removed": 0,
        "candidate_layer_and_all_latest_partial_histories_unchanged_by_midarc_rule": True,
        "Rstar_conditional_frontier_pending_subtrees": 4957,
        "Rstar_conditional_frontier_families": families,
        "midarc_source_conditional_pending_subtrees": 5637, "midarc_new_strict_whole_source_prefixes": 680,
        "midarc_actual_prior_candidate_layer_identity": layer,
        "midarc_independent_exact_source_accounting": result,
        "SYNTHETIC_midarc_header_NOT_real_current_or_geometry_acceptance": True,
    })
    snapshot = identity.gate(current, current_digest, candidate, reader=reader, hasher=hasher)
    accounting.current_gate(current, parent, result, layer)
    old_source = Path("outputs/n26-current-candidate-owned-forest-v8")
    if identity.gate(base, base_digest, old_source) != identity.previous.gate(base, base_digest, old_source):
        raise AssertionError("new midarc adapter changed actual old-schema delegation")
    identity_rejected = []

    def reject_identity(name, changed, digest=current_digest, chosen=candidate):
        try:
            identity.gate(changed, digest, chosen, reader=reader, hasher=hasher)
        except (ValueError, KeyError, TypeError):
            identity_rejected.append(name)
        else:
            raise AssertionError("invalid midarc candidate ancestry accepted: " + name)

    for name, field, value in (
        ("unbound-current", "current_bound_bytes_rechecked", False),
        ("full-main-not-completed", "midarc_full_current_semantic_exit_code", 1),
        ("own-publication-semantic-mismatch", "midarc_actual_own_publication_and_current_semantic_reports_equal", False),
        ("old25-candidate-objective-restored", "candidate_angle_unresolved_closed_boxes", 25),
        ("unfiltered5637-frontier-restored", "Rstar_conditional_frontier_pending_subtrees", 5637),
        ("original11183-source-restored", "midarc_source_conditional_pending_subtrees", 11183),
        ("NEW680-count-changed", "midarc_new_strict_whole_source_prefixes", 679),
        ("radius-promoted-to-original-U", "radius_scope", "unconditional-original-U"),
        ("original-LOCAL-erased", "original_52_coordinate_local_allowance_unchanged", "0"),
        ("global-lower-bound-overclaim", "global_lower_bound_proved", True),
        ("candidate-payment-in-enumeration", "midarc_candidate_whole_roots_removed", 1),
        ("latest-histories-discarded", "candidate_layer_and_all_latest_partial_histories_unchanged_by_midarc_rule", False),
        ("original-U-state-erased", "original_U_current_pending_subtrees_unchanged", 0),
        ("unclosed-n26-skipped-to-n27", "n27_started", True),
    ):
        changed = dict(current, **{field: value})
        reject_identity(name, changed)
    reject_identity("enumeration-relabelled-as-candidate-owner", dict(
        current, actual_current_candidate_acceptance=linux(candidate / "VERIFIED.json")))
    reject_identity("parent-ancestry-cycle", current, digest=parent_digest)
    changed = dict(current, files=dict(current["files"]))
    changed["files"].pop(linux(parent_path))
    reject_identity("actual-parent-not-bound", changed)
    changed = dict(current, files=dict(current["files"]))
    changed["files"].pop(linux(original_proof_path))
    reject_identity("old-proof-dependency-dropped", changed)
    reject_identity("recorded-real-candidate-source-reset", dict(
        current, midarc_actual_prior_candidate_layer_identity={}))
    reject_identity("old-owned8-source-substituted-for-mixed16-source", current, chosen=old_source)
    if len(identity_rejected) != 20:
        raise AssertionError("midarc identity controls incomplete")
    checker_digest = binding.sha(Path("work/verify_midarc_source_geometry.py"))
    body = {
        "entire_actual_ORIGINAL_SIX_filtered_source_prefixes_reconstructed": 5637,
        "strict_NEW_midarc_whole_prefixes": 680,
        "all_original_physical_count_AND_shadow_label_cases_checked": 9172,
        "distinct_patch_locators_AND_original_vs_shadow_set_enumerations_agreed": True,
        "all_raw_complete_candidate_and_competitor_terminals_retained_identically": True,
        "prefix_free_entire_source_and_unpaid_sibling_partition_checked": True,
        "old5546_SIX_whole_prefixes_NOT_repaid": True,
        "fresh_independent_exact_midarc_core_target_identities": accounting.source.independent_targets(),
        "family_conservation": result["independent_family_conservation"],
    }
    accepted = {
        "schema": accounting.source.ACCEPTANCE_SCHEMA, "verified": True,
        "radius_scope": accounting.source.SCOPE, "inherited_source_is_unconditional_at_U": False,
        "executed_checker_file": accounting.CHECKER, "executed_checker_sha256": checker_digest,
        "files": {accounting.CHECKER: checker_digest}, "source_files": inventory,
        "actual_parent_current_sha256": parent_digest, "actual_parent_final_sha256": final_digest,
        "actual_candidate_layer_identity": layer, "radius_upper": parent["r_strict_interval"][1],
        "r_strict_interval": parent["r_strict_interval"],
        "screen_radius_threshold_for_NEW_midarc_rule": str(accounting.source.U),
        "complete_parent_dependency_inventory_rehashed_BEFORE_AND_AFTER": True,
        "prior_completed_parent_semantic_proof_chain_still_bound_NOT_replaced_by_DATA": True,
        "all_actual16_candidate_roots_histories_and_original_LOCAL_retained": True,
        "all_original_counts_AND_shadow_label_placements_freshly_checked_both_ways": True,
        "corner_shadow_is_embedded_LIMIT_NOT26_positive_area_Voronoi_cells": True,
        "written_continuous_midarc_cover_and_embedding_proofs_used_NOT_inferred_from_finite_tests": True,
        "fresh_independent_universal_bridge_scalar_identities": 12,
        "historical_closed_types_retained": 87, "historical_proof_receipts_retained_and_associated": 215,
        "source_actual_current_frontier": 5637,
        "geometry_accepted_filtered_frontier_REQUIRES_CURRENT_AND_FINAL": 4957,
        "strict_NEW_midarc_whole_source_prefixes": 680,
        "old5546_SIX_whole_prefix_payments_preserved_NOT_repaid": True,
        "actual_geometric_scope_negative_controls_rejected": ["SYNTHETIC-NOT-executed"]*10,
        "actual_current_nodes_removed_by_this_OWN_acceptance": 0,
        "new_formal_geometric_payments_by_this_OWN_acceptance": 0,
        "candidate_whole_roots_removed": 0, "original_U_frontier_nodes_removed": 0,
        "unrestricted_reduction_final_joint_acceptance": False, "frozen_geometric_reduction_proved": False,
        **{field: False for field in accounting.source.GLOBAL_FALSE},
        "ENTIRE_actual_source_prefixes_midarc_geometry_and_case_partition_replayed_here": body,
        "independent_complete_actual_remaining_source_accounting": result,
        "SYNTHETIC_receipt_shape_NEVER_written_as_actual_geometry_acceptance": True,
    }
    accounting.receipt_gate(
        parent, parent_digest, final_digest, accepted, accepted, accepted, checker_digest, layer,
    )
    receipt_rejected = []

    def reject_receipt(name, mutation):
        changed = deepcopy(accepted)
        mutation(changed)
        try:
            accounting.receipt_gate(
                parent, parent_digest, final_digest, changed, changed, changed, checker_digest, layer,
            )
        except (ValueError, KeyError, TypeError):
            receipt_rejected.append(name)
        else:
            raise AssertionError("invalid synthetic midarc receipt shape accepted: " + name)

    for name, field, value in (
        ("old-SIX-receipt-used-for-NEW680", "schema", "old-SIX"),
        ("unverified-own-receipt", "verified", False),
        ("wrong-real-candidate-source-identity", "actual_candidate_layer_identity", {}),
        ("unconditional-original-U-receipt", "radius_scope", "unconditional-original-U"),
        ("old11183-receipt-source", "source_actual_current_frontier", 11183),
        ("NEW680-receipt-count-changed", "strict_NEW_midarc_whole_source_prefixes", 679),
        ("own-receipt-claims-formal-U-payment", "original_U_frontier_nodes_removed", 1),
        ("shadow-positive-area-cell-frame", "corner_shadow_is_embedded_LIMIT_NOT26_positive_area_Voronoi_cells", False),
        ("missing-universal-bridge-identity", "fresh_independent_universal_bridge_scalar_identities", 11),
        ("wrong-actual-full-checker", "executed_checker_file", "verify_six_target_source_geometry.py"),
        ("global-optimality-overclaim", "global_optimality_proved", True),
    ):
        reject_receipt(name, lambda row, field=field, value=value: row.update({field: value}))
    reject_receipt("partial-original-prefix-reconstruction", lambda row: row[
        "ENTIRE_actual_source_prefixes_midarc_geometry_and_case_partition_replayed_here"].update(
            entire_actual_ORIGINAL_SIX_filtered_source_prefixes_reconstructed=5636))
    reject_receipt("missing-physical-shadow-case", lambda row: row[
        "ENTIRE_actual_source_prefixes_midarc_geometry_and_case_partition_replayed_here"].update(
            all_original_physical_count_AND_shadow_label_cases_checked=9171))
    reject_receipt("old-source-proof-not-bound", lambda row: row["source_files"].pop(linux(original_proof_path)))
    different = deepcopy(accepted)
    different["SYNTHETIC_report_changed"] = True
    try:
        accounting.receipt_gate(
            parent, parent_digest, final_digest, accepted, accepted, different, checker_digest, layer,
        )
    except ValueError:
        receipt_rejected.append("actual-semantic-report-differs-from-own-publication")
    else:
        raise AssertionError("mismatched synthetic semantic report accepted")
    current_rejected = []
    for name, field, value in (
        ("unfiltered5637-current-restored", "Rstar_conditional_frontier_pending_subtrees", 5637),
        ("old25-candidate-current-restored", "candidate_angle_unresolved_closed_boxes", 25),
        ("full-current-main-not-completed", "midarc_full_current_semantic_exit_code", 1),
        ("original-U-state-discarded", "original_U_current_pending_subtrees_unchanged", 0),
        ("original-LOCAL-remainder-erased", "original_52_coordinate_local_allowance_unchanged", "0"),
        ("one-old-proof-receipt-lost", "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked", 214),
        ("global-lower-bound-current-overclaim", "global_lower_bound_proved", True),
        ("n27-started-before-n26-closure", "n27_started", True),
        ("candidate-pointer-under-new-enumeration-schema", "actual_current_candidate_acceptance", "wrong"),
        ("recorded-candidate-identity-changed", "midarc_actual_prior_candidate_layer_identity", {}),
    ):
        changed = dict(current, **{field: value})
        try:
            accounting.current_gate(changed, parent, result, layer)
        except (ValueError, KeyError, TypeError):
            current_rejected.append(name)
        else:
            raise AssertionError("invalid synthetic midarc current scope accepted: " + name)
    changed = dict(current, files=dict(current["files"]))
    changed["files"].pop(linux(original_proof_path))
    try:
        accounting.current_gate(changed, parent, result, layer)
    except ValueError:
        current_rejected.append("old-current-proof-dependency-dropped")
    else:
        raise AssertionError("dropped original current dependency accepted")
    if len(receipt_rejected) != 15 or len(current_rejected) != 11:
        raise AssertionError("midarc receipt/current controls incomplete")
    report = {
        "schema": "N26-midarc-current-synthetic-identity-and-accounting-controls-v1",
        "verified": False, "new_formal_geometric_payments": 0,
        "all_parent_current_final_and_geometry_receipt_headers_explicitly_SYNTHETIC": True,
        "actual_mixed16_root_source_geometry_DATA_preserved": True,
        "actual_SIX_compositor_identity_delegation_checked_NOT_final_adoption": True,
        "synthetic_parent_path_NEVER_written_or_monkey_patched": True,
        "synthetic_actual_mixed_geometry_source_identity_snapshot_NOT_formal_parent": layer,
        "synthetic_midarc_wrapper_identity_snapshot_NOT_actual_current": snapshot,
        "actual_independent_remaining_source_partition": result,
        "invalid_candidate_ancestry_controls_rejected": identity_rejected,
        "synthetic_invalid_geometry_receipt_controls_rejected": receipt_rejected,
        "synthetic_invalid_current_scope_controls_rejected": current_rejected,
        "actual_mixed_acceptance_sha256": binding.sha(candidate / "VERIFIED.json"),
        "actual_mixed_pending_angles_sha256": binding.sha(candidate / "PENDING-ANGLES.json"),
        "actual_remaining_source_accounting_controls_sha256": binding.sha(source_control_path),
        "tested_identity_module_sha256": binding.sha(identity.__file__),
        "tested_accounting_module_sha256": binding.sha(accounting.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "candidate_whole_roots_removed": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "midarc_explicit_new_schema_and_actual_source_header_controls_completed": True,
        "invalid_identity_controls": len(identity_rejected),
        "invalid_receipt_controls": len(receipt_rejected),
        "invalid_current_controls": len(current_rejected),
        "all_headers_SYNTHETIC_NOT_actual_admission": True, "new_formal_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
