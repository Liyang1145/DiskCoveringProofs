"""Synthetic structural controls using REAL completed mixed and SIX geometry DATA.

No completed SIX parent/current/final is fabricated on disk. Passing these
pure metadata/partition guards is NOT geometry admission or formal progress
in the root/frontier counts. The real frozen mains and actual finals remain
required. The sealed old accounting routine is reused unchanged.
"""

from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_mixed_after_six_current_accounting as accounting
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-mixed-after-six-current-accounting-controls-v1.json")
    if output.exists():
        raise FileExistsError(output)
    overlay = Path("outputs/n26-current-candidate-mixed-curvature-covers-v1")
    frontier_path = Path("outputs/n26-current28-six-target-source-geometry-v1/FRONTIER.json")
    old_path = Path("outputs/n26-twenty-eighth-conditional-current-audit-v28-sparse-v1-strict-with-owned8-scope.json")
    frontier, old = binding.read(frontier_path), binding.read(old_path)
    frontier_digest = binding.sha(frontier_path)
    accepted = binding.read(overlay / "VERIFIED.json")
    data = {}
    for name in ("SOURCE-PENDING-ANGLES.json", "ROOT-PAYMENTS.json", "PENDING-ANGLES.json",
                 "SOURCE-ROOT-HISTORY.json", "REMAINING-ROOT-HISTORY.json", "CERTIFICATE.json"):
        if binding.sha(overlay / name) != accepted["files"][name]:
            raise ValueError("control actual geometry DATA changed: " + name)
        data[name] = binding.read(overlay / name)
    digest = "b" * 64
    # Small explicit synthetic inventories avoid treating repeated 273k-file
    # hashing as a unit test. Complete-current executors still hash them all.
    synthetic_inventory = {
        linux(frontier_path): frontier_digest,
        "synthetic-required-old-proof-NOT-a-real-file": "c" * 64,
    }
    parent = {
        **old, "schema": accounting.identity.SIX_SCHEMA,
        "files": synthetic_inventory,
        "six_target_actual_own_publication_and_current_semantic_reports_equal": True,
        "six_target_full_current_semantic_exit_code": 0,
        "candidate_layer_and_all_latest_partial_histories_unchanged_by_six_target_rule": True,
        "six_target_candidate_whole_roots_removed": 0,
        "six_target_new_strict_whole_source_prefixes": 5546,
        "Rstar_conditional_frontier_pending_subtrees": 5637,
        "Rstar_conditional_frontier_families": frontier["families"],
        "current_frontier_actual_file": linux(frontier_path),
        "synthetic_SIX_parent_header_NOT_actual_current_admission": True,
    }
    final = {
        "schema": accounting.SIX_FINAL_SCHEMA, "current_audit_sha256": digest,
        "all_current_file_digests_rehashed": True,
        "current_file_digests_rechecked": len(synthetic_inventory),
        "actual_own_publication_AND_complete_current_semantic_reports_byte_identical": True,
        "all_actual_latest_owned8_histories_and_raw_terminal_obligations_retained": True,
        "candidate_angle_unresolved_closed_boxes": 25, "candidate_whole_roots_removed": 0,
        "new_strict_whole_prefixes": 5546,
        "Rstar_conditional_frontier_pending_subtrees": 5637,
        "Rstar_conditional_frontier_families": frontier["families"],
        "retained_closed_full_type_codes": 87, "retained_checked_proof_receipts": 215,
        "radius_scope": parent["radius_scope"], "r_strict_interval": parent["r_strict_interval"],
        **{name: False for name in accounting.GLOBAL_FALSE},
        "synthetic_SIX_final_header_NOT_actual_acceptance": True,
    }
    current = {
        **parent, "schema": accounting.CURRENT_SCHEMA,
        "prior_current_audit_sha256": digest,
        "mixed_after_six_actual_completed_parent_pair_bound": True,
        "mixed_after_six_frontier_sha256": frontier_digest,
        "mixed_curvature_actual_published_replay_matched_and_semantics_replayed_here": True,
        "mixed_curvature_actual_full_semantic_exit_code": 0,
        "mixed_curvature_source_is_actual_latest_candidate_layer": True,
        "all_newest_owned_histories_retained_identically": True,
        "current_transport_frontier_unchanged_by_mixed_candidate_covers": True,
        "mixed_curvature_new_whole_source_roots_lower_bounded": 9,
        "mixed_curvature_new_strictly_empty_source_roots": 0,
        "mixed_curvature_new_source_roots_with_original_LOCAL": 9,
        "candidate_angle_unresolved_closed_boxes": 16,
        "remaining_latest_partial_root_histories": 1,
        "LOCAL_equality_feasible_regions_never_declared_empty": True,
        "candidate_transport_global_lower_bound_proved": False,
        "synthetic_mixed_current_header_NOT_actual_admission": True,
    }
    partition = [
        current, accepted, data["SOURCE-PENDING-ANGLES.json"], data["ROOT-PAYMENTS.json"],
        data["PENDING-ANGLES.json"], data["SOURCE-ROOT-HISTORY.json"],
        data["REMAINING-ROOT-HISTORY.json"],
        data["CERTIFICATE.json"]["discharged_actual_source_root_indices"],
    ]
    parent_args = [parent, digest, final, frontier, frontier_path, frontier_digest]
    current_args = [current, parent, digest, frontier, frontier_digest]
    accounting.parent_gate(*parent_args)
    accounting.current_gate(*current_args)
    accounting.source_partition_gate(*partition)
    rejected = []

    def reject(name, gate, original, mutate):
        changed = deepcopy(original)
        mutate(changed)
        try:
            gate(*changed)
        except (ValueError, KeyError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError("invalid mixed-after-SIX accounting accepted: " + name)

    for name, index, field, value in (
        ("uncompleted-SIX-parent", 0, "six_target_full_current_semantic_exit_code", 1),
        ("old11183-frontier-parent-restored", 0, "Rstar_conditional_frontier_pending_subtrees", 11183),
        ("six5546-payment-count-lost", 0, "six_target_new_strict_whole_source_prefixes", 643),
        ("wrong-parent-final-digest", 2, "current_audit_sha256", "d" * 64),
        ("missing-independent-SIX-final", 2, "all_current_file_digests_rehashed", False),
        ("incomplete-parent-final-inventory", 2, "current_file_digests_rechecked", 1),
        ("old-unfiltered-frontier-schema", 3, "schema", "old-unfiltered"),
        ("SIX-final-global-overclaim", 2, "global_optimality_proved", True),
    ):
        reject(name, accounting.parent_gate, parent_args,
               lambda rows, index=index, field=field, value=value: rows[index].update({field: value}))
    reject("different-bound-frontier-digest", accounting.parent_gate, parent_args,
           lambda rows: rows.__setitem__(5, "e" * 64))
    reject("filtered-prefix-omitted", accounting.parent_gate, parent_args,
           lambda rows: rows[3]["pending_states"].pop())
    for name, field, value in (
        ("old11183-frontier-current-restored", "Rstar_conditional_frontier_pending_subtrees", 11183),
        ("SIX-payment-rebound-to-different-frontier", "mixed_after_six_frontier_sha256", "e" * 64),
        ("all25-candidates-reintroduced", "candidate_angle_unresolved_closed_boxes", 25),
        ("LOCAL-equality-marked-empty", "mixed_curvature_new_strictly_empty_source_roots", 9),
        ("source-history-reset", "all_newest_owned_histories_retained_identically", False),
        ("actual-full-mixed-main-not-completed", "mixed_curvature_actual_full_semantic_exit_code", 1),
        ("original-U-frontier-erased", "original_U_current_pending_subtrees_unchanged", 0),
        ("original-LOCAL-erased", "original_52_coordinate_local_allowance_unchanged", "0"),
        ("historical-proof-receipts-lost", "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked", 214),
        ("global-lower-bound-overclaim", "global_lower_bound_proved", True),
        ("unclosed-n26-skipped-to-n27", "n27_started", True),
    ):
        reject(name, accounting.current_gate, current_args,
               lambda rows, field=field, value=value: rows[0].update({field: value}))
    reject("old-bound-proof-dependency-dropped", accounting.current_gate, current_args,
           lambda rows: rows[0].__setitem__("files", {
               linux(frontier_path): frontier_digest,
           }))
    reject("duplicate-discharged-root", accounting.source_partition_gate, partition,
           lambda rows: rows[7].append(rows[7][0]))
    reject("boolean-root-index", accounting.source_partition_gate, partition,
           lambda rows: rows[7].__setitem__(0, True))
    reject("whole-root-payment-omitted", accounting.source_partition_gate, partition,
           lambda rows: rows[3].pop())
    reject("uncovered-root-omitted", accounting.source_partition_gate, partition,
           lambda rows: rows[4].pop())
    reject("paid-root-reintroduced", accounting.source_partition_gate, partition,
           lambda rows: rows[4].append(next(
               row for row in rows[2] if row["index"] == rows[7][0])))
    reject("false-strict-empty-payment", accounting.source_partition_gate, partition,
           lambda rows: rows[3][0].update(source_candidate_root_strictly_empty=True))
    reject("whole-root-not-actually-lower-bounded", accounting.source_partition_gate, partition,
           lambda rows: rows[3][0].update(source_candidate_root_fully_lower_bounded=False))
    reject("root959-latest-history-omitted", accounting.source_partition_gate, partition,
           lambda rows: rows[6].clear())
    reject("root959-history-reset-to-OPEN", accounting.source_partition_gate, partition,
           lambda rows: rows[6][0].update(nodes=[{"kind": "OPEN"}]))
    reject("mixed-negative-control-missing", accounting.source_partition_gate, partition,
           lambda rows: rows[1]["negative_controls_rejected"].pop())
    reject("original-source-model-replay-substituted", accounting.source_partition_gate, partition,
           lambda rows: rows[1].update(original_full_latest_model_source_all_old_payments_and_history_replayed=False))
    reject("different-whole-source-root-row", accounting.source_partition_gate, partition,
           lambda rows: rows[4][0].update(index=777))
    if len(rejected) != accounting.CONTROL_COUNT:
        raise AssertionError("mixed-after-SIX control count disagrees: " + str(len(rejected)))
    report = {
        "schema": "N26-mixed-after-six-synthetic-current-accounting-controls-v1",
        "verified": False, "new_geometric_payments": 0,
        "synthetic_parent_and_current_headers_NOT_actual_admission": True,
        "actual_geometry_DATA_source_root_history_partition_passed": True,
        "actual_six_geometry_DATA_filtered_frontier_preservation_passed": True,
        "invalid_controls_rejected": rejected,
        "actual_mixed_acceptance_sha256": binding.sha(overlay / "VERIFIED.json"),
        "actual_six_geometry_frontier_sha256": frontier_digest,
        "tested_accounting_sha256": binding.sha(accounting.__file__),
        "tested_pure_root_accounting_sha256": binding.sha(accounting.old_final.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "formal_frontier_and_candidate_counts_NOT_changed_by_unit_tests": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "mixed_after_six_pure_accounting_controls_completed": True,
        "invalid_controls_rejected": len(rejected), "new_geometric_payments": 0,
        "synthetic_headers_NOT_actual_current_or_final": True,
    }), flush=True)


if __name__ == "__main__":
    main()
