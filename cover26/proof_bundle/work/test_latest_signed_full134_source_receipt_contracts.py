"""Synthetic extended-source receipt guards + actual old receipt rejection ONLY.

No complete source/geometry execution and no synthetic acceptance file is
created. A real adopted latest layer does not exist until its own gates pass.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import n26_current_latest_signed_full134_candidate_source as source
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("actual-current", "actual-final", "actual-source", "actual-source-replay", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    owner_digest, checker_digest = "1"*64, "2"*64
    owner = {
        "schema": source.accounting.CURRENT_SCHEMA,
        "current_bound_bytes_rechecked": True, "prior_completed_full_chain_semantic_replay_still_bound": True,
        "radius_scope": binding.SCOPE, "global_lower_bound_proved": False, "global_optimality_proved": False,
        "full_catalog_complete": False, "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "original_U_current_pending_subtrees_unchanged": 3922, "candidate_angle_unresolved_closed_boxes": 3,
        "r_strict_interval": ["1/5", "1/4"], "files": {"SYNTHETIC-NOT-REAL": "3"*64},
        "latest_forest_actual_published_replay_matched_and_semantics_replayed_here": True,
        "latest_forest_source_is_actual_latest_candidate_layer": True,
        "all_newest_owned_histories_retained_identically": True,
        "latest_forest_actual_full_semantic_exit_code": 0,
    }
    accepted = {
        "schema": source.checker.SCHEMA, "verified": True, "radius_scope": "same-root-Rstar",
        "radius_upper": "1/4", "unresolved_closed_angle_boxes": 3, "remaining_root_partial_histories_retained": 2,
        "executed_checker_file": source.checker.CHECKER, "executed_checker_sha256": checker_digest,
        "files": {source.checker.CHECKER: checker_digest}, "negative_controls_rejected": ["fixture-"+str(i) for i in range(21)],
        "accepted_forest_modes": source.checker.MODES,
        "actual_full_source_replay": {"ENTIRE_actual_source_model_old_payments_and_latest_history_replayed_here": True},
        "actual_latest_root25_v3_and_root28_grown_v9_replayed_not_reset": True,
        "actual_old_baselines_and_every_strict_ledger_freshly_reconstructed": True,
        "source_identity_and_arithmetic_controls_NOT_used_as_geometry_substitutes": True,
        "LOCAL_equality_feasible_regions_never_declared_empty": True,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "full_catalog_complete": False, "n27_started": False,
    }
    final = {
        "schema": "N26-independent-latest-signed-grown-full134rod-current-final-rehash-v1",
        "current_audit_sha256": owner_digest, "all_current_file_digests_rehashed": True,
        "current_file_digests_rechecked": 1, "candidate_angle_unresolved_closed_boxes": 3,
        "remaining_latest_partial_root_histories": 2,
        "actual_own_geometry_publication_and_current_semantic_replays_equal": True,
        "independent_exact_root_and_newest_history_accounting": {
            "exact_source_root_partition_and_all_latest_histories_checked": True},
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
    publication, semantic = deepcopy(accepted), deepcopy(accepted)
    positive = source.receipt_gate(owner, final, owner_digest, accepted, publication, semantic, checker_digest)
    rejected = []

    def reject(label, mutation):
        own, rehash, acc, pub, sem = (
            deepcopy(owner), deepcopy(final), deepcopy(accepted), deepcopy(publication), deepcopy(semantic))
        mutation(own, rehash, acc, pub, sem)
        try:
            source.receipt_gate(own, rehash, owner_digest, acc, pub, sem, checker_digest)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid synthetic latest source receipt association accepted: "+label)

    for label, mutation in (
        ("owner-final-current-snapshot-forged", lambda o, f, a, p, s: f.update(current_audit_sha256="0"*64)),
        ("owner-final-inventory-rehash-incomplete", lambda o, f, a, p, s: f.update(all_current_file_digests_rehashed=False)),
        ("owner-final-inventory-count-forged", lambda o, f, a, p, s: f.update(current_file_digests_rechecked=0)),
        ("owner-final-legacy-schema-laundered", lambda o, f, a, p, s: f.update(
            schema="N26-independent-final-current-inventory-rehash-v1")),
        ("owner-final-source-semantic-equality-marker-omitted", lambda o, f, a, p, s: f.update(
            actual_own_geometry_publication_and_current_semantic_replays_equal=False)),
        ("owner-final-remaining-root-count-forged", lambda o, f, a, p, s: f.update(candidate_angle_unresolved_closed_boxes=0)),
        ("owner-final-latest-history-count-forged", lambda o, f, a, p, s: f.update(remaining_latest_partial_root_histories=0)),
        ("owner-final-whole-history-accounting-marker-omitted", lambda o, f, a, p, s: f[
            "independent_exact_root_and_newest_history_accounting"].update(
                exact_source_root_partition_and_all_latest_histories_checked=False)),
        ("source-old-owned-receipt-laundered-as-latest", lambda o, f, a, p, s: a.update(schema=source.prior_source.owned.SCHEMA)),
        ("source-unaccepted-latest-receipt", lambda o, f, a, p, s: a.update(verified=False)),
        ("source-publication-replay-differs", lambda o, f, a, p, s: p.update(verified=False)),
        ("source-current-semantic-replay-differs", lambda o, f, a, p, s: s.update(verified=False)),
        ("source-frozen-main-bytes-forged", lambda o, f, a, p, s: a.update(executed_checker_sha256="0"*64)),
        ("source-entire-model-marker-replaced-by-identity", lambda o, f, a, p, s: a[
            "actual_full_source_replay"].update(ENTIRE_actual_source_model_old_payments_and_latest_history_replayed_here=False)),
        ("source-original-LOCAL-expanded", lambda o, f, a, p, s: a.update(original_52_coordinate_local_allowance_unchanged="1")),
        ("source-radius-promoted-to-original-U", lambda o, f, a, p, s: a.update(radius_upper="234701/1000000")),
        ("source-global-proof-level-promoted", lambda o, f, a, p, s: a.update(global_optimality_proved=True)),
    ):
        reject(label, mutation)
    current, actual_final = binding.read(args.actual_current), binding.read(args.actual_final)
    actual_accepted, actual_replay = binding.read(args.actual_source / "VERIFIED.json"), binding.read(args.actual_source_replay)
    actual_digest = binding.sha(args.actual_current)
    source.prior_source.pair_gate(current, actual_final, actual_digest)
    if actual_accepted != actual_replay:
        raise ValueError("actual old geometry receipt/publication differs before refusal test")
    old_checker = args.actual_source / "verify_owned_candidate_forests.py"
    try:
        source.receipt_gate(current, actual_final, actual_digest, actual_accepted,
                            actual_replay, deepcopy(actual_replay), binding.sha(old_checker))
    except (ValueError, KeyError, TypeError, IndexError):
        actual_old_refused = True
    else:
        raise AssertionError("ACTUAL older accepted source was relabelled as adopted extended layer")
    if "n26_typed_arithmetic_context" in source.sys.modules:
        raise ValueError("new extended source receipt interface imported a typed geometry/source cache")
    report = {
        "schema": "N26-independent-adopted-latest-forest-source-receipt-contract-controls-v1",
        "synthetic_receipt_only_positive_shape": positive,
        "synthetic_invalid_adopted_layer_and_receipt_contract_controls_rejected": rejected,
        "ACTUAL_completed_older_source_receipt_REJECTED_as_new_extended_layer": actual_old_refused,
        "actual_old_current_sha256": actual_digest,
        "actual_old_final_sha256": binding.sha(args.actual_final),
        "actual_old_acceptance_sha256": binding.sha(args.actual_source / "VERIFIED.json"),
        "synthetic_shapes_NOT_an_actual_latest_source_geometry_or_current_acceptance": True,
        "ENTIRE_frozen_main_original_model_latest_forest_and_history_replay_NOT_executed": True,
        "typed_context_or_diagnostic_producer_NOT_imported": True,
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_complete_extended_source_adapter_sha256": binding.sha(source.__file__),
        "tested_adopted_layer_identity_sha256": binding.sha(source.identity.__file__),
        "tested_independent_final_receipt_gate_sha256": binding.sha(source.independent_final.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "extended_source_receipt_contract_controls_completed": True,
        "synthetic_invalid_receipts": len(rejected), "ACTUAL_old_source_relabel_refused": actual_old_refused,
        "actual_complete_source_geometry_NOT_executed": True, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
