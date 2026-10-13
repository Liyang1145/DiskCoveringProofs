"""Synthetic latest-schema guards and ACTUAL older-source identity delegation.

Synthetic receipt shapes are in memory ONLY and are not geometry/current
acceptance. No geometry checker or full current/final executor is run here.
"""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_identity_with_latest_signed_forests as identity
import recheck_latest_signed_full134_candidate_current as final
import verify_conditional_force_stage as binding


def digest(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    for name in ("actual-current", "actual-source", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    folder = Path(__file__).with_name("_synthetic_latest_signed_source_NOT_REAL")
    parent_path = Path(__file__).with_name("_synthetic_latest_signed_parent_NOT_REAL.json")
    keys = [linux(folder / name) for name in (
        "VERIFIED.json", "PENDING-ANGLES.json", "REMAINING-ROOT-HISTORY.json", identity.CHECKER)]
    parent_key = linux(parent_path)
    current_digest, parent_digest = digest("synthetic-latest-enumeration"), digest("synthetic-latest-owner")
    hashes = {key: digest(key) for key in keys}
    inventory = dict(hashes)
    rows = [{"index": index} for index in (25, 28, 959)]
    history = [{"source_OPEN_index": row["index"], "actual_source_closed_box": row} for row in rows[:2]]
    accepted = {
        "schema": identity.ACCEPTANCE_SCHEMA, "verified": True, "radius_scope": "same-root-Rstar",
        "radius_upper": "1/4", "unresolved_closed_angle_boxes": 3,
        "executed_checker_file": identity.CHECKER, "executed_checker_sha256": hashes[keys[3]],
        "files": {identity.CHECKER: hashes[keys[3]], "REMAINING-ROOT-HISTORY.json": hashes[keys[2]]},
        "accepted_forest_modes": identity.MODES, "negative_controls_rejected": ["synthetic-"+str(i) for i in range(21)],
        "actual_latest_root25_v3_and_root28_grown_v9_replayed_not_reset": True,
        "actual_old_baselines_and_every_strict_ledger_freshly_reconstructed": True,
        "actual_full_source_replay": {"ENTIRE_actual_source_model_old_payments_and_latest_history_replayed_here": True},
        "source_identity_and_arithmetic_controls_NOT_used_as_geometry_substitutes": True,
        "remaining_root_partial_histories_retained": 2,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "LOCAL_equality_feasible_regions_never_declared_empty": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "full_catalog_complete": False, "n27_started": False,
    }
    owner = {
        "schema": identity.CURRENT_SCHEMA, "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "radius_scope": binding.SCOPE, "global_lower_bound_proved": False, "global_optimality_proved": False,
        "candidate_angle_unresolved_closed_boxes": 3, "r_strict_interval": ["1/5", "1/4"],
        "files": dict(inventory), "actual_current_candidate_acceptance": keys[0],
        "actual_current_candidate_pending_angles": keys[1],
        "actual_current_candidate_remaining_history": keys[2],
        "latest_forest_actual_published_replay_matched_and_semantics_replayed_here": True,
        "latest_forest_source_is_actual_latest_candidate_layer": True,
        "all_newest_owned_histories_retained_identically": True,
        "latest_forest_actual_full_semantic_exit_code": 0, "full_catalog_complete": False,
    }
    current = {
        "schema": identity.prior.prior.original.ENUMERATION_SCHEMA,
        "current_bound_bytes_rechecked": True, "prior_completed_full_chain_semantic_replay_still_bound": True,
        "radius_scope": binding.SCOPE, "global_lower_bound_proved": False, "global_optimality_proved": False,
        "candidate_angle_unresolved_closed_boxes": 3, "r_strict_interval": ["1/5", "1/4"],
        "prior_current_audit_sha256": parent_digest,
        "files": {**inventory, parent_key: parent_digest},
    }
    records = {keys[0]: accepted, keys[1]: rows, keys[2]: history, parent_key: owner}
    hashes[parent_key] = parent_digest

    def check(cur=current, data=records, byte_hashes=hashes, source=folder):
        return identity.gate(cur, current_digest, source,
                             reader=lambda path: deepcopy(data[linux(binding.local_path(path))]),
                             hasher=lambda path: byte_hashes[linux(binding.local_path(path))])

    check()
    rejected = []

    def reject(label, mutation):
        cur, data, hs = deepcopy(current), deepcopy(records), dict(hashes)
        mutation(cur, data, hs)
        try:
            check(cur, data, hs)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid latest extended-source identity accepted: "+label)

    changes = (
        ("missing-actual-current-semantic-replay", lambda c, d, h: d[parent_key].update(
            latest_forest_actual_published_replay_matched_and_semantics_replayed_here=False)),
        ("latest-schema-relabelled-as-old-owned", lambda c, d, h:
         d[keys[0]].update(schema="N26-accepted-current-owned-candidate-energy-LOCAL-forests-v1")),
        ("own-executor-renamed-to-old-checker", lambda c, d, h:
         d[keys[0]].update(executed_checker_file="verify_owned_candidate_forests.py")),
        ("own-executor-bytes-forged", lambda c, d, h: h.update({keys[3]: "0"*64})),
        ("own-checker-unbound-from-complete-current", lambda c, d, h: c["files"].pop(keys[3])),
        ("newest-history-pointer-omitted", lambda c, d, h:
         d[parent_key].pop("actual_current_candidate_remaining_history")),
        ("actual-newest-history-bytes-substituted", lambda c, d, h: h.update({keys[2]: "0"*64})),
        ("full134rod-mode-relabelled-as-old-integral", lambda c, d, h:
         d[keys[0]].update(accepted_forest_modes=["integrated-Taylor"])),
        ("actual-own-forest-control-omitted", lambda c, d, h: d[keys[0]]["negative_controls_rejected"].pop()),
        ("ancestor-root-count-changed", lambda c, d, h:
         d[parent_key].update(candidate_angle_unresolved_closed_boxes=2)),
        ("partial-source-ownership-pointers", lambda c, d, h:
         d[parent_key].pop("actual_current_candidate_pending_angles")),
        ("bound-candidate-parent-bytes-changed", lambda c, d, h: h.update({parent_key: "0"*64})),
        ("bound-candidate-parent-missing", lambda c, d, h: c["files"].pop(parent_key)),
        ("latest-history-retention-marker-omitted", lambda c, d, h:
         d[parent_key].update(all_newest_owned_histories_retained_identically=False)),
        ("entire-source-model-replay-replaced-by-identity", lambda c, d, h:
         d[keys[0]]["actual_full_source_replay"].update(
             ENTIRE_actual_source_model_old_payments_and_latest_history_replayed_here=False)),
        ("boolean-whole-root-owner", lambda c, d, h: d[keys[1]][0].update(index=True)),
        ("duplicate-whole-root-owner", lambda c, d, h: d[keys[1]][0].update(index=28)),
        ("newest-partial-history-domain-escaped", lambda c, d, h:
         d[keys[2]][0].update(actual_source_closed_box={"index": -1})),
        ("newest-partial-history-count-forged", lambda c, d, h:
         d[keys[0]].update(remaining_root_partial_histories_retained=0)),
    )
    for label, mutation in changes:
        reject(label, mutation)
    try:
        check(source=folder.with_name("_synthetic_older_equal_count_source_NOT_REAL"))
    except (ValueError, KeyError, TypeError):
        rejected.append("older-equal-count-source-substituted-for-latest")
    else:
        raise AssertionError("older equal-count source was accepted")
    final.acceptance_gate(owner, accepted, deepcopy(accepted), deepcopy(accepted), hashes[keys[3]])
    final_rejected = []

    def bad_final(label, mutation):
        cur, own, replay, semantic = deepcopy(owner), deepcopy(accepted), deepcopy(accepted), deepcopy(accepted)
        mutation(cur, own, replay, semantic)
        try:
            final.acceptance_gate(cur, own, replay, semantic, hashes[keys[3]])
        except (ValueError, KeyError, TypeError, IndexError):
            final_rejected.append(label)
        else:
            raise AssertionError("invalid synthetic final geometry-receipt association accepted: "+label)

    for label, mutation in (
        ("final-current-semantic-replay-marker-missing", lambda c, a, r, s:
         c.update(latest_forest_actual_published_replay_matched_and_semantics_replayed_here=False)),
        ("final-current-latest-source-marker-missing", lambda c, a, r, s:
         c.update(latest_forest_source_is_actual_latest_candidate_layer=False)),
        ("final-current-newest-history-marker-missing", lambda c, a, r, s:
         c.update(all_newest_owned_histories_retained_identically=False)),
        ("final-unaccepted-own-geometry", lambda c, a, r, s: a.update(verified=False)),
        ("final-own-geometry-schema-laundered", lambda c, a, r, s: a.update(schema="OLD-SOURCE")),
        ("final-own-checker-bytes-forged", lambda c, a, r, s: a.update(executed_checker_sha256="0"*64)),
        ("final-one-actual-geometry-control-omitted", lambda c, a, r, s: a["negative_controls_rejected"].pop()),
        ("final-publication-object-differs", lambda c, a, r, s: r.update(verified=False)),
        ("final-current-semantic-object-differs", lambda c, a, r, s: s.update(verified=False)),
        ("final-full-source-model-marker-omitted", lambda c, a, r, s: a["actual_full_source_replay"].update(
            ENTIRE_actual_source_model_old_payments_and_latest_history_replayed_here=False)),
        ("final-radius-endpoint-promoted-to-U", lambda c, a, r, s: a.update(radius_upper="234701/1000000")),
        ("final-original-LOCAL-allowance-enlarged", lambda c, a, r, s:
         a.update(original_52_coordinate_local_allowance_unchanged="1")),
        ("final-mode-laundered-as-integral", lambda c, a, r, s: a.update(accepted_forest_modes=["integrated-Taylor"])),
        ("final-own-partial-geometry-promoted-to-global-optimality", lambda c, a, r, s:
         a.update(global_optimality_proved=True)),
        ("final-current-partial-layer-promoted-to-global-lower-bound", lambda c, a, r, s:
         c.update(global_lower_bound_proved=True)),
        ("final-failed-current-semantic-execution", lambda c, a, r, s:
         c.update(latest_forest_actual_full_semantic_exit_code=1)),
    ):
        bad_final(label, mutation)
    snapshot = identity.gate(binding.read(args.actual_current), binding.sha(args.actual_current), args.actual_source)
    report = {
        "schema": "N26-latest-signed-full134rod-current-identity-and-final-association-controls-v1",
        "synthetic_new_schema_ownership_and_final_association_checked": True,
        "synthetic_invalid_latest_identity_controls_rejected": rejected,
        "synthetic_invalid_final_acceptance_controls_rejected": final_rejected,
        "actual_prior_schema_delegation_identity_snapshot": snapshot,
        "actual_snapshot_is_identity_only_NOT_geometry_or_current_adoption": True,
        "synthetic_latest_receipt_shapes_NOT_an_actual_geometry_acceptance": True,
        "ENTIRE_geometry_current_join_and_independent_final_NOT_executed": True,
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "tested_identity_module_sha256": binding.sha(identity.__file__),
        "tested_independent_final_executor_sha256": binding.sha(final.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "latest_identity_and_final_association_controls_completed": True,
        "identity_rejections": len(rejected), "final_association_rejections": len(final_rejected),
        "actual_old_source_identity_delegation_ONLY": True, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
