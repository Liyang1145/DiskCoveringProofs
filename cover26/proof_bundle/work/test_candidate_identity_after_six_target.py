"""Explicit synthetic SIX-header identity guards using ACTUAL unchanged source.

No completed SIX current is forged/written, no geometry/current is accepted.
"""

from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_identity_after_six_target as identity
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-candidate-identity-after-six-target-controls-v1.json")
    if output.exists():
        raise FileExistsError(output)
    parent_path = Path("outputs/n26-twenty-eighth-conditional-current-audit-v28-sparse-v1-strict-with-owned8-scope.json")
    source = Path("outputs/n26-current-candidate-owned-forest-v8")
    parent, parent_digest = binding.read(parent_path), binding.sha(parent_path)
    original_layer = identity.previous.gate(parent, parent_digest, source)
    inventory = dict(parent["files"])
    inventory[linux(parent_path)] = parent_digest
    fixture = {
        **parent, "schema": identity.SIX_SCHEMA, "files": inventory,
        "six_target_actual_own_publication_and_current_semantic_reports_equal": True,
        "six_target_full_current_semantic_exit_code": 0,
        "six_target_candidate_whole_roots_removed": 0,
        "candidate_layer_and_all_latest_partial_histories_unchanged_by_six_target_rule": True,
        "candidate_angle_unresolved_closed_boxes": 25,
        "Rstar_conditional_frontier_pending_subtrees": 5637,
        "six_target_new_strict_whole_source_prefixes": 5546,
        "six_target_source_conditional_pending_subtrees": 11183,
        "six_target_parent_audit_file": linux(parent_path),
        "prior_current_audit_sha256": parent_digest,
        "six_target_actual_prior_candidate_layer_identity": original_layer,
    }
    synthetic_digest = "a"*64
    snapshot = identity.gate(fixture, synthetic_digest, source)
    if (
        snapshot["actual_latest_candidate_acceptance_sha256"] != original_layer["actual_latest_candidate_acceptance_sha256"]
        or snapshot["actual_latest_candidate_pending_angles_sha256"] != original_layer["actual_latest_candidate_pending_angles_sha256"]
        or snapshot["actual_remaining_candidate_whole_roots"] != 25
        or identity.gate(parent, parent_digest, source) != original_layer
    ):
        raise AssertionError("new explicit enumeration wrapper changed the actual old candidate owner")
    rejected = []
    def reject(name, changed, digest=synthetic_digest, chosen=source):
        try:
            identity.gate(changed, digest, chosen)
        except (ValueError, KeyError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError("invalid six-target candidate ancestry accepted: "+name)
    for name, field, value in (
        ("unbound-current-bytes", "current_bound_bytes_rechecked", False),
        ("old-semantic-chain-missing", "prior_completed_full_chain_semantic_replay_still_bound", False),
        ("six-full-semantic-main-not-completed", "six_target_full_current_semantic_exit_code", 1),
        ("six-publication-not-matched", "six_target_actual_own_publication_and_current_semantic_reports_equal", False),
        ("newer-histories-discarded", "candidate_layer_and_all_latest_partial_histories_unchanged_by_six_target_rule", False),
        ("candidate-root-payment-in-enumeration", "six_target_candidate_whole_roots_removed", 1),
        ("smaller-six-candidate-objective", "candidate_angle_unresolved_closed_boxes", 16),
        ("old-unfiltered-frontier-restored", "Rstar_conditional_frontier_pending_subtrees", 11183),
        ("six-exclusion-count-changed", "six_target_new_strict_whole_source_prefixes", 5545),
        ("different-source-partition", "six_target_source_conditional_pending_subtrees", 10905),
        ("radius-scope-promoted-to-U", "radius_scope", "unconditional-original-U"),
        ("original-U-state-discarded", "original_U_current_pending_subtrees_unchanged", 0),
        ("LOCAL-allowance-erased", "original_52_coordinate_local_allowance_unchanged", "0"),
        ("global-optimality-overclaim", "global_optimality_proved", True),
    ):
        changed = dict(fixture)
        changed[field] = value
        reject(name, changed)
    changed = dict(fixture)
    changed["actual_current_candidate_acceptance"] = original_layer["actual_latest_candidate_acceptance"]
    reject("new-six-enumeration-relabelled-as-candidate-layer", changed)
    reject("six-parent-ancestry-cycle", fixture, digest=parent_digest)
    changed = dict(fixture, files=dict(inventory))
    changed["files"].pop(linux(parent_path))
    reject("actual-parent-not-bound", changed)
    changed = dict(fixture, files=dict(inventory))
    changed["files"].pop(next(iter(parent["files"])))
    reject("old-proof-dependency-dropped", changed)
    changed = dict(fixture, six_target_actual_prior_candidate_layer_identity={})
    reject("recorded-source-identity-reset", changed)
    reject("older-equal-count-owned-source-substituted", fixture,
           chosen=Path("outputs/n26-current-candidate-owned-forest-v7"))
    if len(rejected) != 20:
        raise AssertionError("identity controls incomplete")
    report = {
        "schema": "N26-candidate-identity-after-six-target-synthetic-controls-v1",
        "verified": False, "new_geometric_payments": 0,
        "tested_identity_module_sha256": binding.sha(identity.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "actual_parent_current_sha256": parent_digest,
        "actual_old_source_layer_identity_snapshot": original_layer,
        "synthetic_six_header_wrapper_identity_snapshot_NOT_current": snapshot,
        "synthetic_invalid_six_schema_ancestry_controls_rejected": rejected,
        "actual_owned8_source_AND_all_original_25_roots_identically_retained": True,
        "synthetic_six_header_NOT_completed_current_or_geometry_acceptance": True,
        "no_old_sealed_identity_module_modified_or_monkey_patched": True,
        "actual_formal_frontier_STILL": 11183, "candidate_whole_roots_STILL": 25,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_source_new_six_schema_identity_controls_completed": True,
        "invalid_controls_rejected": len(rejected),
        "synthetic_header_is_NOT_actual_current_or_geometry": True,
        "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
