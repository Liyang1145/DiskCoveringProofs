"""Synthetic new-schema ownership guards plus actual old-schema identity only."""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_identity_with_mixed_curvature as identity
import verify_conditional_force_stage as binding


def digest(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    for name in ("actual-owned-current", "actual-owned-source", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    folder = Path(__file__).with_name("_synthetic_mixed_identity_source_NOT_real")
    parent_path = Path(__file__).with_name("_synthetic_mixed_current_NOT_real.json")
    keys = [linux(folder / name) for name in
            ("VERIFIED.json", "PENDING-ANGLES.json", identity.CHECKER)]
    parent_key = linux(parent_path)
    acceptance_sha, pending_sha, checker_sha = map(digest, keys)
    current_sha, parent_sha = digest("synthetic-enumeration-current"), digest("synthetic-mixed-parent")
    rows = [{"index": index} for index in range(16)]
    acceptance = {
        "schema": identity.ACCEPTANCE_SCHEMA, "verified": True,
        "radius_scope": "same-root-Rstar", "radius_upper": "1/4",
        "unresolved_closed_angle_boxes": 16,
        "executed_checker_file": identity.CHECKER,
        "executed_checker_sha256": checker_sha,
        "files": {identity.CHECKER: checker_sha},
        "accepted_curvature_modes": ["constant-hull", "integrated-Taylor"],
        "negative_controls_rejected": ["synthetic-control-" + str(index) for index in range(29)],
        "original_full_latest_model_source_all_old_payments_and_history_replayed": True,
        "actual_newest_per_root_owned_forests_retained_identically": True,
    }
    inventory = dict(zip(keys, (acceptance_sha, pending_sha, checker_sha)))
    parent = {
        "schema": identity.CURRENT_SCHEMA,
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "radius_scope": binding.SCOPE, "global_optimality_proved": False,
        "candidate_angle_unresolved_closed_boxes": 16,
        "r_strict_interval": ["1/5", "1/4"], "files": dict(inventory),
        "actual_current_candidate_acceptance": keys[0],
        "actual_current_candidate_pending_angles": keys[1],
        "mixed_curvature_actual_published_replay_matched_and_semantics_replayed_here": True,
        "mixed_curvature_source_is_actual_latest_candidate_layer": True,
        "all_newest_owned_histories_retained_identically": True,
    }
    current = {
        "schema": identity.original.ENUMERATION_SCHEMA,
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "radius_scope": binding.SCOPE, "global_optimality_proved": False,
        "candidate_angle_unresolved_closed_boxes": 16,
        "r_strict_interval": ["1/5", "1/4"], "prior_current_audit_sha256": parent_sha,
        "files": {**inventory, parent_key: parent_sha},
    }
    records = {keys[0]: acceptance, keys[1]: rows, parent_key: parent}
    hashes = {**inventory, parent_key: parent_sha}

    def check(cur=current, data=records, byte_hashes=hashes, source=folder):
        return identity.gate(
            cur, current_sha, source,
            reader=lambda path: deepcopy(data[linux(binding.local_path(path))]),
            hasher=lambda path: byte_hashes[linux(binding.local_path(path))])

    check()
    rejected = []

    def reject(name, mutation):
        cur, data, byte_hashes = deepcopy(current), deepcopy(records), dict(hashes)
        mutation(cur, data, byte_hashes)
        try:
            check(cur, data, byte_hashes)
        except (ValueError, KeyError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError("invalid mixed candidate identity accepted: " + name)

    reject("mixed-admission-semantic-marker-omitted",
           lambda cur, data, hs: data[parent_key].update(
               mixed_curvature_actual_published_replay_matched_and_semantics_replayed_here=False))
    reject("new-source-schema-relabelled-as-old-owned",
           lambda cur, data, hs: data[keys[0]].update(schema="old-owned-schema"))
    reject("actual-own-checker-renamed",
           lambda cur, data, hs: data[keys[0]].update(
               executed_checker_file="verify_owned_candidate_forests.py"))
    reject("actual-own-checker-bytes-changed",
           lambda cur, data, hs: hs.update({keys[2]: "0" * 64}))
    reject("own-checker-not-bound-in-current",
           lambda cur, data, hs: cur["files"].pop(keys[2]))
    reject("one-curvature-mode-omitted",
           lambda cur, data, hs: data[keys[0]].update(accepted_curvature_modes=["constant-hull"]))
    reject("an-actual-mode-control-omitted",
           lambda cur, data, hs: data[keys[0]]["negative_controls_rejected"].pop())
    reject("remaining-whole-root-count-changed",
           lambda cur, data, hs: data[parent_key].update(candidate_angle_unresolved_closed_boxes=15))
    reject("half-ownership-pointer-missing",
           lambda cur, data, hs: data[parent_key].pop("actual_current_candidate_pending_angles"))
    reject("bound-parent-bytes-changed",
           lambda cur, data, hs: hs.update({parent_key: "0" * 64}))
    reject("bound-parent-missing",
           lambda cur, data, hs: cur["files"].pop(parent_key))
    reject("latest-partial-histories-not-preserved",
           lambda cur, data, hs: data[parent_key].update(all_newest_owned_histories_retained_identically=False))
    reject("source-geometry-gate-omitted",
           lambda cur, data, hs: data[keys[0]].update(
               original_full_latest_model_source_all_old_payments_and_history_replayed=False))
    reject("boolean-root-index",
           lambda cur, data, hs: data[keys[1]][0].update(index=True))
    reject("duplicate-remaining-whole-root-index",
           lambda cur, data, hs: data[keys[1]][0].update(index=1))
    try:
        check(source=folder.with_name("_synthetic_older_equal_count_source_NOT_real"))
    except (ValueError, KeyError):
        rejected.append("older-source-with-equal-count-and-rows-rejected")
    else:
        raise AssertionError("mixed candidate identity reset to an equal-count older source")
    # Real old-schema delegation reads the completed owned CURRENT audit only.
    # This is identity inspection, not its independent-final adoption.
    actual_sha = binding.sha(args.actual_owned_current)
    actual = identity.gate(
        binding.read(args.actual_owned_current), actual_sha, args.actual_owned_source)
    report = {
        "schema": "N26-explicit-mixed-candidate-identity-regression-v1",
        "synthetic_new_schema_and_enumeration_ancestry_identity_passed": True,
        "synthetic_invalid_identity_controls_rejected": rejected,
        "actual_old_schema_delegation_identity_snapshot": actual,
        "actual_snapshot_is_identity_only_NOT_geometry_or_final_current_adoption": True,
        "synthetic_16_root_fixture_is_NOT_an_actual_current_source": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "tested_identity_module_sha256": binding.sha(identity.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "global_optimality_proved": False,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
