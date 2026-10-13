"""Synthetic product ownership guards and actual prior-schema identity ONLY."""

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_identity_with_product_forests as identity
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
    folder = Path(__file__).with_name("_synthetic_product_source_NOT_real")
    parent_path = Path(__file__).with_name("_synthetic_product_parent_NOT_real.json")
    keys = [linux(folder/name) for name in ("VERIFIED.json", "PENDING-ANGLES.json", identity.CHECKER)]
    parent_key = linux(parent_path)
    acceptance_sha, pending_sha, checker_sha = map(digest, keys)
    current_sha, parent_sha = digest("synthetic-product-enumeration"), digest("synthetic-product-parent")
    inventory = dict(zip(keys, (acceptance_sha, pending_sha, checker_sha)))
    accepted = {
        "schema": identity.ACCEPTANCE_SCHEMA, "verified": True,
        "radius_scope": "same-root-Rstar", "radius_upper": "1/4",
        "unresolved_closed_angle_boxes": 15,
        "executed_checker_file": identity.CHECKER, "executed_checker_sha256": checker_sha,
        "files": {identity.CHECKER: checker_sha},
        "accepted_curvature_modes": [identity.MODE],
        "negative_controls_rejected": ["synthetic-"+str(index) for index in range(19)],
        "original_full_latest_model_source_all_old_payments_and_history_replayed": True,
        "actual_newest_per_root_owned_forests_retained_identically": True,
    }
    rows = [{"index": index} for index in range(15)]
    parent = {
        "schema": identity.CURRENT_SCHEMA,
        "current_bound_bytes_rechecked": True, "prior_completed_full_chain_semantic_replay_still_bound": True,
        "radius_scope": binding.SCOPE, "global_optimality_proved": False,
        "candidate_angle_unresolved_closed_boxes": 15, "r_strict_interval": ["1/5", "1/4"],
        "files": dict(inventory), "actual_current_candidate_acceptance": keys[0],
        "actual_current_candidate_pending_angles": keys[1],
        "product_actual_published_replay_matched_and_semantics_replayed_here": True,
        "product_source_is_actual_latest_candidate_layer": True,
        "all_newest_owned_histories_retained_identically": True,
    }
    current = {
        "schema": identity.prior.original.ENUMERATION_SCHEMA,
        "current_bound_bytes_rechecked": True, "prior_completed_full_chain_semantic_replay_still_bound": True,
        "radius_scope": binding.SCOPE, "global_optimality_proved": False,
        "candidate_angle_unresolved_closed_boxes": 15, "r_strict_interval": ["1/5", "1/4"],
        "prior_current_audit_sha256": parent_sha, "files": {**inventory, parent_key: parent_sha},
    }
    records, hashes = {keys[0]: accepted, keys[1]: rows, parent_key: parent}, {
        **inventory, parent_key: parent_sha}

    def check(cur=current, data=records, byte_hashes=hashes, source=folder):
        return identity.gate(
            cur, current_sha, source,
            reader=lambda path: deepcopy(data[linux(binding.local_path(path))]),
            hasher=lambda path: byte_hashes[linux(binding.local_path(path))])

    check()
    negative = []

    def reject(label, mutation):
        cur, data, hs = deepcopy(current), deepcopy(records), dict(hashes)
        mutation(cur, data, hs)
        try:
            check(cur, data, hs)
        except (ValueError, KeyError, TypeError):
            negative.append(label)
        else:
            raise AssertionError("invalid product candidate identity accepted: "+label)

    reject("product-current-semantic-admission-marker-omitted", lambda cur, data, hs:
           data[parent_key].update(product_actual_published_replay_matched_and_semantics_replayed_here=False))
    reject("product-acceptance-relabelled-as-mixed", lambda cur, data, hs:
           data[keys[0]].update(schema=identity.prior.ACCEPTANCE_SCHEMA))
    reject("product-executor-renamed-to-old-owned-checker", lambda cur, data, hs:
           data[keys[0]].update(executed_checker_file="verify_owned_candidate_forests.py"))
    reject("product-own-code-bytes-changed", lambda cur, data, hs: hs.update({keys[2]: "0"*64}))
    reject("product-own-checker-not-bound-in-current", lambda cur, data, hs: cur["files"].pop(keys[2]))
    reject("product-mode-relabelled-as-integrated-Taylor", lambda cur, data, hs:
           data[keys[0]].update(accepted_curvature_modes=["integrated-Taylor"]))
    reject("one-product-actual-control-omitted", lambda cur, data, hs:
           data[keys[0]]["negative_controls_rejected"].pop())
    reject("product-current-root-count-changed", lambda cur, data, hs:
           data[parent_key].update(candidate_angle_unresolved_closed_boxes=14))
    reject("product-partial-ownership-pointers", lambda cur, data, hs:
           data[parent_key].pop("actual_current_candidate_pending_angles"))
    reject("product-bound-parent-bytes-changed", lambda cur, data, hs: hs.update({parent_key: "0"*64}))
    reject("product-bound-parent-missing", lambda cur, data, hs: cur["files"].pop(parent_key))
    reject("product-newest-partial-history-preservation-omitted", lambda cur, data, hs:
           data[parent_key].update(all_newest_owned_histories_retained_identically=False))
    reject("product-full-model-source-gate-omitted", lambda cur, data, hs:
           data[keys[0]].update(original_full_latest_model_source_all_old_payments_and_history_replayed=False))
    reject("product-boolean-whole-root-index", lambda cur, data, hs: data[keys[1]][0].update(index=True))
    reject("product-duplicate-remaining-root-index", lambda cur, data, hs: data[keys[1]][0].update(index=1))
    try:
        check(source=folder.with_name("_synthetic_older_equal_count_source_NOT_real"))
    except (ValueError, KeyError):
        negative.append("product-older-equal-count-source-substituted")
    else:
        raise AssertionError("product identity accepted an older equal-count source")
    snapshot = identity.gate(
        binding.read(args.actual_current), binding.sha(args.actual_current), args.actual_source)
    report = {
        "schema": "N26-product-latest-candidate-identity-regression-v1",
        "synthetic_product_new_schema_identity_passed": True,
        "synthetic_invalid_identity_controls_rejected": negative,
        "actual_prior_schema_delegation_identity_snapshot": snapshot,
        "actual_snapshot_is_identity_only_NOT_geometry_or_final_current_adoption": True,
        "synthetic_15_remaining_roots_NOT_formal_current": True,
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_optimality_proved": False,
        "tested_identity_module_sha256": binding.sha(identity.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"product_identity_regression_completed": True, "synthetic_rejections": len(negative),
                      "actual_prior_schema_identity_only_checked": True,
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
