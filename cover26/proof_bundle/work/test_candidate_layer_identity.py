"""Synthetic stale-layer controls and an actual bound ancestry snapshot.

No ENERGY/LOCAL geometry is proved by this ownership regression.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import verify_conditional_force_stage as binding


def fixture():
    root = Path(__file__).resolve().parent / "candidate-layer-identity-synthetic"
    latest, old = root / "latest", root / "old"
    ancestor_path = linux(root / "ancestor.json")
    hashes = {
        linux(latest / "VERIFIED.json"): "c" * 64,
        linux(latest / "PENDING-ANGLES.json"): "d" * 64,
        linux(old / "VERIFIED.json"): "e" * 64,
        linux(old / "PENDING-ANGLES.json"): "d" * 64,
        ancestor_path: "b" * 64,
    }
    common = {
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "radius_scope": binding.SCOPE, "global_optimality_proved": False,
        "candidate_angle_unresolved_closed_boxes": 2,
        "r_strict_interval": ["0.20", "0.21"],
    }
    ancestor = {
        **common,
        "schema": "N26-complete-current-chain-with-per-root-owned-candidate-forests-audit-v1",
        "actual_current_candidate_acceptance": linux(latest / "VERIFIED.json"),
        "actual_current_candidate_pending_angles": linux(latest / "PENDING-ANGLES.json"),
        "files": {text: value for text, value in hashes.items() if text != ancestor_path},
    }
    current = {
        **common, "schema": identity.ENUMERATION_SCHEMA,
        "prior_current_audit_sha256": "b" * 64, "files": dict(hashes),
    }
    accepted = {
        "verified": True, "radius_scope": "same-root-Rstar",
        "radius_upper": "21/100", "unresolved_closed_angle_boxes": 2,
    }
    rows = [{"index": 1}, {"index": 2}]
    reports = {
        ancestor_path: ancestor,
        linux(latest / "VERIFIED.json"): accepted,
        linux(old / "VERIFIED.json"): deepcopy(accepted),
        linux(latest / "PENDING-ANGLES.json"): rows,
        linux(old / "PENDING-ANGLES.json"): deepcopy(rows),
    }
    return current, hashes, reports, latest, old, ancestor_path


def run(case, source=None):
    current, hashes, reports, latest, _, _ = case
    return identity.gate(
        current, "a" * 64, latest if source is None else source,
        reader=lambda path: deepcopy(reports[linux(path)]),
        hasher=lambda path: hashes[linux(path)],
    )


def main():
    parser = argparse.ArgumentParser()
    for name in ("current-audit", "expected-source", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    control = run(fixture())
    if len(control["enumeration_only_bound_ancestors_followed"]) != 1:
        raise AssertionError("enumeration-only current parent did not resolve its latest candidate layer")
    rejected = []

    def reject(label, mutate, use_old_source=False):
        case = fixture()
        mutate(case)
        try:
            run(case, case[4] if use_old_source else None)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid latest candidate layer was accepted: " + label)

    reject("stale-candidate-layer-with-identical-count-and-full-root-rows", lambda case: None, True)
    reject("missing-bound-ancestor", lambda case: case[0]["files"].pop(case[5]))
    reject("changed-bound-ancestor-bytes", lambda case: case[1].update({case[5]: "f" * 64}))
    reject("cyclic-current-ancestry", lambda case: case[0].update({"prior_current_audit_sha256": "a" * 64}))
    reject("half-of-candidate-ownership-pointers-missing", lambda case: case[2][case[5]].pop(
        "actual_current_candidate_pending_angles"))
    reject("ancestor-inventory-not-retained-identically", lambda case: case[2][case[5]]["files"].update({
        linux(case[3] / "VERIFIED.json"): "f" * 64}))
    reject("ancestor-candidate-count-changed", lambda case: case[2][case[5]].update({
        "candidate_angle_unresolved_closed_boxes": 3}))
    reject("unsupported-pointerless-schema", lambda case: case[0].update({"schema": "unknown-current-schema"}))
    reject("latest-pending-rows-changed", lambda case: case[2][linux(case[3] / "PENDING-ANGLES.json")].pop())
    reject("latest-source-acceptance-bytes-changed", lambda case: case[1].update({
        linux(case[3] / "VERIFIED.json"): "f" * 64}))

    initial_sha = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    actual = identity.gate(current, initial_sha, args.expected_source)
    if binding.sha(args.current_audit) != initial_sha:
        raise ValueError("actual current snapshot changed during ownership regression")
    report = {
        "schema": "N26-latest-candidate-layer-identity-regression-v1",
        "synthetic_equal_count_and_equal_full_root_rows_stale_source_rejected": True,
        "synthetic_invalid_layer_identity_controls_rejected": rejected,
        "actual_bound_ancestry_snapshot": actual,
        "actual_snapshot_identity_only_not_a_geometric_replay": True,
        "new_geometric_candidate_payments": 0,
        "tested_identity_checker_sha256": binding.sha(identity.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
