"""Actual-current fresh/continued candidate forests with per-root history."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_seed_extension as contract
import n26_current_owned_candidate_source as source
import verify_candidate_energy_local_forests as base


read, sha, local_path, bound = base.read, base.sha, base.local_path, base.bound
SCHEMA = "N26-current-owned-candidate-forest-input-bindings-v1"
PROPOSAL_SCHEMA = "N26-unaccepted-current-owned-candidate-energy-LOCAL-forests-v1"


def input_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != SCHEMA or manifest["radius_scope"] != "same-root-Rstar":
        raise ValueError("owned candidate forest changed its current-source schema or scope")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("owned candidate sealed input changed: " + name)
    for module in (source, contract, base, base.forest, base.independent):
        if sha(module.__file__) != manifest["copied_files"][Path(module.__file__).name]:
            raise ValueError("owned candidate executes different sealed source/partition arithmetic")
    original_source = local_path(manifest["source"])
    replay, parent_path, rehash_path = (local_path(manifest[key]) for key in
                                       ("source_replay", "parent_current_audit", "parent_digest_recheck"))
    accepted, original_values, pending, inventory, _ = source.gate(
        original_source, replay, parent_path, rehash_path
    )
    history, paths = source.history(original_source, pending)
    inventory.extend(paths)
    parent = read(parent_path)
    if (
        sha(original_source / "VERIFIED.json") != manifest["source_acceptance_sha256"]
        or read(folder / "SOURCE-ACCEPTANCE.json") != accepted
        or read(folder / "SOURCE-PENDING-ANGLES.json") != pending
        or read(folder / "SOURCE-ROOT-HISTORY.json") != [history[key] for key in sorted(history)]
        or sha(parent_path) != manifest["parent_current_audit_sha256"]
        or read(folder / "SOURCE-CURRENT-AUDIT.json") != parent
        or sha(rehash_path) != manifest["parent_digest_recheck_sha256"]
        or read(folder / "SOURCE-FINAL-DIGEST-RECHECK.json") != read(rehash_path)
        or len(pending) != parent["candidate_angle_unresolved_closed_boxes"]
        or F(original_values[3]["radius"]) != F(parent["r_strict_interval"][1])
    ):
        raise ValueError("owned forest changed actual current roots, per-root history, radius or parent")
    proposal = read(folder / "PROPOSAL.json")
    if (
        proposal["schema"] != PROPOSAL_SCHEMA
        or proposal["verified"] is not False
        or proposal["radius_scope"] != "same-root-Rstar"
        or proposal["source_acceptance_sha256"] != manifest["source_acceptance_sha256"]
        or proposal["source_pending_angles_sha256"] != sha(original_source / "PENDING-ANGLES.json")
        or proposal["current_audit_sha256"] != manifest["parent_current_audit_sha256"]
        or proposal["current_digest_recheck_sha256"] != manifest["parent_digest_recheck_sha256"]
        or proposal["source_actual_remaining_candidate_roots"] != len(pending)
        or proposal["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or proposal["all_newest_accepted_per_root_forests_and_unattempted_whole_roots_preserved"] is not True
    ):
        raise ValueError("owned discovery changed its exact current source or original coordinate allowance")
    return manifest, parent, accepted, original_values, pending, proposal, history, inventory


def ownership(values, roots_override=None):
    _, _, _, original_values, pending, proposal, history, _ = values
    roots = proposal["forests"] if roots_override is None else roots_override
    by_index = {row["index"]: row for row in pending}
    if not isinstance(roots, list) or not roots or len(by_index) != len(pending):
        raise ValueError("owned forest has no distinct actual current root ownership")
    seen, result = set(), []
    for item in roots:
        index = item["source_OPEN_index"]
        if type(index) is not int or index in seen or index not in by_index:
            raise ValueError("owned forest repeated, invented or reopened a previously paid whole root")
        seen.add(index)
        row, seed = by_index[index], history.get(index)
        if item["actual_source_closed_box"] != row:
            raise ValueError("owned forest changed the entire actual current closed root")
        expected_mode = "SEEDED" if seed is not None else "FRESH"
        expected_origin = seed["history_source"] if seed is not None else None
        if item["history_mode"] != expected_mode or item["accepted_history_source"] != expected_origin:
            raise ValueError("owned forest reset an older accepted seed or invented a historical payment")
        if seed is None:
            virtual = {"source_OPEN_index": index, "actual_source_closed_box": row,
                       "nodes": [{"kind": "OPEN"}]}
            kept = contract.gate(row, virtual, item)
            baseline = dict.fromkeys(base.forest.KINDS, 0)
            baseline["OPEN"] = 1
        else:
            kept = contract.gate(row, seed, item)
            initial, _, _ = base.forest.replay(
                original_values[3], original_values[5], original_values[6], row, seed["nodes"]
            )
            if (
                {"source_OPEN_index": index, "actual_source_closed_box": row, **initial}
                != seed["accepted_source_classification"]
                or initial["source_candidate_root_fully_lower_bounded"]
            ):
                raise ValueError("newest per-root seed did not replay its actual incomplete classification")
            baseline = initial["counts"]
        result.append({
            **kept, "history_mode": expected_mode, "accepted_history_source": expected_origin,
            "baseline_counts": baseline,
            "FRESH_OPEN_structure_is_not_a_geometric_payment": seed is None,
            "all_newest_accepted_per_root_non_OPEN_nodes_retained_identically": True,
        })
    return result


def derive(values, roots_override=None):
    ownership(values, roots_override)
    # Original exact root/forest derivation expects its seven-field source tuple.
    original_tuple = (*values[:6], values[-1])
    return base.derive(original_tuple, roots_override)


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = input_gate(folder)
    manifest, parent, accepted, original_values, incoming, proposal, _, inventory = values
    payments, remaining, results, boxes, ledgers = derive(values)
    owners = ownership(values)
    new_closed = sum(
        sum(row["counts"][kind] - owner["baseline_counts"][kind] for kind in ("ENERGY", "LOCAL", "EMPTY"))
        for row, owner in zip(results, owners)
    )
    if new_closed <= 0:
        raise ValueError("owned acceptance requires new exact closed leaves, not splits or unchanged receipts")
    history_test = read(folder / "HISTORY-REGRESSION.json")
    partition = read(folder / "PARTITION-REGRESSION.json")
    if (
        history_test["tested_source_sha256"] != sha(source.__file__)
        or len(history_test["invalid_history_controls_rejected"]) != 8
        or history_test["synthetic_history_only_not_an_actual_geometric_source_replay"] is not True
        or history_test["new_geometric_candidate_payments"] != 0
        or history_test["executed_test_sha256"] != manifest["copied_files"]["test_owned_candidate_history.py"]
        or partition["tested_forest_sha256"] != sha(base.forest.__file__)
        or len(partition["invalid_partition_controls_rejected"]) != 9
        or partition["synthetic_structure_regression_only"] is not True
        or partition["current_candidate_source_roots_removed"] != 0
    ):
        raise ValueError("owned history or exact closed-partition regression changed")
    negatives = []

    def reject(label, changed):
        try:
            derive(values, changed)
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid actual-current owned forest accepted: " + label)

    roots = proposal["forests"]
    reject("duplicate-actual-current-owned-root", roots + roots[:1])
    bad = deepcopy(roots[:1])
    bad[0]["actual_source_closed_box"]["sharp_lower"][0] = str(
        F(bad[0]["actual_source_closed_box"]["sharp_lower"][0]) - 1
    )
    reject("changed-owned-full-current-box", bad)
    bad = deepcopy(roots[:1])
    bad[0]["source_OPEN_index"] = 1958
    reject("previously-paid-original-root-reopened", bad)
    bad = deepcopy(roots[:1])
    bad[0]["source_OPEN_index"] = True
    reject("boolean-instead-of-current-root-owner", bad)
    bad = deepcopy(roots[:1])
    bad[0]["history_mode"] = "SEEDED" if bad[0]["history_mode"] == "FRESH" else "FRESH"
    reject("actual-per-root-history-mode-changed", bad)
    bad = deepcopy(roots[:1])
    bad[0]["nodes"].append({"kind": "OPEN"})
    reject("hidden-unreachable-owned-OPEN-leaf", bad)
    bad = deepcopy(roots[:1])
    bad[0]["nodes"] = [{"kind": "EMPTY"}]
    reject("nonempty-current-owned-root-falsely-emptied", bad)
    first_energy = next((item for item in roots if any(node["kind"] == "ENERGY" for node in item["nodes"])), None)
    if first_energy is not None:
        bad = deepcopy([first_energy])
        next(node for node in bad[0]["nodes"] if node["kind"] == "ENERGY")["certificate"]["eta"] = "-1"
        reject("owned-energy-negative-curvature-allowance", bad)
    first_split = next((item for item in roots if any(node["kind"] == "SPLIT" for node in item["nodes"])), None)
    if first_split is not None:
        bad = deepcopy([first_split])
        split = next(node for node in bad[0]["nodes"] if node["kind"] == "SPLIT")
        split["children"][1] = split["children"][0]
        reject("owned-closed-half-shared-boundary-lost", bad)
    first_local = next((item for item in roots if any(node["kind"] == "LOCAL" for node in item["nodes"])), None)
    if first_local is not None:
        bad = deepcopy([first_local])
        next(node for node in bad[0]["nodes"] if node["kind"] == "LOCAL")["supplied_hull"] = []
        reject("owned-LOCAL-hull-not-reconstructed", bad)
    publish(folder, report_path, values, payments, remaining, results, boxes, ledgers, owners, new_closed, negatives)


def publish(folder, report_path, values, payments, remaining, results, boxes, ledgers, owners, new_closed, negatives):
    manifest, parent, _, original_values, incoming, _, _, inventory = values
    if any(row["source_candidate_root_strictly_empty"] and row["counts"]["LOCAL"] for row in payments):
        raise ValueError("owned LOCAL equality-feasible region was falsely declared empty")
    positives = base.source.tiny_control(original_values)
    certificate = {
        "schema": "N26-accepted-current-owned-candidate-energy-LOCAL-forest-v1",
        "radius_scope": "same-root-Rstar", "radius_upper": str(original_values[3]["radius"]),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_pending_angles_sha256": sha(folder / "SOURCE-PENDING-ANGLES.json"),
        "discharged_actual_source_root_indices": [row["source_OPEN_index"] for row in payments],
        "all_unattempted_or_incompletely_proved_source_roots_retained": True,
        "LOCAL_lower_bound_is_not_an_emptiness_claim": True,
        "all_newest_per_root_accepted_non_OPEN_nodes_retained_identically": True,
    }
    outputs = {
        "CERTIFICATE.json": certificate, "ROOT-PAYMENTS.json": payments, "PENDING-ANGLES.json": remaining,
        "ROOT-CLASSIFICATION.json": results, "PENDING-FOREST-LEAVES.json": boxes,
        "LOWER-LEDGER.json": ledgers, "POSITIVE-CONTROLS.json": positives, "OWNERSHIP.json": owners,
    }
    for name, data in outputs.items():
        path = folder / name
        if path.exists():
            if read(path) != data:
                raise ValueError("owned candidate published semantic output changed: " + name)
        else:
            path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    inventory.extend(folder / name for name in manifest["copied_files"])
    hashes = {linux(path): sha(path) for path in inventory}
    report = {
        "schema": source.SCHEMA, "verified": True, "radius_scope": "same-root-Rstar",
        "radius_upper": str(original_values[3]["radius"]),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "parent_current_audit_sha256": manifest["parent_current_audit_sha256"],
        "source_actual_remaining_candidate_roots": len(incoming),
        "source_candidate_roots_independently_reconstructed": len(results),
        "new_whole_candidate_source_roots_lower_bounded": len(payments),
        "new_strictly_empty_source_roots": sum(row["source_candidate_root_strictly_empty"] for row in payments),
        "new_source_roots_discharged_with_original_LOCAL": sum(row["counts"]["LOCAL"] > 0 for row in payments),
        "new_exact_closed_leaf_payments": new_closed,
        "unresolved_closed_angle_boxes": len(remaining),
        "verified_forest_counts": {kind: sum(row["counts"][kind] for row in results) for kind in base.forest.KINDS},
        "all_complete_candidate_root_forests_and_shared_boundaries_independently_replayed": True,
        "all_newest_per_root_accepted_non_OPEN_nodes_retained_identically": True,
        "all_unattempted_and_incompletely_paid_whole_source_roots_retained_identically": True,
        "all_prior_Dirichlet_curvature_local_force_and_closed_split_payments_preserved": True,
        "original_92_rod_kernel_and_52_coordinate_frame_preserved": True,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": True,
        "LOCAL_equality_feasible_regions_never_declared_empty": True,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "candidate_transport_global_lower_bound_proved": not remaining,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False, "negative_controls_rejected": negatives,
        "files": {name: sha(folder / name) for name in dict.fromkeys(
            ["MANIFEST.json", *manifest["copied_files"], *outputs]
        )},
        "source_files": hashes, "executed_checker_sha256": sha(__file__),
    }
    if report["executed_checker_sha256"] != report["files"][Path(__file__).name]:
        raise ValueError("owned candidate executed a different sealed checker")
    for text, digest in hashes.items():
        if sha(text) != digest:
            raise ValueError("owned candidate source changed during final binding")
    for text, digest in parent["files"].items():
        if sha(text) != digest:
            raise ValueError("owned candidate parent changed during final binding")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: val for key, val in report.items() if key not in ("files", "source_files")}, indent=2),
          flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.source)
    proposal = read(args.proposal)
    if (
        read(args.source_replay) != accepted
        or proposal["schema"] != PROPOSAL_SCHEMA
        or proposal["source_acceptance_sha256"] != sha(args.source / "VERIFIED.json")
        or proposal["current_audit_sha256"] != sha(args.parent_current_audit)
        or proposal["current_digest_recheck_sha256"] != sha(args.parent_digest_recheck)
    ):
        raise ValueError("owned builder lacks the actual current source and proof-time parent")
    pending = read(args.source / "PENDING-ANGLES.json")
    history, _ = source.history(args.source, pending)
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend([
        (args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
        (args.source / "PENDING-ANGLES.json", "SOURCE-PENDING-ANGLES.json"),
        (args.parent_current_audit, "SOURCE-CURRENT-AUDIT.json"),
        (args.parent_digest_recheck, "SOURCE-FINAL-DIGEST-RECHECK.json"),
        (args.proposal, "PROPOSAL.json"), (args.regression, "PARTITION-REGRESSION.json"),
        (args.history_regression, "HISTORY-REGRESSION.json"),
    ])
    history_path = args.output / "SOURCE-ROOT-HISTORY.json"
    history_path.write_text(json.dumps([history[key] for key in sorted(history)], indent=2) + "\n", encoding="utf-8")
    copies.append((history_path, history_path.name))
    for name in ("verify_owned_candidate_forests.py", "n26_current_owned_candidate_source.py",
                 "propose_owned_candidate_forests.py", "test_owned_candidate_history.py",
                 "n26_candidate_seed_extension.py"):
        copies.append((Path(__file__).with_name(name), name))
    copies.append((Path(__file__).with_name("n26-owned-candidate-forest-proof.md"), "PROOF.md"))
    for original, name in copies:
        if original.resolve() != (args.output / name).resolve():
            (args.output / name).write_bytes(original.read_bytes())
    manifest = {
        "schema": SCHEMA, "radius_scope": "same-root-Rstar",
        "source": linux(args.source), "source_replay": linux(args.source_replay),
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "parent_current_audit": linux(args.parent_current_audit),
        "parent_current_audit_sha256": sha(args.parent_current_audit),
        "parent_digest_recheck": linux(args.parent_digest_recheck),
        "parent_digest_recheck_sha256": sha(args.parent_digest_recheck),
        "copied_files": {name: sha(args.output / name) for _, name in copies},
    }
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False,
                      "actual_per_root_history_and_all_closed_leaf_acceptance_pending": True}), flush=True)


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    builder = commands.add_parser("build")
    for name in ("source", "source-replay", "parent-current-audit", "parent-digest-recheck",
                 "proposal", "regression", "history-regression", "output"):
        builder.add_argument("--" + name, type=Path, required=True)
    verifier = commands.add_parser("verify")
    verifier.add_argument("--input", type=Path, required=True)
    verifier.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "build":
        build(args)
    else:
        verify(args.input, args.report)


if __name__ == "__main__":
    main()
