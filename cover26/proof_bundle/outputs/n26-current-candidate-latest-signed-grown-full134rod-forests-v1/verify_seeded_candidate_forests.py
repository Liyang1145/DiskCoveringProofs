"""Independent accepted-seed ENERGY/LOCAL forests on actual current roots."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_seed_extension as seed_contract
import n26_current_seeded_candidate_source as source
import verify_candidate_energy_local_forests as base


read, sha, local_path, bound = base.read, base.sha, base.local_path, base.bound
SCHEMA = "N26-current-candidate-seeded-forest-input-bindings-v1"
PROPOSAL_SCHEMA = "N26-unaccepted-current-candidate-seeded-ENERGY-LOCAL-forest-v1"


def input_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != SCHEMA or manifest["radius_scope"] != "same-root-Rstar":
        raise ValueError("seeded candidate forest changed its explicit current-source schema")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("seeded candidate sealed input changed: " + name)
    for module in (source, seed_contract, base, base.forest, base.independent):
        if sha(module.__file__) != manifest["copied_files"][Path(module.__file__).name]:
            raise ValueError("seeded candidate uses different sealed source/partition arithmetic")
    original_source = local_path(manifest["source"])
    replay = local_path(manifest["source_replay"])
    parent_path = local_path(manifest["parent_current_audit"])
    rehash_path = local_path(manifest["parent_digest_recheck"])
    accepted, original_values, pending, inventory, paid = source.gate(
        original_source, replay, parent_path, rehash_path
    )
    parent = read(parent_path)
    if (
        sha(original_source / "VERIFIED.json") != manifest["source_acceptance_sha256"]
        or read(folder / "SOURCE-ACCEPTANCE.json") != accepted
        or read(folder / "SOURCE-PENDING-ANGLES.json") != pending
        or sha(parent_path) != manifest["parent_current_audit_sha256"]
        or read(folder / "SOURCE-CURRENT-AUDIT.json") != parent
        or sha(rehash_path) != manifest["parent_digest_recheck_sha256"]
        or read(folder / "SOURCE-FINAL-DIGEST-RECHECK.json") != read(rehash_path)
        or F(original_values[3]["radius"]) != F(parent["r_strict_interval"][1])
        or len(pending) != parent["candidate_angle_unresolved_closed_boxes"]
        or read(folder / "ACCEPTED-SEED-PROPOSAL.json") != read(original_source / "PROPOSAL.json")
        or read(folder / "ACCEPTED-SEED-CLASSIFICATION.json") != read(original_source / "ROOT-CLASSIFICATION.json")
    ):
        raise ValueError("seeded candidate substituted exact current roots, seed or ancestry")
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
        or proposal["accepted_seed_proposal_sha256"] != sha(original_source / "PROPOSAL.json")
        or proposal["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
        or proposal["old_paid_leaves_and_closed_splits_retained_identically"] is not True
    ):
        raise ValueError("seeded discovery lost its actual source, seed or original local allowance")
    if "already_paid_current_continuation_indices" in proposal and proposal[
        "already_paid_current_continuation_indices"
    ] != [row["source_OPEN_index"] for row in paid]:
        raise ValueError("seeded discovery changed its previous whole-root payment ledger")
    return manifest, parent, accepted, original_values, pending, proposal, inventory


def seed_contract_results(values, roots_override=None):
    manifest, _, _, original_values, pending, proposal, _ = values
    roots = proposal["forests"] if roots_override is None else roots_override
    source_folder = local_path(manifest["source"])
    previous = read(source_folder / "PROPOSAL.json")["forests"]
    classes = read(source_folder / "ROOT-CLASSIFICATION.json")
    by_index = {row["index"]: row for row in pending}
    by_seed = {row["source_OPEN_index"]: row for row in previous}
    by_class = {row["source_OPEN_index"]: row for row in classes}
    if not isinstance(roots, list) or not roots:
        raise ValueError("seeded candidate lacks explicit current roots")
    seen, controls = set(), []
    for extension in roots:
        index = extension["source_OPEN_index"]
        if type(index) is not int or index in seen or index not in by_index or index not in by_seed:
            raise ValueError("seeded candidate root is repeated, previously paid or lacks an actual accepted seed")
        seen.add(index)
        row, seed = by_index[index], by_seed[index]
        retained = seed_contract.gate(row, seed, extension)
        initial, _, _ = base.forest.replay(
            original_values[3], original_values[5], original_values[6], row, seed["nodes"]
        )
        classification = {"source_OPEN_index": index, "actual_source_closed_box": row, **initial}
        if classification != by_class.get(index) or initial["source_candidate_root_fully_lower_bounded"]:
            raise ValueError("seeded candidate did not replay an actual accepted incomplete current root")
        controls.append({**retained, "accepted_seed_exact_result": initial})
    return controls


def derive(values, roots_override=None):
    seed_contract_results(values, roots_override)
    return base.derive(values, roots_override)


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = input_gate(folder)
    manifest, parent, accepted, original_values, incoming, proposal, inventory = values
    payments, remaining, results, boxes, ledgers = derive(values)
    retention = seed_contract_results(values)
    new_strict = sum(row["counts"]["ENERGY"] + row["counts"]["LOCAL"] + row["counts"]["EMPTY"]
                     - item["accepted_seed_exact_result"]["counts"]["ENERGY"]
                     - item["accepted_seed_exact_result"]["counts"]["LOCAL"]
                     - item["accepted_seed_exact_result"]["counts"]["EMPTY"]
                     for row, item in zip(results, retention))
    if new_strict <= 0:
        raise ValueError("seeded acceptance requires new exact lower-bounded/empty leaves, not splits alone")
    regression = read(folder / "SEED-CONTRACT-REGRESSION.json")
    if (
        regression["tested_seed_contract_sha256"] != sha(seed_contract.__file__)
        or len(regression["invalid_seed_extension_controls_rejected"]) != 8
        or regression["new_geometric_candidate_payments"] != 0
        or regression["source_snapshot_and_structure_only_not_a_geometric_replay"] is not True
        or regression["executed_test_sha256"] != manifest["copied_files"]["test_candidate_seed_extension.py"]
        or regression["actual_seed_proposal_sha256"] != sha(folder / "ACCEPTED-SEED-PROPOSAL.json")
        or regression["actual_source_acceptance_sha256"] != sha(folder / "SOURCE-ACCEPTANCE.json")
    ):
        raise ValueError("seeded candidate preservation regression changed")
    partition = read(folder / "PARTITION-REGRESSION.json")
    if (
        partition["tested_forest_sha256"] != sha(base.forest.__file__)
        or len(partition["invalid_partition_controls_rejected"]) != 9
        or partition["synthetic_structure_regression_only"] is not True
        or partition["current_candidate_source_roots_removed"] != 0
    ):
        raise ValueError("seeded candidate closed-half partition regression changed")
    negatives = []

    def reject(label, changed):
        try:
            derive(values, changed)
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid seeded candidate forest accepted: " + label)

    roots = proposal["forests"]
    reject("duplicate-actual-seeded-current-root", roots + roots[:1])
    bad = deepcopy(roots[:1])
    bad[0]["actual_source_closed_box"]["sharp_lower"][0] = str(
        F(bad[0]["actual_source_closed_box"]["sharp_lower"][0]) - 1
    )
    reject("changed-seeded-full-source-root", bad)
    bad = deepcopy(roots[:1])
    bad[0]["source_OPEN_index"] = 1151
    reject("previously-paid-seven-root-owner-overwritten", bad)
    bad = deepcopy(roots[:1])
    next(node for node in bad[0]["nodes"] if node["kind"] == "ENERGY")["certificate"]["eta"] = "-1"
    reject("accepted-seed-energy-certificate-changed", bad)
    bad = deepcopy(roots[:1])
    next(node for node in bad[0]["nodes"] if node["kind"] == "SPLIT")["children"].reverse()
    reject("accepted-seed-closed-sibling-ownership-changed", bad)
    bad = deepcopy(roots[:1])
    bad[0]["nodes"].append({"kind": "OPEN"})
    reject("unreachable-seeded-OPEN-leaf", bad)
    first_index = roots[0]["source_OPEN_index"]
    seed = next(item for item in read(folder / "ACCEPTED-SEED-PROPOSAL.json")["forests"]
                if item["source_OPEN_index"] == first_index)
    modified_open = next((i for i, node in enumerate(seed["nodes"])
                          if node["kind"] == "OPEN" and roots[0]["nodes"][i]["kind"] != "OPEN"), None)
    if modified_open is not None:
        bad = deepcopy(roots[:1])
        bad[0]["nodes"][modified_open] = {"kind": "EMPTY"}
        reject("nonempty-accepted-OPEN-region-falsely-emptied", bad)
    fresh_energy = next((i for i, node in enumerate(roots[0]["nodes"])
                         if node["kind"] == "ENERGY"
                         and (i >= len(seed["nodes"]) or seed["nodes"][i]["kind"] == "OPEN")), None)
    if fresh_energy is not None:
        bad = deepcopy(roots[:1])
        bad[0]["nodes"][fresh_energy]["certificate"]["eta"] = "-1"
        reject("new-seeded-energy-negative-curvature-allowance", bad)
    fresh_split = next((i for i, node in enumerate(roots[0]["nodes"])
                        if node["kind"] == "SPLIT"
                        and (i >= len(seed["nodes"]) or seed["nodes"][i]["kind"] == "OPEN")), None)
    if fresh_split is not None:
        bad = deepcopy(roots[:1])
        bad[0]["nodes"][fresh_split]["children"][1] = bad[0]["nodes"][fresh_split]["children"][0]
        reject("new-seeded-closed-half-shared-boundary-lost", bad)
    positives = base.source.tiny_control(original_values)
    certificate = {
        "schema": "N26-accepted-current-candidate-seeded-energy-LOCAL-forest-v1",
        "radius_scope": "same-root-Rstar", "radius_upper": str(original_values[3]["radius"]),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_pending_angles_sha256": sha(folder / "SOURCE-PENDING-ANGLES.json"),
        "discharged_actual_source_root_indices": [row["source_OPEN_index"] for row in payments],
        "all_unattempted_or_incompletely_proved_source_roots_retained": True,
        "LOCAL_lower_bound_is_not_an_emptiness_claim": True,
        "all_accepted_seed_paid_leaves_and_closed_splits_retained_identically": True,
    }
    outputs = {
        "CERTIFICATE.json": certificate, "ROOT-PAYMENTS.json": payments, "PENDING-ANGLES.json": remaining,
        "ROOT-CLASSIFICATION.json": results, "PENDING-FOREST-LEAVES.json": boxes,
        "LOWER-LEDGER.json": ledgers, "POSITIVE-CONTROLS.json": positives, "SEED-RETENTION.json": retention,
    }
    for name, data in outputs.items():
        path = folder / name
        if path.exists():
            if read(path) != data:
                raise ValueError("seeded candidate published semantic output changed: " + name)
        else:
            path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    inventory.extend(folder / name for name in manifest["copied_files"])
    hashes = {linux(path): sha(path) for path in inventory}
    report = {
        "schema": source.SEEDED_SCHEMA, "verified": True, "radius_scope": "same-root-Rstar",
        "radius_upper": str(original_values[3]["radius"]),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "parent_current_audit_sha256": manifest["parent_current_audit_sha256"],
        "source_actual_remaining_candidate_roots": len(incoming),
        "source_candidate_roots_independently_reconstructed": len(results),
        "new_whole_candidate_source_roots_lower_bounded": len(payments),
        "new_strictly_empty_source_roots": sum(row["source_candidate_root_strictly_empty"] for row in payments),
        "new_source_roots_discharged_with_original_LOCAL": sum(row["counts"]["LOCAL"] > 0 for row in payments),
        "new_exact_closed_leaf_payments": new_strict,
        "unresolved_closed_angle_boxes": len(remaining),
        "verified_forest_counts": {kind: sum(row["counts"][kind] for row in results) for kind in base.forest.KINDS},
        "all_complete_candidate_root_forests_and_shared_boundaries_independently_replayed": True,
        "all_accepted_seed_non_OPEN_nodes_retained_identically": True,
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
        raise ValueError("seeded candidate executed a different sealed verifier")
    for text, digest in hashes.items():
        if sha(text) != digest:
            raise ValueError("seeded candidate source changed during final binding")
    for text, digest in parent["files"].items():
        if sha(text) != digest:
            raise ValueError("seeded candidate proof parent changed during acceptance")
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
        raise ValueError("seeded candidate builder lacks its actual current source and proof-time parent")
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend([
        (args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
        (args.source / "PENDING-ANGLES.json", "SOURCE-PENDING-ANGLES.json"),
        (args.source / "PROPOSAL.json", "ACCEPTED-SEED-PROPOSAL.json"),
        (args.source / "ROOT-CLASSIFICATION.json", "ACCEPTED-SEED-CLASSIFICATION.json"),
        (args.parent_current_audit, "SOURCE-CURRENT-AUDIT.json"),
        (args.parent_digest_recheck, "SOURCE-FINAL-DIGEST-RECHECK.json"),
        (args.proposal, "PROPOSAL.json"), (args.regression, "PARTITION-REGRESSION.json"),
        (args.seed_regression, "SEED-CONTRACT-REGRESSION.json"),
    ])
    for name in ("verify_seeded_candidate_forests.py", "n26_current_seeded_candidate_source.py",
                 "n26_current_candidate_continuation_source.py", "n26_candidate_seed_extension.py",
                 "test_candidate_seed_extension.py", "propose_seeded_current_candidate_forest.py"):
        copies.append((Path(__file__).with_name(name), name))
    copies.append((Path(__file__).with_name("n26-seeded-candidate-forest-proof.md"), "PROOF.md"))
    for original, name in copies:
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
                      "exact_seed_preservation_and_closed_forest_acceptance_pending": True}), flush=True)


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    builder = commands.add_parser("build")
    for name in ("source", "source-replay", "parent-current-audit", "parent-digest-recheck",
                 "proposal", "regression", "seed-regression", "output"):
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
