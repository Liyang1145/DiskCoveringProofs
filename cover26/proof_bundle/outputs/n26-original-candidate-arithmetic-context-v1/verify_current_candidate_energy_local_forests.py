"""Standalone continuation forests on exact folded current candidate roots.

This fresh gate uses the accepted forest's remaining roots, not its historical
curvature source. The immutable original closed-half/energy/LOCAL arithmetic
and root-ownership derivation are reused without changing the original graph.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_forest_source as current_source
import verify_candidate_energy_local_forests as base


read, sha, local_path, bound = base.read, base.sha, base.local_path, base.bound
SCHEMA = "N26-current-candidate-energy-LOCAL-continuation-bindings-v1"
PROPOSAL_SCHEMA = "N26-unaccepted-current-candidate-energy-LOCAL-continuation-forests-v1"


def input_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != SCHEMA or manifest["radius_scope"] != "same-root-Rstar":
        raise ValueError("candidate continuation changed its source schema or same-root scope")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("candidate continuation sealed input changed: " + name)
    for module in (current_source, base, base.forest, base.independent):
        if sha(module.__file__) != manifest["copied_files"][Path(module.__file__).name]:
            raise ValueError("candidate continuation executes a different sealed source or partition gate")
    source_folder = local_path(manifest["source"])
    source_replay = local_path(manifest["source_replay"])
    current_path = local_path(manifest["parent_current_audit"])
    rehash_path = local_path(manifest["parent_digest_recheck"])
    accepted, original_values, pending, inventory, previous_paid = current_source.gate(
        source_folder, source_replay, current_path, rehash_path
    )
    parent = read(current_path)
    if (
        sha(source_folder / "VERIFIED.json") != manifest["source_acceptance_sha256"]
        or read(folder / "SOURCE-ACCEPTANCE.json") != accepted
        or read(folder / "SOURCE-PENDING-ANGLES.json") != pending
        or sha(current_path) != manifest["parent_current_audit_sha256"]
        or read(folder / "SOURCE-CURRENT-AUDIT.json") != parent
        or sha(rehash_path) != manifest["parent_digest_recheck_sha256"]
        or read(folder / "SOURCE-FINAL-DIGEST-RECHECK.json") != read(rehash_path)
        or F(original_values[3]["radius"]) != F(parent["r_strict_interval"][1])
        or len(pending) != parent["candidate_angle_unresolved_closed_boxes"]
    ):
        raise ValueError("candidate continuation substituted its actual folded roots or current ancestry")
    regression = read(folder / "FOLDED-SOURCE-REGRESSION.json")
    if (
        regression["tested_source_loader_sha256"] != sha(current_source.__file__)
        or regression["actual_source_snapshot_sha256"] != sha(source_folder / "VERIFIED.json")
        or len(regression["invalid_folded_accounting_controls_rejected"]) != 9
        or regression["new_geometric_candidate_payments"] != 0
        or regression["source_snapshot_only_not_a_geometric_replay"] is not True
        or regression["executed_test_sha256"] != manifest["copied_files"]["test_current_candidate_forest_source.py"]
    ):
        raise ValueError("candidate continuation folded-source accounting controls changed")
    proposal = read(folder / "PROPOSAL.json")
    if (
        proposal["schema"] != PROPOSAL_SCHEMA
        or proposal["verified"] is not False
        or proposal["radius_scope"] != "same-root-Rstar"
        or proposal["source_acceptance_sha256"] != manifest["source_acceptance_sha256"]
        or proposal["source_pending_angles_sha256"] != sha(source_folder / "PENDING-ANGLES.json")
        or proposal["current_audit_sha256"] != manifest["parent_current_audit_sha256"]
        or proposal["current_digest_recheck_sha256"] != manifest["parent_digest_recheck_sha256"]
        or proposal["source_actual_remaining_candidate_roots"] != len(pending)
        or proposal["already_paid_accepted_forest_root_indices"] != [
            row["source_OPEN_index"] for row in previous_paid
        ]
        or proposal["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
    ):
        raise ValueError("candidate continuation discovery lost actual folded source ownership")
    return manifest, parent, accepted, original_values, pending, proposal, inventory


derive = base.derive


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = input_gate(folder)
    manifest, parent, accepted, original_values, incoming, proposal, inventory = values
    payments, remaining, results, boxes, ledgers = derive(values)
    if not payments:
        raise ValueError("accepted continuation requires at least one fully lower-bounded whole root")
    regression = read(folder / "PARTITION-REGRESSION.json")
    if (
        regression["tested_forest_sha256"] != sha(base.forest.__file__)
        or len(regression["invalid_partition_controls_rejected"]) != 9
        or regression["synthetic_structure_regression_only"] is not True
        or regression["current_candidate_source_roots_removed"] != 0
    ):
        raise ValueError("candidate continuation closed-half controls changed")
    positives = base.source.tiny_control(original_values)
    rejected = []

    def reject(label, changed):
        try:
            derive(values, changed)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid continuation forest accepted: " + label)

    roots = proposal["forests"]
    reject("duplicate-current-root", roots + roots[:1])
    bad = deepcopy(roots[:1])
    bad[0]["actual_source_closed_box"]["sharp_lower"][0] = str(
        F(bad[0]["actual_source_closed_box"]["sharp_lower"][0]) - 1
    )
    reject("changed-current-full-root-box", bad)
    for index in (1123, 1001, 997, 1958):
        bad = deepcopy(roots[:1])
        bad[0]["source_OPEN_index"] = index
        reject("previously-paid-root-overwritten-" + str(index), bad)
    first_split = next((item for item in roots if any(
        node["kind"] == "SPLIT" for node in item["nodes"]
    )), None)
    if first_split is not None:
        bad = deepcopy([first_split])
        split = next(node for node in bad[0]["nodes"] if node["kind"] == "SPLIT")
        split["children"][1] = split["children"][0]
        reject("current-closed-half-shared-boundary-lost", bad)
    bad = deepcopy(roots[:1])
    bad[0]["nodes"].append({"kind": "OPEN"})
    reject("unreachable-current-OPEN-leaf", bad)
    bad = deepcopy(roots[:1])
    bad[0]["nodes"] = [{"kind": "EMPTY"}]
    reject("nonempty-current-root-falsely-emptied", bad)
    first_energy = next((item for item in roots if any(
        node["kind"] == "ENERGY" for node in item["nodes"]
    )), None)
    if first_energy is not None:
        bad = deepcopy([first_energy])
        next(node for node in bad[0]["nodes"] if node["kind"] == "ENERGY")["certificate"]["eta"] = "-1"
        reject("negative-current-energy-curvature-allowance", bad)
    for result in results:
        if result["counts"]["LOCAL"] and result["source_candidate_root_strictly_empty"]:
            raise ValueError("LOCAL equality-feasible continuation region was falsely emptied")
    certificate = {
        "schema": "N26-accepted-current-candidate-energy-LOCAL-continuation-forest-v1",
        "radius_scope": "same-root-Rstar",
        "radius_upper": str(original_values[3]["radius"]),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_pending_angles_sha256": sha(folder / "SOURCE-PENDING-ANGLES.json"),
        "discharged_actual_source_root_indices": [row["source_OPEN_index"] for row in payments],
        "all_unattempted_or_incompletely_proved_source_roots_retained": True,
        "LOCAL_lower_bound_is_not_an_emptiness_claim": True,
    }
    outputs = {
        "CERTIFICATE.json": certificate, "ROOT-PAYMENTS.json": payments,
        "PENDING-ANGLES.json": remaining, "ROOT-CLASSIFICATION.json": results,
        "PENDING-FOREST-LEAVES.json": boxes, "LOWER-LEDGER.json": ledgers,
        "POSITIVE-CONTROLS.json": positives,
    }
    for name, data in outputs.items():
        path = folder / name
        if path.exists():
            if read(path) != data:
                raise ValueError("candidate continuation semantic output changed: " + name)
        else:
            path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    inventory.extend(folder / name for name in manifest["copied_files"])
    hashes = {linux(path): sha(path) for path in inventory}
    report = {
        "schema": "N26-accepted-current-candidate-energy-LOCAL-continuation-forests-v1",
        "verified": True, "radius_scope": "same-root-Rstar",
        "radius_upper": str(original_values[3]["radius"]),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "parent_current_audit_sha256": manifest["parent_current_audit_sha256"],
        "source_actual_remaining_candidate_roots": len(incoming),
        "source_candidate_roots_independently_reconstructed": len(results),
        "new_whole_candidate_source_roots_lower_bounded": len(payments),
        "new_strictly_empty_source_roots": sum(row["source_candidate_root_strictly_empty"] for row in payments),
        "new_source_roots_discharged_with_original_LOCAL": sum(row["counts"]["LOCAL"] > 0 for row in payments),
        "unresolved_closed_angle_boxes": len(remaining),
        "verified_forest_counts": {
            kind: sum(row["counts"][kind] for row in results) for kind in base.forest.KINDS
        },
        "all_complete_candidate_root_forests_and_shared_boundaries_independently_replayed": True,
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
        "global_optimality_proved": False, "n27_started": False,
        "negative_controls_rejected": rejected,
        "files": {name: sha(folder / name) for name in dict.fromkeys(
            ["MANIFEST.json", *manifest["copied_files"], *outputs]
        )},
        "source_files": hashes, "executed_checker_sha256": sha(__file__),
    }
    if report["executed_checker_sha256"] != report["files"][Path(__file__).name]:
        raise ValueError("candidate continuation executed a different sealed checker")
    for text, digest in hashes.items():
        if sha(local_path(text)) != digest:
            raise ValueError("candidate continuation source changed during final binding")
    for text, digest in parent["files"].items():
        if sha(local_path(text)) != digest:
            raise ValueError("candidate continuation current parent changed during acceptance")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: val for key, val in report.items() if key not in ("files", "source_files")}, indent=2),
          flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    acceptance, _ = bound(args.source)
    proposal = read(args.proposal)
    if (
        read(args.source_replay) != acceptance
        or proposal["schema"] != PROPOSAL_SCHEMA
        or proposal["source_acceptance_sha256"] != sha(args.source / "VERIFIED.json")
        or proposal["current_audit_sha256"] != sha(args.parent_current_audit)
        or proposal["current_digest_recheck_sha256"] != sha(args.parent_digest_recheck)
        or not proposal["proposed_complete_lower_bounded_source_roots"]
    ):
        raise ValueError("continuation builder lacks a complete proposal on the actual folded source")
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name) for name in acceptance["files"] if name.endswith(".py")]
    copies.extend([
        (args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
        (args.source / "PENDING-ANGLES.json", "SOURCE-PENDING-ANGLES.json"),
        (args.parent_current_audit, "SOURCE-CURRENT-AUDIT.json"),
        (args.parent_digest_recheck, "SOURCE-FINAL-DIGEST-RECHECK.json"),
        (args.proposal, "PROPOSAL.json"), (args.regression, "PARTITION-REGRESSION.json"),
        (args.source_regression, "FOLDED-SOURCE-REGRESSION.json"),
    ])
    for name in ("verify_current_candidate_energy_local_forests.py",
                 "n26_current_candidate_forest_source.py", "test_current_candidate_forest_source.py",
                 "propose_current_candidate_common_grid_forests.py",
                 "propose_common_grid_candidate_curvature.py",
                 "propose_candidate_curvature_energy.py", "propose_quadratic_energy_minorant.py",
                 "propose_quadratic_secant_refinement.py",
                 "verify_conditional_force_stage.py", "verify_force_stage.py",
                 "verify_force_forest.py", "verify_partial_area_closures.py",
                 "verify_multislope_area.py", "n26_force_angles.py"):
        copies.append((Path(__file__).with_name(name), name))
    copies.append((Path(__file__).with_name("n26-current-candidate-folded-forest-source-proof.md"),
                   "PROOF.md"))
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
                      "independent_folded_source_and_complete_forest_acceptance_pending": True}), flush=True)


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    builder = commands.add_parser("build")
    for name in ("source", "source-replay", "parent-current-audit", "parent-digest-recheck",
                 "proposal", "regression", "source-regression", "output"):
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
