"""Standalone complete ENERGY/LOCAL forests on actual retained candidate roots."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_energy_local_forest as forest
import verify_candidate_curvature_overlay as source
import verify_selected_type_trees as independent


read, sha, local_path, bound = source.read, source.sha, source.local_path, source.bound
SCHEMA = "N26-original-candidate-energy-LOCAL-forest-current-bindings-v1"


def input_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != SCHEMA or manifest["radius_scope"] != "same-root-Rstar":
        raise ValueError("candidate forest changed its explicit same-root scope")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("candidate forest sealed input changed: " + name)
    parent_path = local_path(manifest["parent_current_audit"])
    parent = read(parent_path)
    if (sha(parent_path) != manifest["parent_current_audit_sha256"]
            or read(folder / "SOURCE-CURRENT-AUDIT.json") != parent
            or not parent["current_bound_bytes_rechecked"]
            or parent["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
            or parent["global_optimality_proved"] is not False):
        raise ValueError("candidate forest does not use an actual honest current chain")
    for text, digest in parent["files"].items():
        if sha(local_path(text)) != digest:
            raise ValueError("candidate forest current parent bytes changed: " + text)
    source_folder = local_path(manifest["source"])
    accepted, inventory = bound(source_folder)
    replay_path = local_path(manifest["source_replay"])
    if (read(replay_path) != accepted or read(folder / "SOURCE-ACCEPTANCE.json") != accepted
            or sha(source_folder / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or parent["files"].get(linux(source_folder / "VERIFIED.json")) != sha(source_folder / "VERIFIED.json")
            or parent["files"].get(linux(replay_path)) != sha(replay_path)
            or sha(source.__file__) != accepted["files"]["verify_candidate_curvature_overlay.py"]):
        raise ValueError("candidate forest substituted the actual accepted curvature source")
    print("Reconstructing all source candidate payments and the actual remaining roots.", flush=True)
    source_values = source.input_gate(source_folder)
    old_payments, pending = source.derive(source_values)
    positives = {**source.source.identity_control(source_values[5]), **source.tiny_control(source_values)}
    if (old_payments != read(source_folder / "LOWER-LEDGER.json")
            or pending != read(source_folder / "PENDING-ANGLES.json")
            or pending != read(folder / "SOURCE-PENDING-ANGLES.json")
            or positives != read(source_folder / "POSITIVE-CONTROLS.json")
            or len(pending) != parent["candidate_angle_unresolved_closed_boxes"]
            or len(pending) != accepted["unresolved_closed_angle_boxes"]
            or F(source_values[3]["radius"]) != F(parent["r_strict_interval"][1])
            or parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"):
        raise ValueError("candidate forest actual source roots, local frame or prior payments did not reconstruct")
    for module in (forest, independent):
        if sha(module.__file__) != manifest["copied_files"][Path(module.__file__).name]:
            raise ValueError("candidate forest executed different sealed partition arithmetic")
    proposal = read(folder / "PROPOSAL.json")
    if (proposal["schema"] != "N26-unaccepted-original-candidate-energy-LOCAL-closed-forests-v1"
            or proposal["verified"] is not False or proposal["radius_scope"] != "same-root-Rstar"
            or proposal["source_acceptance_sha256"] != sha(source_folder / "VERIFIED.json")
            or proposal["source_pending_angles_sha256"] != sha(source_folder / "PENDING-ANGLES.json")
            or proposal["original_52_coordinate_local_allowance_unchanged"] != "7/800000"):
        raise ValueError("candidate forest discovery changed its original source or allowance")
    inventory.extend(source_values[-1])
    inventory.extend([parent_path, replay_path])
    return manifest, parent, accepted, source_values, pending, proposal, inventory


def derive(values, roots_override=None):
    _, _, _, source_values, pending, proposal, _ = values
    roots = proposal["forests"] if roots_override is None else roots_override
    if not isinstance(roots, list) or not roots:
        raise ValueError("candidate forest lacks explicit source-root ownership")
    by_index = {row["index"]: row for row in pending}
    if len(by_index) != len(pending):
        raise ValueError("actual candidate pending roots are not distinct")
    seen, discharged, results, boxes, ledgers = set(), set(), [], [], []
    original, kernel, arcs = source_values[3], source_values[5], source_values[6]
    for item in roots:
        index = item["source_OPEN_index"]
        if type(index) is not int or index in seen or index not in by_index:
            raise ValueError("candidate forest duplicated, overwrote or invented a source root")
        seen.add(index)
        row = by_index[index]
        if item["actual_source_closed_box"] != row:
            raise ValueError("candidate forest uses different full source root bounds")
        result, retained, ledger = forest.replay(original, kernel, arcs, row, item["nodes"])
        if result["source_candidate_root_fully_lower_bounded"]:
            discharged.add(index)
        results.append({"source_OPEN_index": index, "actual_source_closed_box": row, **result})
        boxes.append({"source_OPEN_index": index, "retained_closed_leaf_boxes": retained})
        ledgers.append({"source_OPEN_index": index, "verified_closed_leaves": ledger})
    remaining = [row for row in pending if row["index"] not in discharged]
    payments = [row for row in results if row["source_OPEN_index"] in discharged]
    if len(remaining) + len(payments) != len(pending):
        raise ValueError("candidate forest lost an unattempted or incompletely proved whole source root")
    return payments, remaining, results, boxes, ledgers


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = input_gate(folder)
    manifest, parent, accepted, source_values, incoming, proposal, inventory = values
    payments, remaining, results, boxes, ledgers = derive(values)
    if not payments:
        raise ValueError("this accepted candidate extension requires a fully discharged source root")
    regression = read(folder / "PARTITION-REGRESSION.json")
    if (regression["tested_forest_sha256"] != sha(forest.__file__)
            or len(regression["invalid_partition_controls_rejected"]) != 9
            or regression["synthetic_structure_regression_only"] is not True
            or regression["current_candidate_source_roots_removed"] != 0):
        raise ValueError("candidate forest synthetic partition controls changed")
    positives = source.tiny_control(source_values)
    negatives = []

    def reject(label, changed):
        try:
            derive(values, changed)
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid current candidate forest accepted: " + label)

    roots = proposal["forests"]
    reject("duplicate-actual-candidate-root", roots + roots[:1])
    bad = deepcopy(roots[:1])
    bad[0]["actual_source_closed_box"]["sharp_lower"][0] = str(
        F(bad[0]["actual_source_closed_box"]["sharp_lower"][0]) - 1)
    reject("changed-full-candidate-source-root", bad)
    bad = deepcopy(roots[:1])
    bad[0]["source_OPEN_index"] = 1958
    reject("previously-paid-candidate-root-overwritten", bad)
    first_split = next(item for item in roots if any(node["kind"] == "SPLIT" for node in item["nodes"]))
    bad = deepcopy([first_split])
    split = next(node for node in bad[0]["nodes"] if node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("lost-shared-candidate-closed-half", bad)
    bad = deepcopy([first_split])
    bad[0]["nodes"].append({"kind": "OPEN"})
    reject("unreachable-candidate-OPEN-leaf", bad)
    bad = deepcopy(roots[:1])
    bad[0]["nodes"] = [{"kind": "EMPTY"}]
    reject("nonempty-candidate-root-declared-empty", bad)
    first_energy = next(item for item in roots if any(node["kind"] == "ENERGY" for node in item["nodes"]))
    bad = deepcopy([first_energy])
    next(node for node in bad[0]["nodes"] if node["kind"] == "ENERGY")["certificate"]["eta"] = "-1"
    reject("negative-candidate-forest-curvature-allowance", bad)
    first_local = next((item for item in roots if any(node["kind"] == "LOCAL" for node in item["nodes"])), None)
    if first_local is not None:
        bad = deepcopy([first_local])
        next(node for node in bad[0]["nodes"] if node["kind"] == "LOCAL")["supplied_hull"] = []
        reject("candidate-LOCAL-hull-not-reconstructed", bad)
    for result in results:
        if result["counts"]["LOCAL"] and result["source_candidate_root_strictly_empty"]:
            raise ValueError("equality-feasible LOCAL candidate region was falsely called empty")
    certificate = {"schema": "N26-accepted-original-candidate-energy-LOCAL-closed-root-forest-v1",
                   "radius_scope": "same-root-Rstar", "radius_upper": str(source_values[3]["radius"]),
                   "source_acceptance_sha256": manifest["source_acceptance_sha256"],
                   "source_pending_angles_sha256": sha(folder / "SOURCE-PENDING-ANGLES.json"),
                   "discharged_actual_source_root_indices": [row["source_OPEN_index"] for row in payments],
                   "all_unattempted_or_incompletely_proved_source_roots_retained": True,
                   "LOCAL_lower_bound_is_not_an_emptiness_claim": True}
    for name, data in (("CERTIFICATE.json", certificate), ("ROOT-CLASSIFICATION.json", results),
                       ("PENDING-ANGLES.json", remaining), ("ROOT-PAYMENTS.json", payments),
                       ("LOWER-LEDGER.json", ledgers), ("PENDING-FOREST-LEAVES.json", boxes),
                       ("POSITIVE-CONTROLS.json", positives)):
        path = folder / name
        if path.exists():
            if read(path) != data:
                raise ValueError("candidate forest published semantic output changed: " + name)
        else:
            path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    inventory.extend(folder / name for name in manifest["copied_files"])
    hashes = {linux(path): sha(path) for path in inventory}
    counts = {kind: sum(row["counts"][kind] for row in results) for kind in forest.KINDS}
    report = {"schema": "N26-accepted-current-original-candidate-energy-LOCAL-forests-v1",
              "verified": True, "radius_scope": "same-root-Rstar", "radius_upper": str(source_values[3]["radius"]),
              "source_acceptance_sha256": manifest["source_acceptance_sha256"],
              "parent_current_audit_sha256": manifest["parent_current_audit_sha256"],
              "source_actual_remaining_candidate_roots": len(incoming),
              "source_candidate_roots_independently_reconstructed": len(results),
              "new_whole_candidate_source_roots_lower_bounded": len(payments),
              "new_strictly_empty_source_roots": sum(row["source_candidate_root_strictly_empty"] for row in payments),
              "new_source_roots_discharged_with_original_LOCAL": sum(row["counts"]["LOCAL"] > 0 for row in payments),
              "unresolved_closed_angle_boxes": len(remaining),
              "verified_forest_counts": counts,
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
              "negative_controls_rejected": negatives,
              "files": {name: sha(folder / name) for name in
                        ["MANIFEST.json", *manifest["copied_files"], "CERTIFICATE.json", "ROOT-CLASSIFICATION.json",
                         "ROOT-PAYMENTS.json", "PENDING-ANGLES.json", "LOWER-LEDGER.json",
                         "PENDING-FOREST-LEAVES.json", "POSITIVE-CONTROLS.json"]},
              "source_files": hashes, "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_candidate_energy_local_forests.py"]:
        raise ValueError("candidate forest executed a different sealed checker")
    for text, digest in hashes.items():
        if sha(local_path(text)) != digest:
            raise ValueError("candidate forest source changed during final binding")
    for text, digest in parent["files"].items():
        if sha(local_path(text)) != digest:
            raise ValueError("candidate forest parent bytes changed during acceptance")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2),
          flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.source)
    proposal = read(args.proposal)
    if (read(args.source_replay) != accepted
            or proposal["source_acceptance_sha256"] != sha(args.source / "VERIFIED.json")
            or not proposal["proposed_complete_lower_bounded_source_roots"]):
        raise ValueError("candidate forest builder lacks matching actual source and complete proposals")
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend([(args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
                   (args.source / "PENDING-ANGLES.json", "SOURCE-PENDING-ANGLES.json"),
                   (args.parent_current_audit, "SOURCE-CURRENT-AUDIT.json"),
                   (args.proposal, "PROPOSAL.json"), (args.regression, "PARTITION-REGRESSION.json")])
    for name in ("verify_candidate_energy_local_forests.py", "n26_candidate_energy_local_forest.py",
                 "verify_selected_type_trees.py", "n26_sharp_type_tree.py", "n26_terminal_canonical.py",
                 "verify_positive_stress.py", "verify_terminal_catalog.py"):
        copies.append((Path(__file__).with_name(name), name))
    copies.append((Path(__file__).with_name("n26-candidate-energy-LOCAL-forest-proof.md"), "PROOF.md"))
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest = {"schema": SCHEMA, "radius_scope": "same-root-Rstar",
                "source": linux(args.source), "source_replay": linux(args.source_replay),
                "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
                "parent_current_audit": linux(args.parent_current_audit),
                "parent_current_audit_sha256": sha(args.parent_current_audit),
                "copied_files": {name: sha(args.output / name) for _, name in copies}}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False,
                      "candidate_roots_attempted": proposal["source_roots_attempted"],
                      "independent_complete_forest_acceptance_pending": True}), flush=True)


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    builder = commands.add_parser("build")
    for name in ("source", "source-replay", "parent-current-audit", "proposal", "regression", "output"):
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
