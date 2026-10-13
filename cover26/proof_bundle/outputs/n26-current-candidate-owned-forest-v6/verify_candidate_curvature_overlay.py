"""Standalone original-candidate curvature energy on actual retained OPEN boxes."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_curvature_energy as energy
import n26_quadratic_energy_minorant as quadratic
from n26_sharp_radius_constraints import tighten
import verify_dirichlet_candidate_overlay as source


read, sha, local_path, bound = source.read, source.sha, source.leaf.local_path, source.leaf.bound
SCHEMA = "N26-original-candidate-curvature-energy-current-bindings-v1"


def input_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != SCHEMA or manifest["radius_scope"] != "same-root-Rstar":
        raise ValueError("candidate curvature overlay changed its radius scope")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("candidate curvature sealed file changed: " + name)
    parent_path = local_path(manifest["parent_current_audit"])
    parent = read(parent_path)
    if (sha(parent_path) != manifest["parent_current_audit_sha256"]
            or parent != read(folder / "SOURCE-CURRENT-AUDIT.json")
            or not parent["current_bound_bytes_rechecked"]
            or parent["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
            or parent["global_optimality_proved"] is not False
            or parent["candidate_angle_unresolved_closed_boxes"] != manifest["source_remaining_boxes"]):
        raise ValueError("candidate curvature overlay is not attached to the actual current angle chain")
    for text, digest in parent["files"].items():
        if sha(local_path(text)) != digest:
            raise ValueError("candidate current parent bytes changed: " + text)
    source_folder = local_path(manifest["source"])
    accepted, inventory = bound(source_folder)
    replay_path = local_path(manifest["source_replay"])
    if (read(replay_path) != accepted or read(folder / "SOURCE-ACCEPTANCE.json") != accepted
            or parent["files"].get(linux(source_folder / "VERIFIED.json")) != sha(source_folder / "VERIFIED.json")
            or parent["files"].get(linux(replay_path)) != sha(replay_path)
            or sha(source.__file__) != accepted["files"]["verify_dirichlet_candidate_overlay.py"]
            or sha(source_folder / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or accepted["unresolved_closed_angle_boxes"] != manifest["source_remaining_boxes"]):
        raise ValueError("candidate curvature substituted the actual accepted Dirichlet source")
    values = source.source_gate(source_folder)
    _, _, original, _, pending, _, discovery, old_kernel, arcs, paths = values
    old_payments, remaining = source.derive(pending, discovery["proposed_paid_OPEN_indices"],
                                           old_kernel, original["radius"], arcs)
    if (old_payments != read(source_folder / "LOWER-LEDGER.json")
            or remaining != read(source_folder / "PENDING-ANGLES.json")
            or remaining != read(folder / "SOURCE-PENDING-ANGLES.json")
            or original["reference"] != read(folder / "ORIGINAL-REFERENCE.json")
            or len(remaining) != parent["candidate_angle_unresolved_closed_boxes"]
            or F(original["radius"]) != F(parent["r_strict_interval"][1])
            or accepted["original_52_coordinate_local_allowance_unchanged"] != "7/800000"):
        raise ValueError("candidate actual remaining boxes, prior payments, graph frame or root did not reconstruct")
    if sha(folder / "ORIGINAL-KERNEL.json") != accepted["files"]["DIRICHLET-KERNEL.json"]:
        raise ValueError("candidate curvature changed the original exact kernel")
    kernel = energy.kernel_gate(original["reference"], read(folder / "ORIGINAL-KERNEL.json"))
    for module in (energy, quadratic):
        if sha(module.__file__) != manifest["copied_files"][Path(module.__file__).name]:
            raise ValueError("candidate curvature executed different sealed arithmetic")
    proposal = read(folder / "PROPOSAL.json")
    if (proposal["schema"] != "N26-unaccepted-original-candidate-curvature-energy-overlay-v1"
            or proposal["verified"] is not False or proposal["radius_scope"] != "same-root-Rstar"
            or proposal["source_acceptance_sha256"] != sha(source_folder / "VERIFIED.json")
            or proposal["source_pending_angles_sha256"] != sha(source_folder / "PENDING-ANGLES.json")
            or proposal["original_Dirichlet_kernel_sha256"] != sha(folder / "ORIGINAL-KERNEL.json")):
        raise ValueError("candidate curvature discovery substituted its actual source")
    inventory.extend(paths)
    inventory.extend([parent_path, replay_path])
    return manifest, parent, accepted, original, remaining, kernel, arcs, proposal, inventory


def derive(values, selected=None, proposal_override=None):
    manifest, _, _, original, pending, kernel, arcs, proposal, _ = values
    selected = manifest["selected_source_OPEN_indices"] if selected is None else selected
    proposal = proposal if proposal_override is None else proposal_override
    if (not isinstance(selected, list) or not selected or len(set(selected)) != len(selected)
            or any(type(index) is not int for index in selected)):
        raise ValueError("candidate curvature paid ownership is invalid or duplicated")
    by_index = {row["index"]: row for row in pending}
    if len(by_index) != len(pending) or not set(selected) <= set(by_index):
        raise ValueError("candidate curvature payment is not an actual current retained box")
    records = {row["source_OPEN_index"]: row for row in proposal["proposals"]}
    if len(records) != len(proposal["proposals"]):
        raise ValueError("candidate curvature discovery duplicated an incoming box")
    payments, remaining = [], []
    for row in pending:
        if row["index"] not in selected:
            remaining.append(row)
            continue
        record = records[row["index"]]
        if record["source_closed_box"] != row:
            raise ValueError("candidate energy certificate belongs to different full closed bounds")
        result = energy.bound(kernel, original["matrix"], row["sharp_lower"], row["sharp_upper"],
                              record["certificate"], original["radius"], arcs)
        energy.strict_gate(result)
        payments.append({**row, "kind": "CANDIDATE_CURVATURE_ENERGY_EMPTY", **result})
    if len(payments) != len(selected) or len(payments) + len(remaining) != len(pending):
        raise ValueError("candidate curvature overlay lost an incoming box")
    return payments, remaining


def tiny_control(values):
    _, _, accepted, original, _, kernel, arcs, _, _ = values
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    lower, upper = [F(row[0]) for row in tiny], [F(row[1]) for row in tiny]
    box = tighten(original["matrix"], lower, upper)
    if box is None or not accepted["known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf"]:
        raise ValueError("candidate curvature method lost the feasible root tiny box or original LOCAL proof")
    lower, upper = box
    eta = F(100)
    for _ in range(7):
        try:
            quadratic.curvature_gate(kernel, original["matrix"], lower, upper, eta, arcs)
        except ValueError:
            eta *= 10
        else:
            break
    else:
        raise ValueError("candidate tiny-box curvature control could not be proved")
    certificate = {"reference_turns": list(map(str, lower)), "eta": str(eta),
                   "curvature_mode": "box-secant", "difference_dual": {"q": 1, "terms": []}}
    result = energy.bound(kernel, original["matrix"], lower, upper, certificate, original["radius"], arcs)
    if result["candidate_same_root_whole_closed_box_excluded"]:
        raise ValueError("candidate curvature falsely excluded its known feasible tiny root box")
    return {"known_feasible_root_tiny_box_not_energy_excluded": True,
            "original_LOCAL_leaf_and_52_coordinate_allowance_preserved": True,
            "tiny_box_control_certificate": certificate, "tiny_box_control_result": result}


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    print("Reconstructing every original candidate payment and actual remaining box.", flush=True)
    values = input_gate(folder)
    manifest, parent, accepted, original, pending, kernel, _, proposal, inventory = values
    payments, remaining = derive(values)
    positives = {**source.identity_control(kernel), **tiny_control(values)}
    regression = read(folder / "ADAPTER-REGRESSION.json")
    if (regression["tested_adapter_sha256"] != sha(energy.__file__)
            or len(regression["invalid_kernel_controls_rejected"]) != 7
            or regression["reference_sha256"] != sha(folder / "ORIGINAL-REFERENCE.json")
            or regression["kernel_sha256"] != sha(folder / "ORIGINAL-KERNEL.json")):
        raise ValueError("original candidate adapter regression evidence changed")
    selected, negatives = manifest["selected_source_OPEN_indices"], []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid candidate curvature payment accepted: " + label)

    reject("duplicate-current-candidate-box", lambda: derive(values, selected + selected[:1]))
    old_paid = next(row["index"] for row in read(local_path(manifest["source"]) / "LOWER-LEDGER.json"))
    reject("old-Dirichlet-payment-overwritten", lambda: derive(values, [old_paid]))
    bad = deepcopy(proposal)
    record = next(row for row in bad["proposals"] if row["source_OPEN_index"] == selected[0])
    record["source_closed_box"]["sharp_lower"][0] = str(F(record["source_closed_box"]["sharp_lower"][0]) - 1)
    reject("changed-full-incoming-candidate-box", lambda: derive(values, proposal_override=bad))
    bad = deepcopy(proposal)
    record = next(row for row in bad["proposals"] if row["source_OPEN_index"] == selected[0])
    record["certificate"]["eta"] = "-1"
    reject("negative-candidate-curvature-allowance", lambda: derive(values, proposal_override=bad))
    bad = deepcopy(proposal)
    record = next(row for row in bad["proposals"] if row["source_OPEN_index"] == selected[0])
    record["certificate"]["difference_dual"] = {"q": 1, "terms": [[0, 1, "-1"]]}
    reject("negative-candidate-difference-dual", lambda: derive(values, proposal_override=bad))
    equality = deepcopy(payments[0])
    equality["minimum_strict_energy_margin"] = "0"
    reject("candidate-energy-equality-not-strict", lambda: energy.strict_gate(equality))
    bad_kernel = read(folder / "ORIGINAL-KERNEL.json")
    bad_kernel["inverse_numerators"][0][0] = str(int(bad_kernel["inverse_numerators"][0][0]) + 1)
    reject("changed-original-candidate-ground-inverse",
           lambda: energy.kernel_gate(original["reference"], bad_kernel))
    bad_reference = deepcopy(original["reference"])
    bad_reference["edges"].append([0, 16])
    reject("full-type-or-future-rod-added-to-candidate",
           lambda: energy.kernel_gate(bad_reference, read(folder / "ORIGINAL-KERNEL.json")))
    certificate = {"schema": "N26-original-candidate-curvature-verified-OPEN-overlay-v1",
                   "radius_scope": "same-root-Rstar", "radius_upper": str(original["radius"]),
                   "source_acceptance_sha256": manifest["source_acceptance_sha256"],
                   "source_pending_angles_sha256": sha(folder / "SOURCE-PENDING-ANGLES.json"),
                   "all_original_tree_nodes_paid_leaves_and_closed_splits_unchanged": True,
                   "paid_actual_source_OPEN_indices": [row["index"] for row in payments]}
    for name, data in (("CERTIFICATE.json", certificate), ("LOWER-LEDGER.json", payments),
                       ("PENDING-ANGLES.json", remaining), ("POSITIVE-CONTROLS.json", positives)):
        path = folder / name
        if path.exists():
            if read(path) != data:
                raise ValueError("candidate curvature published semantic output changed: " + name)
        else:
            path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    inventory.extend(folder / name for name in manifest["copied_files"])
    hashes = {linux(path): sha(path) for path in inventory}
    report = {"schema": "N26-accepted-original-candidate-curvature-energy-overlay-v1",
              "verified": True, "radius_scope": "same-root-Rstar", "radius_upper": str(original["radius"]),
              "source_acceptance_sha256": manifest["source_acceptance_sha256"],
              "parent_current_audit_sha256": manifest["parent_current_audit_sha256"],
              "source_actual_remaining_closed_boxes": len(pending),
              "new_strict_whole_candidate_box_energy_exclusions": len(payments),
              "unresolved_closed_angle_boxes": len(remaining),
              "minimum_strict_energy_margin": str(min(F(row["minimum_strict_energy_margin"]) for row in payments)),
              "minimum_strict_radius_margin": str(min(F(row["minimum_strict_radius_margin"]) for row in payments)),
              "all_original_92_rods_46_free_vertices_inverse_and_frame_mapping_rechecked": True,
              "all_prior_local_force_Dirichlet_payments_closed_splits_and_unpaid_boxes_preserved": True,
              "all_candidate_energy_reference_curvature_and_duals_rechecked_on_actual_full_boxes": True,
              "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": True,
              "original_52_coordinate_local_allowance_unchanged": "7/800000",
              "current_global_combinatorial_frontier_nodes_removed": 0,
              "candidate_transport_global_lower_bound_proved": not remaining,
              "unrestricted_reduction_final_joint_acceptance": False,
              "full_catalog_complete": False, "global_lower_bound_proved": False,
              "global_optimality_proved": False, "n27_started": False,
              "negative_controls_rejected": negatives,
              "files": {name: sha(folder / name) for name in
                        ["MANIFEST.json", *manifest["copied_files"], "CERTIFICATE.json",
                         "LOWER-LEDGER.json", "PENDING-ANGLES.json", "POSITIVE-CONTROLS.json"]},
              "source_files": hashes, "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_candidate_curvature_overlay.py"]:
        raise ValueError("candidate curvature executed a different sealed checker")
    for text, digest in hashes.items():
        if sha(local_path(text)) != digest:
            raise ValueError("candidate curvature source bytes changed during final binding")
    for text, digest in parent["files"].items():
        if sha(local_path(text)) != digest:
            raise ValueError("candidate curvature current parent bytes changed during acceptance")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2),
          flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.source)
    proposal = read(args.proposal)
    if (read(args.source_replay) != accepted
            or proposal["source_acceptance_sha256"] != sha(args.source / "VERIFIED.json")):
        raise ValueError("candidate curvature builder lacks actual matching source evidence")
    selected = [row["source_OPEN_index"] for row in proposal["proposals"]
                if row["proposed_strict_candidate_energy_payment"]]
    if not selected:
        raise ValueError("no strict candidate curvature proposal to accept")
    source_manifest = read(args.source / "MANIFEST.json")
    continuation_folder = local_path(source_manifest["source"])
    pinning_folder = local_path(read(continuation_folder / "MANIFEST.json")["sources"]["pinning"])
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend([(args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
                   (args.source / "PENDING-ANGLES.json", "SOURCE-PENDING-ANGLES.json"),
                   (args.source / "DIRICHLET-KERNEL.json", "ORIGINAL-KERNEL.json"),
                   (pinning_folder / "CERTIFICATE.json", "ORIGINAL-REFERENCE.json"),
                   (args.parent_current_audit, "SOURCE-CURRENT-AUDIT.json"),
                   (args.proposal, "PROPOSAL.json"), (args.regression, "ADAPTER-REGRESSION.json")])
    for name in ("verify_candidate_curvature_overlay.py", "n26_candidate_curvature_energy.py",
                 "n26_quadratic_energy_minorant.py"):
        copies.append((Path(__file__).with_name(name), name))
    copies.append((Path(__file__).with_name("n26-candidate-curvature-energy-proof.md"), "PROOF.md"))
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest = {"schema": SCHEMA, "radius_scope": "same-root-Rstar",
                "source": linux(args.source), "source_replay": linux(args.source_replay),
                "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
                "parent_current_audit": linux(args.parent_current_audit),
                "parent_current_audit_sha256": sha(args.parent_current_audit),
                "source_remaining_boxes": accepted["unresolved_closed_angle_boxes"],
                "selected_source_OPEN_indices": selected,
                "copied_files": {name: sha(args.output / name) for _, name in copies}}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False, "selected_candidate_box_proposals": len(selected),
                      "independent_current_acceptance_pending": True}), flush=True)


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
