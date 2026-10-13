"""Standalone exact Dirichlet payments on semantically replayed current OPEN."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
import continue_current_candidate_angles as source_checker
from n26_force import load_trig
import n26_dirichlet_energy as energy


leaf = source_checker.leaf
read, sha = source_checker.read, leaf.sha


def source_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-current-candidate-Dirichlet-overlay-bindings-v1":
        raise ValueError("wrong Dirichlet overlay bindings")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("sealed Dirichlet input changed")
    source_folder = leaf.local_path(manifest["source"])
    accepted, inventory = leaf.bound(source_folder)
    if (accepted["schema"] != "N26-accepted-current-candidate-angle-continuation-v1"
            or sha(source_folder / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or read(leaf.local_path(manifest["source_replay"])) != accepted
            or read(folder / "SOURCE-ACCEPTANCE.json") != accepted
            or sha(source_checker.__file__) != accepted["files"]["continue_current_candidate_angles.py"]):
        raise ValueError("Dirichlet overlay source lacks its sealed actual replay")
    source_manifest, paths, values, source_proposal = source_checker.input_gate(source_folder)
    arcs = load_trig(source_folder)[0]
    nodes, result, pending, ledger, empty, local = source_checker.continuation.replay_and_close(
        values, source_proposal, arcs)
    certificate = {
        "schema": "N26-current-candidate-continued-closed-angular-tree-v1",
        "radius_scope": "same-root-Rstar", "spec": values["source"]["spec"],
        "source_acceptance_sha256": source_manifest["source_acceptance_sha256"], "nodes": nodes}
    if (certificate != read(source_folder / "CERTIFICATE.json")
            or certificate != read(folder / "SOURCE-CERTIFICATE.json")
            or pending != read(source_folder / "PENDING-ANGLES.json")
            or ledger != read(source_folder / "LOWER-LEDGER.json")
            or any(accepted[key] != value for key, value in result.items())
            or empty != accepted["automatically_paid_sharp_empty_indices"]
            or local != accepted["automatically_paid_sharp_local_indices"]):
        raise ValueError("Dirichlet source tree, all hull payments or OPEN did not semantically replay")
    inventory.extend(values["inventory"])
    inventory.extend([leaf.local_path(manifest["source_replay"]), Path(source_checker.__file__)])
    discovery = read(folder / "PROPOSAL.json")
    if (discovery["schema"] != "N26-unaccepted-current-candidate-Dirichlet-energy-overlay-v1"
            or discovery["verified"] is not False or discovery["radius_scope"] != "same-root-Rstar"
            or discovery["source_acceptance_sha256"] != manifest["source_acceptance_sha256"]
            or discovery["pinning_acceptance_sha256"] != sha(paths[9] / "VERIFIED.json")
            or discovery["cap_acceptance_sha256"] != sha(paths[10] / "VERIFIED.json")
            or discovery["kernel_sha256"] != sha(folder / "DIRICHLET-KERNEL.json")
            or sha(energy.__file__) != manifest["copied_files"]["n26_dirichlet_energy.py"]):
        raise ValueError("Dirichlet discovery changed source, radius, rods or exact arithmetic")
    reference = values["reference"]
    geometry, edges, suggested, t = leaf.refined.base.root_geometry(*values["data"][:3])
    if (reference["edges"] != [list(row) for row in edges]
            or reference["radius_scope"] != "at-most-the-certified-same-root-Rstar"
            or F(values["data"][4]["unrestricted_center_neighbourhood_halfwidth_before_rotation"]) != F(7, 800000)
            or certificate["spec"]["faces"] != values["source"]["spec"]["faces"]):
        raise ValueError("Dirichlet graph is not the semantically accepted same-root positive rod support")
    kernel = energy.kernel_gate(reference, read(folder / "DIRICHLET-KERNEL.json"))
    return manifest, accepted, values, certificate, pending, ledger, discovery, kernel, arcs, inventory


def derive(pending, indices, kernel, radius, arcs):
    if (not isinstance(indices, list) or not indices or any(type(i) is not int for i in indices)
            or len(set(indices)) != len(indices)):
        raise ValueError("invalid or duplicated Dirichlet payment indices")
    by_index = {row["index"]: row for row in pending}
    if len(by_index) != len(pending) or not set(indices) <= set(by_index):
        raise ValueError("Dirichlet payment is not an actually retained current OPEN leaf")
    payments, remaining = [], []
    for row in pending:
        if row["index"] not in indices:
            remaining.append(row)
            continue
        result = energy.bound(row["sharp_lower"], row["sharp_upper"], kernel, radius**2, arcs)
        if not result["radius_conditional_whole_angle_box_excluded"]:
            raise ValueError("Dirichlet whole-box energy payment is not strict")
        payments.append({**row, "kind": "DIRICHLET_EMPTY", **result})
    if len(payments) + len(remaining) != len(pending):
        raise ValueError("Dirichlet overlay lost a source OPEN box")
    return payments, remaining


def strict_gate(lower, upper):
    if F(lower) <= F(upper):
        raise ValueError("energy payment must be strict")


def identity_control(kernel):
    """Independent direct-edge energy versus eliminated quadratic form."""
    scale, den = kernel["scale"], kernel["inverse_denominator"]
    anchors = [[F((3 * i + 1) % 7 - 3), F((5 * i + 2) % 11 - 5)] for i in range(16)]
    internal = [[F((7 * i + 3) % 13 - 6), F((11 * i + 4) % 17 - 8)] for i in range(46)]
    all_points = anchors + internal
    direct = sum(F(kernel["matrix"][i][j], scale) * sum(all_points[i][d] * all_points[j][d]
                                                      for d in range(2))
                 for i in range(62) for j in range(62) if kernel["matrix"][i][j])
    boundary = sum(F(w, scale * den) * sum((anchors[i][d] - anchors[j][d])**2 for d in range(2))
                   for i, j, w in kernel["pair_weights"])
    deviation = [[internal[i][d] - sum(F(kernel["harmonic"][i][j], den) * anchors[j][d]
                                       for j in range(16)) for d in range(2)] for i in range(46)]
    residual = sum(F(kernel["matrix"][16 + i][16 + j], scale) *
                   sum(deviation[i][d] * deviation[j][d] for d in range(2))
                   for i in range(46) for j in range(46) if kernel["matrix"][16 + i][16 + j])
    if direct != boundary + residual or residual < 0:
        raise AssertionError("independent exact Dirichlet energy identity failed")
    return {"independent_rational_two_coordinate_energy_identity": True,
            "grounded_residual_energy_nonnegative": True}


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    manifest, accepted, values, source, pending, ledger, discovery, kernel, arcs, inventory = source_gate(folder)
    hashes = {linux(path): sha(path) for path in inventory}
    payments, remaining = derive(pending, discovery["proposed_paid_OPEN_indices"], kernel, values["radius"], arcs)
    positives = identity_control(kernel)
    tiny = values["cap"]["known_candidate_tiny_angle_cells"]
    tiny_bound = energy.bound([row[0] for row in tiny], [row[1] for row in tiny],
                              kernel, values["radius"]**2, arcs)
    if (tiny_bound["radius_conditional_whole_angle_box_excluded"]
            or not accepted["known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf"]):
        raise ValueError("exact Dirichlet method rejected the known feasible candidate tiny box")
    positives["same_root_tiny_angle_box_not_falsely_energy_excluded"] = True
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid Dirichlet overlay accepted: " + label)

    bad_kernel = read(folder / "DIRICHLET-KERNEL.json")
    bad_kernel["inverse_numerators"][0][0] = str(int(bad_kernel["inverse_numerators"][0][0]) + 1)
    reject("changed-integer-ground-inverse",
           lambda: energy.kernel_gate(values["reference"], bad_kernel))
    bad_reference = deepcopy(values["reference"])
    bad_reference["weight_numerators"][0] = "0"
    reject("nonpositive-rod-energy-weight",
           lambda: energy.kernel_gate(bad_reference, read(folder / "DIRICHLET-KERNEL.json")))
    reject("unreachable-paid-leaf", lambda: derive(pending, [len(source["nodes"])], kernel, values["radius"], arcs))
    reject("duplicate-energy-payment", lambda: derive(
        pending, discovery["proposed_paid_OPEN_indices"] + discovery["proposed_paid_OPEN_indices"][:1],
        kernel, values["radius"], arcs))
    reject("old-proved-leaf-overwritten", lambda: derive(
        pending, [next(i for i, node in enumerate(source["nodes"]) if node["kind"] != "OPEN")],
        kernel, values["radius"], arcs))
    reject("nonstrict-energy-payment", lambda: strict_gate(values["radius"], values["radius"]))
    unpaid = next((row["index"] for row in remaining), None)
    if unpaid is not None:
        reject("unpaid-box-falsely-closed", lambda: derive(pending, [unpaid], kernel, values["radius"], arcs))
    certificate = {
        "schema": "N26-current-candidate-exact-Dirichlet-OPEN-overlay-v1",
        "radius_scope": "same-root-Rstar", "radius_upper": str(values["radius"]),
        "source_tree_sha256": sha(folder / "SOURCE-CERTIFICATE.json"),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "all_source_nodes_and_closed_splits_unchanged": True,
        "paid_source_OPEN_indices": [row["index"] for row in payments]}
    for name, value in (("CERTIFICATE.json", certificate), ("LOWER-LEDGER.json", payments),
                        ("PENDING-ANGLES.json", remaining), ("POSITIVE-CONTROLS.json", positives)):
        source_checker.publish_or_match(folder / name, value)
    counts = {**accepted["counts"], "OPEN": len(remaining), "DIRICHLET_EMPTY": len(payments)}
    report = {
        "schema": "N26-accepted-current-candidate-Dirichlet-energy-overlay-v1",
        "verified": True, "radius_scope": "same-root-Rstar", "radius_upper": str(values["radius"]),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_angle_nodes": accepted["nodes"], "source_OPEN_boxes": len(pending),
        "new_strict_whole_box_Dirichlet_energy_exclusions": len(payments),
        "minimum_strict_energy_margin": str(min(F(row["strict_energy_exclusion_margin"]) for row in payments)),
        "counts_with_separate_verified_overlay": counts,
        "unresolved_closed_angle_boxes": len(remaining),
        "all_source_nodes_paid_leaves_and_closed_splits_preserved": True,
        "all_unpaid_source_OPEN_boxes_retained_unchanged": True,
        "exact_integer_ground_inverse_identity_independently_rechecked": True,
        "all_positive_rods_free_centers_and_internal_witnesses_eliminated_exactly": True,
        "no_float_or_symbolic_library_used_by_standalone_checker": True,
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": True,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "positive_controls": positives, "negative_controls_rejected": negatives,
        "candidate_transport_global_lower_bound_proved": not remaining,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: sha(folder / name) for name in [
            "MANIFEST.json", *manifest["copied_files"], "CERTIFICATE.json", "LOWER-LEDGER.json",
            "PENDING-ANGLES.json", "POSITIVE-CONTROLS.json"]},
        "source_files": hashes, "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_dirichlet_candidate_overlay.py"]:
        raise ValueError("Dirichlet overlay executed different arithmetic")
    for text, digest in hashes.items():
        if sha(leaf.local_path(text)) != digest:
            raise ValueError("Dirichlet source bytes changed during exact replay")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("Dirichlet sealed input changed during exact replay")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2),
          flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = leaf.bound(args.source)
    args.output.mkdir(parents=True)
    copies = [(args.source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend([(args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
                   (args.source / "CERTIFICATE.json", "SOURCE-CERTIFICATE.json"),
                   (args.proposal, "PROPOSAL.json"), (args.kernel, "DIRICHLET-KERNEL.json"),
                   (Path(energy.__file__), "n26_dirichlet_energy.py"),
                   (Path(__file__), "verify_dirichlet_candidate_overlay.py"),
                   (Path(__file__).with_name("n26-Dirichlet-overlay-proof.md"), "PROOF.md")])
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest = {
        "schema": "N26-current-candidate-Dirichlet-overlay-bindings-v1",
        "source": linux(args.source.resolve()), "source_replay": linux(args.source_replay.resolve()),
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "copied_files": {name: sha(args.output / name) for _, name in copies}}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    subprocess.run([sys.executable, str(args.output / "verify_dirichlet_candidate_overlay.py"),
                    "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=True)


def main():
    parser = argparse.ArgumentParser()
    for key in ("input", "report", "source", "source-replay", "proposal", "kernel", "output"):
        parser.add_argument("--" + key, type=Path)
    args = parser.parse_args()
    if args.input and args.report:
        verify(args.input.resolve(), args.report.resolve())
    elif all((args.source, args.source_replay, args.proposal, args.kernel, args.output)):
        build(args)
    else:
        parser.error("provide replay or full build inputs")


if __name__ == "__main__":
    main()
