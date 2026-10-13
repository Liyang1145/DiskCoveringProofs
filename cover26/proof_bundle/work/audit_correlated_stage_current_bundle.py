"""Current complete chain through correlated support and global stage v9."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import WORK, publish
from audit_local_stage_current_bundle import bound_bundle
from audit_pinning_stage_current_bundle import module_at
from new_upper_scope import local_path, sha
import verify_force_stage as stage


def correlated_report_and_replay(folder, replay_folder, inventory):
    # The independent new bundle was published on Windows. Normalize its
    # provenance paths, not its bound bytes, before replaying the chain in WSL.
    report, files = bound_bundle(folder)
    inventory.extend(files)
    other, files = bound_bundle(replay_folder)
    inventory.extend(files)
    if report != other:
        raise ValueError("correlated standalone acceptance differs")
    for text, digest in report["source_files"].items():
        path = local_path(text.replace("\\", "/"))
        if sha(path) != digest:
            raise ValueError("correlated source provenance bytes changed")
        inventory.append(path)
    return report


def main():
    parser = argparse.ArgumentParser()
    for name in ("output", "parent-output", "continued-parent-output", "centered-parent-output",
                 "sharp-parent-output", "pin-parent-output", "local-parent-output", "angle-parent-output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--reuse-parent-sha256")
    args = parser.parse_args()
    paths = [getattr(args, key) for key in vars(args) if key != "reuse_parent_sha256"]
    if args.output.exists() or (not args.reuse_parent_sha256 and any(path.exists() for path in paths)):
        raise FileExistsError("fresh correlated chain audit paths required")
    out = WORK.parent / "outputs"
    parent_script = WORK / "audit_sharp_constraint_stage_current_bundle.py"
    if args.reuse_parent_sha256:
        if not all(path.exists() for path in paths[1:]) or sha(args.parent_output) != args.reuse_parent_sha256:
            raise ValueError("observed fresh parent replay artifact missing or changed")
    else:
        run = subprocess.run([
            sys.executable, str(parent_script), "--output", str(args.parent_output),
            "--parent-output", str(args.continued_parent_output),
            "--centered-parent-output", str(args.centered_parent_output),
            "--sharp-parent-output", str(args.sharp_parent_output),
            "--pin-parent-output", str(args.pin_parent_output),
            "--local-parent-output", str(args.local_parent_output),
            "--angle-parent-output", str(args.angle_parent_output)], check=False)
        if run.returncode:
            raise ValueError("prior complete upper/scope/local/sharp/stage chain failed")
    parent = json.loads(args.parent_output.read_text())
    if (not parent["current_bound_bytes_rechecked"]
            or parent["candidate_angle_unresolved_closed_boxes"] != 163
            or parent["current_pending_cover_transport_subtrees"] != 2654
            or not parent["sharp_radius_four_outward_sine_caps_independently_replayed"]):
        raise ValueError("eighth-stage and sharp-angle obligations not actually replayed")
    inventory = [Path(__file__), parent_script, *paths[1:], out / "n26-STATUS.md",
                 out / "n26-correlated-angle-and-stage-progress-20261010.md"]
    for path, digest in parent["files"].items():
        if sha(path) != digest:
            raise ValueError("prior full-chain input changed")
        inventory.append(Path(path))
    folder = out / "n26-correlated-candidate-angles-v1"
    accepted = correlated_report_and_replay(
        folder, out / "n26-correlated-candidate-angles-published-replay-v1", inventory)
    angle = module_at("current_correlated_sharp_angle_checker",
                      folder / "verify_correlated_candidate_angles.py")
    if (sha(angle.__file__) != accepted["files"]["verify_correlated_candidate_angles.py"]
            or sha(angle.correlated.__file__) != accepted["files"]["n26_correlated_arc_force.py"]):
        raise ValueError("current audit imported changed correlated acceptance arithmetic")
    inventory.extend((Path(angle.__file__), Path(angle.correlated.__file__)))
    if angle.correlated.controls(stage.load_trig(folder)[0]) != accepted["exact_correlated_force_positive_controls"]:
        raise ValueError("current correlated formula controls differ from accepted replay")
    source_folder = out / "n26-sharp-constraint-candidate-angles-v2"
    source, old_report, radius, cells, matrix, cap, old_pending, inputs = angle.source_gate(
        source_folder, out / "n26-continued-candidate-angles-v1",
        out / "n26-anchor-pinning-v3", out / "n26-positive-stress-v1",
        out / "n26-centered-local-barrier-v2", out / "n26-candidate-transport-control-v1",
        out / "n26-refined-anchor-pinning-v2", out / "n26-sharp-radius-angle-caps-v2")
    inventory.extend(inputs)
    proposal = json.loads((folder / "PROPOSAL.json").read_text())
    if (proposal["source_acceptance_sha256"] != sha(source_folder / "VERIFIED.json")
            or proposal["source_certificate_sha256"] != sha(source_folder / "CERTIFICATE.json")
            or proposal["spec"] != source["spec"] or proposal["radius_scope"] != "same-root-Rstar"):
        raise ValueError("current correlated proposal source changed")
    nodes, result, pending, ledger, auto_empty, auto_local = angle.replay_and_close(
        source, radius, cells, matrix, proposal, stage.load_trig(folder)[0])
    sources = {"starting_partition": sha(source_folder / "VERIFIED.json"),
               "historical_cap_basis": sha(out / "n26-continued-candidate-angles-v1/VERIFIED.json"),
               "sharp_caps": sha(out / "n26-sharp-radius-angle-caps-v2/VERIFIED.json"),
               "pinning": sha(out / "n26-refined-anchor-pinning-v2/VERIFIED.json"),
               "stress": sha(out / "n26-positive-stress-v1/VERIFIED.json"),
               "local": sha(out / "n26-centered-local-barrier-v2/VERIFIED.json"),
               "transport": sha(out / "n26-candidate-transport-control-v1/VERIFIED.json")}
    certificate = {"schema": "N26-correlated-sharp-radius-closed-angular-tree-v1",
                   "spec": source["spec"], "radius_scope": "same-root-Rstar",
                   "source_acceptance_sha256": sources, "nodes": nodes}
    expected = {"SPLIT": 576, "FORCE": 215, "LOCAL": 13, "EMPTY": 0,
                "OPEN": 177, "SHARP_FORCE": 76, "SHARP_LOCAL": 0,
                "SHARP_EMPTY": 3, "SHARP_CORRELATED_FORCE": 93}
    improved = sum(F(row["direct_arc_required_radius_lower"]) <= radius
                   for row in ledger if row["kind"] == angle.CORRELATED)
    below_U = sum(F(row["required_radius_lower"]) <= stage.U
                  for row in ledger if row["kind"] in ("FORCE", "SHARP_FORCE", angle.CORRELATED))
    if (any(accepted[key] != value for key, value in result.items())
            or certificate != json.loads((folder / "CERTIFICATE.json").read_text())
            or pending != json.loads((folder / "PENDING-ANGLES.json").read_text())
            or ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())
            or auto_empty != accepted["automatically_paid_sharp_empty_indices"]
            or auto_local != accepted["automatically_paid_sharp_local_indices"]
            or result["counts"] != expected
            or accepted["new_strict_direct_force_leaves"] != 45
            or accepted["new_strict_correlated_force_leaves"] != 93
            or improved != accepted["correlated_leaves_not_payable_by_their_direct_arc_bound"]):
        raise ValueError("correlated full-arc proof, partition or retained OPEN obligations differ")
    tiny = [tuple(map(F, row)) for row in cap["known_candidate_tiny_angle_cells"]]
    retained = any(row["kind"] in ("LOCAL", "SHARP_LOCAL") and all(
        F(lo) <= a <= b <= F(hi) for lo, hi, (a, b) in zip(
            row.get("sharp_lower", row["lower"]), row.get("sharp_upper", row["upper"]), tiny))
        for row in ledger if row["kind"] in ("LOCAL", "SHARP_LOCAL"))
    if not retained or not accepted["known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf"]:
        raise ValueError("known exact covering candidate lost from paid LOCAL region")
    folder = out / "n26-force-stage-v9"
    stage_report, files = bound_bundle(folder)
    inventory.extend(files)
    published = out / "n26-force-stage-published-replay-v9.json"
    if json.loads(published.read_text()) != stage_report:
        raise ValueError("ninth-stage published replay differs")
    inventory.append(published)
    _, incoming, old, multi, native, trace = stage.input_gate(folder, out / "n26-multislope-area-lower-v1")
    if incoming != json.loads((out / "n26-force-stage-v8/FRONTIER.json").read_text()):
        raise ValueError("ninth-stage source differs from accepted eighth-stage frontier")
    frontier, stage_ledger, margins = stage.replay_trace(
        folder, incoming, old, multi, native, trace, stage.load_trig(folder)[0])
    for name in native["files"]:
        inventory.append(folder / name)
    if (frontier != json.loads((folder / "FRONTIER.json").read_text())
            or stage_ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("ninth-stage frontier or exact lower ledger changed")
    counts = {kind: sum(row[kind] for row in frontier["families"]) for kind in stage.KINDS}
    if (counts != stage_report["event_counts"] or frontier["families"] != stage_report["families"]
            or len(frontier["pending_states"]) != stage_report["pending_cover_transport_subtrees"]):
        raise ValueError("ninth-stage event or pending counts overclaimed")
    candidate = [row for row in incoming["pending_states"] if row["B"] == 16 and row["prefix"] == [24, 40]]
    owners = [row for row in frontier["pending_states"] if row["B"] == 16
              and [24, 40][:len(row["prefix"])] == row["prefix"]]
    if len(candidate) != 1 or len(owners) != 1 or owners[0]["prefix"] != [24, 40]:
        raise ValueError("unique broad known-candidate owner lost or changed")
    for path, digest in parent["files"].items():
        if sha(path) != digest:
            raise ValueError("parent bound bytes changed during current audit")
    if (correlated_report_and_replay(
            out / "n26-correlated-candidate-angles-v1",
            out / "n26-correlated-candidate-angles-published-replay-v1", []) != accepted
            or bound_bundle(folder)[0] != stage_report
            or json.loads(published.read_text()) != stage_report):
        raise ValueError("new accepted bundle or published replay changed during current audit")
    if (sha(angle.correlated.__file__) != accepted["files"]["n26_correlated_arc_force.py"]
            or any(sha(folder / name) != digest for name, digest in native["files"].items())):
        raise ValueError("new arithmetic or native bound bytes changed during current audit")
    current = {
        "schema": "N26-current-correlated-angle-and-ninth-stage-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True,
        "all_prior_upper_scope_and_lower_chain_replayed": True,
        "already_observed_fresh_parent_replay_reused_with_exact_sha256": bool(args.reuse_parent_sha256),
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": parent["r_strict_interval"],
        "full_52_coordinate_nonnegative_equilibrium_replayed": True,
        "centered_entire_51_coordinate_Hessian_and_contact_stability_replayed": True,
        "local_neighbourhood_in_original_52_coordinates": parent["local_neighbourhood_in_original_52_coordinates"],
        "local_optimality_proved": True,
        "sharp_radius_four_outward_sine_caps_and_difference_matrix_replayed": True,
        "nonnegative_difference_dual_and_exact_divergence_recomputed": True,
        "full_turn_derivative_interval_errors_and_whole_arc_curvature_replayed": True,
        "prior_all_proved_angular_nodes_and_closed_splits_preserved": True,
        "new_candidate_angle_direct_force_boxes": 45,
        "new_candidate_angle_correlated_force_boxes": 93,
        "correlated_boxes_not_payable_by_same_flow_direct_arc_bound": improved,
        "candidate_angle_tree_counts": result["counts"],
        "candidate_angle_unresolved_closed_boxes": len(pending),
        "candidate_force_bounds_above_Rstar_upper_but_at_most_U": below_U,
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": retained,
        "candidate_transport_global_lower_bound_proved": False,
        "candidate_angle_classification_global_combinatorial_nodes_removed": 0,
        "new_native_events_and_all_siblings_replayed": len(trace["events"]),
        "new_stage_event_counts": counts,
        "new_stage_whole_transport_subtrees_strictly_excluded": stage_report["strictly_excluded_whole_transport_subtrees"],
        "current_families": frontier["families"],
        "current_pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "known_feasible_candidate_survives_in_exactly_one_current_subtree": owners[0]["prefix"],
        "all_old_forests_and_original_native_queues_preserved": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {str(path): sha(path) for path in inventory}}
    publish(args.output, current)
    print(json.dumps({key: value for key, value in current.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
