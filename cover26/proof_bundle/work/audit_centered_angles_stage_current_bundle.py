"""Current chain: centered larger local proof, four paid OPEN boxes, stage v6."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import WORK, publish
from audit_local_stage_current_bundle import bound_bundle
from audit_pinning_stage_current_bundle import module_at
from new_upper_scope import sha
import verify_force_stage as stage


def report_and_replay(folder, replay_folder, inventory):
    report, files = bound_bundle(folder)
    inventory.extend(files)
    replay, files = bound_bundle(replay_folder)
    inventory.extend(files)
    if report != replay:
        raise ValueError("published standalone replay differs: " + folder.name)
    for path, digest in report.get("source_files", {}).items():
        if sha(path) != digest:
            raise ValueError("accepted new proof source changed")
        inventory.append(Path(path))
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--parent-output", type=Path, required=True)
    parser.add_argument("--pin-parent-output", type=Path, required=True)
    parser.add_argument("--local-parent-output", type=Path, required=True)
    parser.add_argument("--angle-parent-output", type=Path, required=True)
    args = parser.parse_args()
    paths = (args.output, args.parent_output, args.pin_parent_output, args.local_parent_output, args.angle_parent_output)
    if any(p.exists() for p in paths):
        raise FileExistsError("fresh current audit paths required")
    out = WORK.parent / "outputs"
    parent_script = WORK / "audit_sharp_angles_stage_current_bundle.py"
    run = subprocess.run([
        sys.executable, str(parent_script), "--output", str(args.parent_output),
        "--parent-output", str(args.pin_parent_output),
        "--older-parent-output", str(args.local_parent_output),
        "--oldest-parent-output", str(args.angle_parent_output),
    ], check=False)
    if run.returncode:
        raise ValueError("prior upper/scope/local/angle/global-stage chain failed current replay")
    parent = json.loads(args.parent_output.read_text())
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["same_root_entire_disk_cover_replayed"]
            or parent["candidate_angle_unresolved_closed_boxes"] != 38
            or parent["current_pending_cover_transport_subtrees"] != 2155):
        raise ValueError("prior v5 and original sharp-angle obligations were not replayed")
    inventory = [Path(__file__), parent_script, *paths[1:], out / "n26-STATUS.md",
                 out / "n26-centered-angle-and-stage-progress-20261010.md"]
    for path, digest in parent["files"].items():
        if sha(path) != digest:
            raise ValueError("prior replay source changed")
        inventory.append(Path(path))
    centered_folder = out / "n26-centered-local-barrier-v2"
    centered_report = report_and_replay(
        centered_folder, out / "n26-centered-local-barrier-published-replay-v2", inventory)
    centered = module_at("current_centered_local_proof", centered_folder / "verify_centered_local_barrier.py")
    proposal = json.loads((centered_folder / "CERTIFICATE.json").read_text())
    original, root, records = centered.source_gate(
        out / "n26-local-barrier-v3", out / "n26-positive-stress-v1", proposal)
    controls = centered.translation_controls()
    result = centered.derive(original, root, records, proposal, progress=True)
    if (any(centered_report[key] != value for key, value in result.items())
            or controls != centered_report["translation_positive_controls"]
            or F(result["unrestricted_center_neighbourhood_halfwidth_before_rotation"]) != 140 * F(1, 16000000)):
        raise ValueError("centered entire-box result or 140-fold expansion overclaimed")
    refined_folder = out / "n26-refined-anchor-pinning-v1"
    refined_report = report_and_replay(
        refined_folder, out / "n26-refined-anchor-pinning-published-replay-v1", inventory)
    refined = module_at("current_refined_nonlocal_pinning", refined_folder / "verify_refined_anchor_pinning.py")
    pin_proposal = json.loads((refined_folder / "CERTIFICATE.json").read_text())
    data = refined.source_gate(
        out / "n26-anchor-pinning-v3", out / "n26-positive-stress-v1", centered_folder,
        out / "n26-candidate-transport-control-v1", pin_proposal)
    pin_result = refined.derive(*data[:5], pin_proposal)
    if (any(refined_report[key] != value for key, value in pin_result.items())
            or F(pin_result["maximum_center_to_exact_rotated_root_euclidean_error_upper"]) >= F(2551, 10**9)):
        raise ValueError("refined individual-anchor pinning bound overclaimed")
    angle_folder = out / "n26-refined-candidate-angles-v1"
    angle_report = report_and_replay(
        angle_folder, out / "n26-refined-candidate-angles-published-replay-v1", inventory)
    angle = module_at("current_refined_candidate_angle_replay", angle_folder / "verify_refined_candidate_angles.py")
    certificate, angle_result, pending, angle_ledger, inputs, _, prior_report, _ = angle.reconstruct(
        out / "n26-sharp-candidate-angles-v1", out / "n26-anchor-pinning-v3",
        out / "n26-positive-stress-v1", centered_folder,
        out / "n26-candidate-transport-control-v1", refined_folder)
    inventory.extend(inputs)
    if (any(angle_report[key] != value for key, value in angle_result.items())
            or certificate != json.loads((angle_folder / "CERTIFICATE.json").read_text())
            or pending != json.loads((angle_folder / "PENDING-ANGLES.json").read_text())
            or angle_ledger != json.loads((angle_folder / "LOWER-LEDGER.json").read_text())
            or certificate["newly_paid_LOCAL_indices"] != [97, 98, 99, 100]
            or angle_result["counts"] != {"SPLIT": 154, "FORCE": 116, "LOCAL": 5, "EMPTY": 0, "OPEN": 34}):
        raise ValueError("four newly paid angle boxes or all retained complements differ")
    folder = out / "n26-force-stage-v6"
    stage_report, files = bound_bundle(folder)
    inventory.extend(files)
    published = out / "n26-force-stage-published-replay-v6.json"
    if json.loads(published.read_text()) != stage_report:
        raise ValueError("sixth-stage published replay differs")
    inventory.append(published)
    _, source, old, multi, native, trace = stage.input_gate(folder, out / "n26-multislope-area-lower-v1")
    if source != json.loads((out / "n26-force-stage-v5/FRONTIER.json").read_text()):
        raise ValueError("sixth stage did not continue accepted fifth-stage frontier")
    frontier, ledger, margins = stage.replay_trace(folder, source, old, multi, native, trace, stage.load_trig(folder)[0])
    if (frontier != json.loads((folder / "FRONTIER.json").read_text())
            or ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("sixth-stage frontier or lower ledger differs")
    counts = {kind: sum(row[kind] for row in frontier["families"]) for kind in stage.KINDS}
    if (counts != stage_report["event_counts"]
            or frontier["families"] != stage_report["families"]
            or len(frontier["pending_states"]) != stage_report["pending_cover_transport_subtrees"]):
        raise ValueError("sixth-stage counts overclaimed")
    candidate = data[3]["prefix"]
    owners = [row for row in frontier["pending_states"] if row["B"] == 16
              and candidate[:len(row["prefix"])] == row["prefix"]]
    if len(owners) != 1:
        raise ValueError("known feasible candidate lost or duplicated")
    current = {
        "schema": "N26-current-centered-local-refined-angle-and-sixth-stage-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True, "all_prior_upper_scope_and_lower_chain_replayed": True,
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": parent["r_strict_interval"],
        "full_52_coordinate_nonnegative_equilibrium_replayed": True,
        "exact_binomial_translation_and_all_contact_derivative_controls_replayed": controls,
        "centered_entire_51_coordinate_Hessian_and_contact_stability_replayed": True,
        "local_neighbourhood_expansion_relative_to_previous_v3": 140,
        "local_neighbourhood_in_original_52_coordinates": result["unrestricted_center_neighbourhood_halfwidth_before_rotation"],
        "local_optimality_proved": True,
        "per_anchor_exact_arc_extrema_and_actual_path_anchor_pinning_replayed": True,
        "refined_pinning_center_error_upper": pin_result["maximum_center_to_exact_rotated_root_euclidean_error_upper"],
        "prior_all_proved_angular_nodes_and_closed_splits_preserved": True,
        "newly_paid_candidate_LOCAL_indices": certificate["newly_paid_LOCAL_indices"],
        "candidate_angle_tree_counts": angle_result["counts"],
        "candidate_angle_unresolved_closed_boxes": len(pending),
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
        "files": {str(path): sha(path) for path in inventory},
    }
    publish(args.output, current)
    print(json.dumps({key: value for key, value in current.items()
                      if key not in ("files", "refined_pinning_center_error_upper")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
