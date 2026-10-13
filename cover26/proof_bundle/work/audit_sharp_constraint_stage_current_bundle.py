"""Current chain: independently certified sharp constraints and stage v8."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import WORK, publish
from audit_local_stage_current_bundle import bound_bundle
from audit_pinning_stage_current_bundle import module_at
from audit_centered_angles_stage_current_bundle import report_and_replay
from new_upper_scope import sha
import verify_force_stage as stage


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--parent-output", type=Path, required=True)
    parser.add_argument("--centered-parent-output", type=Path, required=True)
    parser.add_argument("--sharp-parent-output", type=Path, required=True)
    parser.add_argument("--pin-parent-output", type=Path, required=True)
    parser.add_argument("--local-parent-output", type=Path, required=True)
    parser.add_argument("--angle-parent-output", type=Path, required=True)
    args = parser.parse_args()
    paths = (args.output, args.parent_output, args.centered_parent_output, args.sharp_parent_output,
             args.pin_parent_output, args.local_parent_output, args.angle_parent_output)
    if any(path.exists() for path in paths):
        raise FileExistsError("fresh current audit paths required")
    out = WORK.parent / "outputs"
    parent_script = WORK / "audit_continued_angles_stage_current_bundle.py"
    run = subprocess.run([
        sys.executable, str(parent_script), "--output", str(args.parent_output),
        "--parent-output", str(args.centered_parent_output),
        "--sharp-parent-output", str(args.sharp_parent_output),
        "--pin-parent-output", str(args.pin_parent_output),
        "--local-parent-output", str(args.local_parent_output),
        "--angle-parent-output", str(args.angle_parent_output),
    ], check=False)
    if run.returncode:
        raise ValueError("prior complete upper/scope/local/angle/stage chain failed")
    parent = json.loads(args.parent_output.read_text())
    if (not parent["current_bound_bytes_rechecked"]
            or parent["candidate_angle_unresolved_closed_boxes"] != 68
            or parent["current_pending_cover_transport_subtrees"] != 2448):
        raise ValueError("accepted seventh-stage and ordinary-angle obligations were not replayed")
    inventory = [Path(__file__), parent_script, *paths[1:], out / "n26-STATUS.md",
                 out / "n26-sharp-constraint-and-stage-progress-20261010.md"]
    for path, digest in parent["files"].items():
        if sha(path) != digest:
            raise ValueError("prior current replay dependency changed")
        inventory.append(Path(path))
    cap_folder = out / "n26-sharp-radius-angle-caps-v2"
    cap_report = report_and_replay(
        cap_folder, out / "n26-sharp-radius-angle-caps-published-replay-v2", inventory)
    cap = module_at("current_certified_sharp_chord_interface", cap_folder / "verify_sharp_radius_angle_caps.py")
    source_folder = out / "n26-continued-candidate-angles-v1"
    source, source_report, radius_upper, cells, pending_old, geometry_data, inputs = cap.source_gate(
        source_folder, out / "n26-anchor-pinning-v3", out / "n26-positive-stress-v1",
        out / "n26-centered-local-barrier-v2", out / "n26-candidate-transport-control-v1",
        out / "n26-refined-anchor-pinning-v2")
    inventory.extend(inputs)
    certificate = json.loads((cap_folder / "CERTIFICATE.json").read_text())
    cap_result, matrix, derivation = cap.derive(
        source, radius_upper, pending_old, geometry_data, certificate, stage.load_trig(source_folder)[0])
    if (any(cap_report[key] != value for key, value in cap_result.items())
            or matrix != json.loads((cap_folder / "MATRIX.json").read_text())
            or derivation != json.loads((cap_folder / "DERIVATION.json").read_text())
            or cap_result["candidate_OPEN_indices_infeasible_for_radius_at_most_Rstar"] != [487, 497, 509]):
        raise ValueError("independent sharp-cap interface or three infeasible source boxes differ")
    folder = out / "n26-sharp-constraint-candidate-angles-v2"
    angle_report = report_and_replay(
        folder, out / "n26-sharp-constraint-candidate-angles-published-replay-v2", inventory)
    angle = module_at("current_radius_conditional_sharp_tree", folder / "verify_sharp_constraint_candidate_angles.py")
    proposal = json.loads((folder / "PROPOSAL.json").read_text())
    replay_source, old_report, actual_upper, actual_cells, actual_matrix, cap_certificate, inputs = angle.input_gate(
        source_folder, out / "n26-anchor-pinning-v3", out / "n26-positive-stress-v1",
        out / "n26-centered-local-barrier-v2", out / "n26-candidate-transport-control-v1",
        out / "n26-refined-anchor-pinning-v2", cap_folder, proposal)
    inventory.extend(inputs)
    nodes, result, pending, ledger, auto_empty, auto_local, strict_new, local_new = angle.replay_and_close(
        replay_source, old_report, actual_upper, actual_cells, actual_matrix, proposal, stage.load_trig(folder)[0])
    sources = {
        "starting_partition": sha(source_folder / "VERIFIED.json"),
        "sharp_constraint_interface": sha(cap_folder / "VERIFIED.json"),
        "pinning": sha(out / "n26-refined-anchor-pinning-v2/VERIFIED.json"),
        "stress": sha(out / "n26-positive-stress-v1/VERIFIED.json"),
        "local": sha(out / "n26-centered-local-barrier-v2/VERIFIED.json"),
        "transport": sha(out / "n26-candidate-transport-control-v1/VERIFIED.json"),
    }
    angle_certificate = {
        "schema": "N26-sharp-radius-conditional-closed-angular-tree-v1",
        "radius_scope": "same-root-Rstar", "spec": source["spec"],
        "source_acceptance_sha256": sources, "nodes": nodes,
    }
    expected_counts = {"SPLIT": 424, "FORCE": 215, "LOCAL": 13, "EMPTY": 0,
                       "OPEN": 163, "SHARP_FORCE": 31, "SHARP_LOCAL": 0, "SHARP_EMPTY": 3}
    below_U = sum(F(row["required_radius_lower"]) <= stage.U for row in ledger
                  if row["kind"] in ("FORCE", "SHARP_FORCE"))
    if (any(angle_report[key] != value for key, value in result.items())
            or angle_certificate != json.loads((folder / "CERTIFICATE.json").read_text())
            or pending != json.loads((folder / "PENDING-ANGLES.json").read_text())
            or ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())
            or auto_empty != angle_report["automatically_paid_sharp_empty_indices"]
            or auto_local != angle_report["automatically_paid_sharp_local_indices"]
            or result["counts"] != expected_counts or strict_new != 31 or local_new != 0 or below_U != 108):
        raise ValueError("sharp conditional leaf semantics, exact bounds or retained OPEN boxes differ")
    tiny = [tuple(map(F, row)) for row in cap_certificate["known_candidate_tiny_angle_cells"]]
    retained = any(row["kind"] in ("LOCAL", "SHARP_LOCAL") and all(
        F(lo) <= a <= b <= F(hi) for lo, hi, (a, b) in zip(
            row.get("sharp_lower", row["lower"]), row.get("sharp_upper", row["upper"]), tiny))
        for row in ledger if row["kind"] in ("LOCAL", "SHARP_LOCAL"))
    if not retained or not angle_report["known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf"]:
        raise ValueError("known candidate positive control lost from local proof")
    folder = out / "n26-force-stage-v8"
    stage_report, files = bound_bundle(folder)
    inventory.extend(files)
    published = out / "n26-force-stage-published-replay-v8.json"
    if json.loads(published.read_text()) != stage_report:
        raise ValueError("eighth-stage standalone replay differs")
    inventory.append(published)
    _, incoming, old, multi, native, trace = stage.input_gate(folder, out / "n26-multislope-area-lower-v1")
    if incoming != json.loads((out / "n26-force-stage-v7/FRONTIER.json").read_text()):
        raise ValueError("eighth stage restarted from a different frontier")
    frontier, stage_ledger, margins = stage.replay_trace(
        folder, incoming, old, multi, native, trace, stage.load_trig(folder)[0])
    if (frontier != json.loads((folder / "FRONTIER.json").read_text())
            or stage_ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("eighth-stage actual frontier or lower ledger differs")
    counts = {kind: sum(row[kind] for row in frontier["families"]) for kind in stage.KINDS}
    if (counts != stage_report["event_counts"] or frontier["families"] != stage_report["families"]
            or len(frontier["pending_states"]) != stage_report["pending_cover_transport_subtrees"]):
        raise ValueError("eighth-stage count overclaim")
    candidate = geometry_data[3]["prefix"]
    owners = [row for row in frontier["pending_states"] if row["B"] == 16
              and candidate[:len(row["prefix"])] == row["prefix"]]
    if len(owners) != 1:
        raise ValueError("known feasible candidate lost or duplicated in the current global frontier")
    current = {
        "schema": "N26-current-sharp-radius-constraint-and-eighth-stage-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True, "all_prior_upper_scope_and_lower_chain_replayed": True,
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": parent["r_strict_interval"],
        "full_52_coordinate_nonnegative_equilibrium_replayed": True,
        "centered_entire_51_coordinate_Hessian_and_contact_stability_replayed": True,
        "local_neighbourhood_in_original_52_coordinates": parent["local_neighbourhood_in_original_52_coordinates"],
        "local_optimality_proved": True,
        "sharp_radius_four_outward_sine_caps_independently_replayed": True,
        "sharp_center_all_pairs_and_anchor_Bellman_Ford_replayed": True,
        "sharp_leaf_scope_radius_at_most_Rstar_not_unconditional_U_emptiness": True,
        "prior_all_proved_angular_nodes_and_closed_splits_preserved": True,
        "new_candidate_angle_strict_SHARP_FORCE_boxes": strict_new,
        "new_candidate_angle_radius_conditional_infeasible_boxes": result["counts"]["SHARP_EMPTY"],
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
        "files": {str(path): sha(path) for path in inventory},
    }
    publish(args.output, current)
    print(json.dumps({key: value for key, value in current.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
