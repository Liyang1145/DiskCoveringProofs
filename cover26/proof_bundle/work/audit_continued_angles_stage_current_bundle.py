"""Current chain: broader pinning, accepted angular continuation, stage v7."""

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
    parser.add_argument("--sharp-parent-output", type=Path, required=True)
    parser.add_argument("--pin-parent-output", type=Path, required=True)
    parser.add_argument("--local-parent-output", type=Path, required=True)
    parser.add_argument("--angle-parent-output", type=Path, required=True)
    args = parser.parse_args()
    paths = (args.output, args.parent_output, args.sharp_parent_output, args.pin_parent_output,
             args.local_parent_output, args.angle_parent_output)
    if any(path.exists() for path in paths):
        raise FileExistsError("fresh current audit paths required")
    out = WORK.parent / "outputs"
    parent_script = WORK / "audit_centered_angles_stage_current_bundle.py"
    run = subprocess.run([
        sys.executable, str(parent_script), "--output", str(args.parent_output),
        "--parent-output", str(args.sharp_parent_output),
        "--pin-parent-output", str(args.pin_parent_output),
        "--local-parent-output", str(args.local_parent_output),
        "--angle-parent-output", str(args.angle_parent_output),
    ], check=False)
    if run.returncode:
        raise ValueError("prior entire upper/scope/centered-local/angle/stage chain failed")
    parent = json.loads(args.parent_output.read_text())
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["centered_entire_51_coordinate_Hessian_and_contact_stability_replayed"]
            or parent["candidate_angle_unresolved_closed_boxes"] != 34
            or parent["current_pending_cover_transport_subtrees"] != 2322):
        raise ValueError("prior v6 and four-local-box closure obligations were not replayed")
    inventory = [Path(__file__), parent_script, *paths[1:], out / "n26-STATUS.md",
                 out / "n26-continued-angle-and-stage-progress-20261010.md"]
    for path, digest in parent["files"].items():
        if sha(path) != digest:
            raise ValueError("prior proof bytes changed during current replay")
        inventory.append(Path(path))
    pin_folder = out / "n26-refined-anchor-pinning-v2"
    pin_report = report_and_replay(
        pin_folder, out / "n26-refined-anchor-pinning-published-replay-v2", inventory)
    pin = module_at("current_broader_individual_anchor_pinning", pin_folder / "verify_refined_anchor_pinning.py")
    proposal = json.loads((pin_folder / "CERTIFICATE.json").read_text())
    data = pin.source_gate(
        out / "n26-anchor-pinning-v3", out / "n26-positive-stress-v1",
        out / "n26-centered-local-barrier-v2", out / "n26-candidate-transport-control-v1", proposal)
    pin_result = pin.derive(*data[:5], proposal)
    if (any(pin_report[key] != value for key, value in pin_result.items())
            or F(pin_result["maximum_center_to_exact_rotated_root_euclidean_error_upper"]) >= F(3684, 10**9)):
        raise ValueError("broader all-anchor pinning result overclaimed")
    folder = out / "n26-continued-candidate-angles-v1"
    angle_report = report_and_replay(
        folder, out / "n26-continued-candidate-angles-published-replay-v1", inventory)
    checker = module_at("current_source_bound_continued_angle_checker", folder / "verify_continued_candidate_angles.py")
    proposed = json.loads((folder / "PROPOSAL.json").read_text())
    source, old_report, replay_pin, cells, radius_upper, inputs = checker.input_gate(
        out / "n26-refined-candidate-angles-v1", out / "n26-sharp-candidate-angles-v1",
        out / "n26-anchor-pinning-v3", out / "n26-positive-stress-v1",
        out / "n26-centered-local-barrier-v2", out / "n26-candidate-transport-control-v1",
        out / "n26-refined-anchor-pinning-v1", pin_folder, proposed)
    inventory.extend(inputs)
    nodes, result, pending, ledger, changed, newly_local, differences = checker.replay_continuation(
        source, old_report, replay_pin, cells, radius_upper, proposed, stage.load_trig(folder)[0])
    below_U = sum(F(row["required_radius_lower"]) <= stage.U for row in ledger if row["kind"] == "FORCE")
    sources = {
        **source["source_acceptance_sha256"],
        "starting_partition": sha(out / "n26-refined-candidate-angles-v1/VERIFIED.json"),
        "refined_pinning": sha(pin_folder / "VERIFIED.json"),
    }
    certificate = {
        "schema": "N26-source-bound-continued-sharp-candidate-angle-tree-v1",
        "radius_scope": "same-root-Rstar", "spec": source["spec"],
        "source_acceptance_sha256": sources,
        "source_certificate_sha256": sha(out / "n26-refined-candidate-angles-v1/CERTIFICATE.json"),
        "nodes": nodes,
    }
    if (any(angle_report[key] != value for key, value in result.items())
            or certificate != json.loads((folder / "CERTIFICATE.json").read_text())
            or pending != json.loads((folder / "PENDING-ANGLES.json").read_text())
            or ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())
            or differences != angle_report["event_count_differences"]
            or changed != angle_report["source_OPEN_roots_refined"]
            or newly_local != angle_report["newly_local_descendant_indices_from_wider_pinning"]
            or result["counts"] != {"SPLIT": 295, "FORCE": 215, "LOCAL": 13, "EMPTY": 0, "OPEN": 68}
            or differences["FORCE"] != 99 or differences["LOCAL"] != 8 or below_U != 77):
        raise ValueError("continued closed tree, new bounds, lineage, or retained OPEN boxes differ")
    folder = out / "n26-force-stage-v7"
    stage_report, files = bound_bundle(folder)
    inventory.extend(files)
    published = out / "n26-force-stage-published-replay-v7.json"
    if json.loads(published.read_text()) != stage_report:
        raise ValueError("seventh-stage published replay differs")
    inventory.append(published)
    _, incoming, old, multi, native, trace = stage.input_gate(folder, out / "n26-multislope-area-lower-v1")
    if incoming != json.loads((out / "n26-force-stage-v6/FRONTIER.json").read_text()):
        raise ValueError("seventh stage did not continue the accepted sixth frontier")
    frontier, stage_ledger, margins = stage.replay_trace(
        folder, incoming, old, multi, native, trace, stage.load_trig(folder)[0])
    if (frontier != json.loads((folder / "FRONTIER.json").read_text())
            or stage_ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("seventh-stage actual frontier or lower ledger differs")
    counts = {kind: sum(row[kind] for row in frontier["families"]) for kind in stage.KINDS}
    if (counts != stage_report["event_counts"]
            or frontier["families"] != stage_report["families"]
            or len(frontier["pending_states"]) != stage_report["pending_cover_transport_subtrees"]):
        raise ValueError("seventh-stage count overclaim")
    candidate = data[3]["prefix"]
    owners = [row for row in frontier["pending_states"] if row["B"] == 16
              and candidate[:len(row["prefix"])] == row["prefix"]]
    if len(owners) != 1:
        raise ValueError("known feasible candidate lost or duplicated")
    current = {
        "schema": "N26-current-source-bound-angle-continuation-and-seventh-stage-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True, "all_prior_upper_scope_and_lower_chain_replayed": True,
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": parent["r_strict_interval"],
        "full_52_coordinate_nonnegative_equilibrium_replayed": True,
        "centered_entire_51_coordinate_Hessian_and_contact_stability_replayed": True,
        "local_neighbourhood_in_original_52_coordinates": parent["local_neighbourhood_in_original_52_coordinates"],
        "local_optimality_proved": True,
        "broader_all_anchor_exact_extrema_and_actual_path_energy_pinning_replayed": True,
        "broader_pinning_center_error_upper": pin_result["maximum_center_to_exact_rotated_root_euclidean_error_upper"],
        "prior_all_proved_angular_nodes_and_closed_splits_preserved": True,
        "new_candidate_angle_force_boxes_strictly_excluded": differences["FORCE"],
        "new_candidate_angle_LOCAL_boxes_paid": differences["LOCAL"],
        "candidate_angle_tree_counts": result["counts"],
        "candidate_FORCE_bounds_above_Rstar_upper_but_at_most_U": below_U,
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
                      if key not in ("files", "broader_pinning_center_error_upper")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
