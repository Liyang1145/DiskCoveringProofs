"""Current chain: larger unrestricted local box, nonlocal pinning, and stage v4."""

import argparse
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import WORK, publish
from new_upper_scope import sha
from audit_local_stage_current_bundle import bound_bundle
import verify_force_stage as stage


def module_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(path.parent))
    try:
        spec.loader.exec_module(module)
    finally:
        sys.path.pop(0)
    return module


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--parent-output", type=Path, required=True)
    parser.add_argument("--grandparent-output", type=Path, required=True)
    args = parser.parse_args()
    if any(p.exists() for p in (args.output, args.parent_output, args.grandparent_output)):
        raise FileExistsError("fresh current audit paths required")
    out = WORK.parent / "outputs"
    parent_script = WORK / "audit_local_stage_current_bundle.py"
    run = subprocess.run([
        sys.executable, str(parent_script), "--output", str(args.parent_output),
        "--parent-output", str(args.grandparent_output),
    ], check=False)
    if run.returncode:
        raise ValueError("full prior upper/scope/lower/stage chain failed current replay")
    parent = json.loads(args.parent_output.read_text())
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["same_root_entire_disk_cover_replayed"]
            or not parent["full_52_coordinate_nonnegative_equilibrium_replayed"]
            or parent["current_pending_cover_transport_subtrees"] != 1648):
        raise ValueError("parent replay did not reconstruct accepted v3 obligations")
    inventory = [Path(__file__), parent_script, args.parent_output, args.grandparent_output,
                 out / "n26-STATUS.md", out / "n26-pinning-and-stage-progress-20261010.md"]
    for path, digest in parent["files"].items():
        if sha(path) != digest:
            raise ValueError("parent current replay changed during audit")
        inventory.append(Path(path))
    local_folder = out / "n26-local-barrier-v3"
    local_report, files = bound_bundle(local_folder)
    inventory.extend(files)
    replay_report, files = bound_bundle(out / "n26-local-barrier-published-replay-v3")
    inventory.extend(files)
    if local_report != replay_report:
        raise ValueError("larger local standalone replay differs")
    local_checker = module_at("current_wider_local_checker", local_folder / "verify_local_barrier.py")
    local_proposal = json.loads((local_folder / "CERTIFICATE.json").read_text())
    original, root, records = local_checker.source_gate(out / "n26-positive-stress-v1", local_proposal)
    local_result = local_checker.derive(original, root, records, local_proposal, progress=True)
    if any(local_report[key] != value for key, value in local_result.items()):
        raise ValueError("larger local-neighbourhood report differs from exact replay")
    if (F(local_result["neighbourhood_halfwidth"]) != 50 * F(1, 10**8)
            or F(local_result["unrestricted_center_neighbourhood_halfwidth_before_rotation"]) != F(1, 16000000)):
        raise ValueError("claimed local expansion factor differs")
    pin_folder = out / "n26-anchor-pinning-v3"
    pin_report, files = bound_bundle(pin_folder)
    inventory.extend(files)
    pin_replay_report, files = bound_bundle(out / "n26-anchor-pinning-published-replay-v3")
    inventory.extend(files)
    if pin_report != pin_replay_report:
        raise ValueError("nonlocal pinning standalone replay differs")
    for path, digest in pin_report["source_files"].items():
        if sha(path) != digest:
            raise ValueError("nonlocal pinning source is no longer current")
        inventory.append(Path(path))
    pin = module_at("current_nonlocal_pinning_checker", pin_folder / "verify_anchor_pinning.py")
    proposal = json.loads((pin_folder / "CERTIFICATE.json").read_text())
    data = pin.source_gate(out / "n26-positive-stress-v1", local_folder,
                           out / "n26-candidate-transport-control-v1", proposal)
    pin_result = pin.derive(*data[:5], proposal)
    if any(pin_report[key] != value for key, value in pin_result.items()):
        raise ValueError("nonlocal pinning claim differs from exact rational replay")
    if (not pin_result["all_16_exact_unit_circle_conditions_used"]
            or not pin_result["no_prior_center_or_internal_witness_neighbourhood_hypothesis"]
            or pin_result["current_global_frontier_nodes_removed"] != 0
            or pin_result["covers_angular_complement"]
            or F(pin_result["maximum_center_to_exact_rotated_root_euclidean_error_upper"]) >= F(2815, 10**11)):
        raise ValueError("pinning scope or narrative error bound overclaimed")
    folder = out / "n26-force-stage-v4"
    stage_report, files = bound_bundle(folder)
    inventory.extend(files)
    published = out / "n26-force-stage-published-replay-v4.json"
    if json.loads(published.read_text()) != stage_report:
        raise ValueError("fourth-stage published replay differs")
    inventory.append(published)
    _, source, old, multi, native, trace = stage.input_gate(folder, out / "n26-multislope-area-lower-v1")
    if source != json.loads((out / "n26-force-stage-v3/FRONTIER.json").read_text()):
        raise ValueError("fourth stage did not continue the accepted third frontier")
    frontier, ledger, margins = stage.replay_trace(folder, source, old, multi, native, trace, stage.load_trig(folder)[0])
    if (frontier != json.loads((folder / "FRONTIER.json").read_text())
            or ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("fourth-stage frontier or lower ledger differs")
    counts = {kind: sum(row[kind] for row in frontier["families"]) for kind in stage.KINDS}
    if (counts != stage_report["event_counts"]
            or frontier["families"] != stage_report["families"]
            or len(frontier["pending_states"]) != stage_report["pending_cover_transport_subtrees"]):
        raise ValueError("fourth-stage count overclaim")
    candidate = data[3]["prefix"]
    owners = [r for r in frontier["pending_states"] if r["B"] == 16 and candidate[:len(r["prefix"])] == r["prefix"]]
    if len(owners) != 1 or owners[0]["prefix"] != [24, 40]:
        raise ValueError("known feasible candidate lost, duplicated, or owner changed unexpectedly")
    report = {
        "schema": "N26-current-nonlocal-pinning-and-fourth-stage-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True, "all_prior_upper_scope_and_lower_chain_replayed": True,
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": parent["r_strict_interval"],
        "full_52_coordinate_nonnegative_equilibrium_replayed": True,
        "strictly_positive_contact_stresses": 36, "exactly_zero_contact_stresses": 10,
        "larger_entire_51_coordinate_local_barrier_replayed": True, "local_neighbourhood_expansion_factor": 50,
        "local_neighbourhood_in_original_52_coordinates": local_result["unrestricted_center_neighbourhood_halfwidth_before_rotation"],
        "local_optimality_proved": True,
        "nonlocal_anchor_energy_to_local_neighbourhood_interface_replayed": True,
        "pinning_scope": "Candidate complete 34-face transport and specified closed 15-angle box only",
        "pinning_angle_width_turns": pin_result["maximum_angle_cell_width_turns"],
        "pinning_all_center_euclidean_error_upper": pin_result["maximum_center_to_exact_rotated_root_euclidean_error_upper"],
        "pinning_current_frontier_nodes_removed": 0, "pinning_covers_angular_complement": False,
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
    publish(args.output, report)
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "pinning_all_center_euclidean_error_upper")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
