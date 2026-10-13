"""Current full chain including exact same-root stress/local bound and stage v3."""

import argparse
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import WORK, publish
from new_upper_scope import sha
import verify_positive_stress as stress_checker
import verify_force_stage as stage_checker


def module_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def bound_bundle(folder):
    path = folder / "VERIFIED.json"
    report = json.loads(path.read_text())
    if not report["verified"] or report["global_optimality_proved"]:
        raise ValueError("accepted bundle has a wrong scope")
    inventory = [path]
    for name, digest in {**report["files"], **report.get("additional_files", {})}.items():
        target = folder / name
        if sha(target) != digest:
            raise ValueError("accepted bundle bytes changed: " + str(target))
        inventory.append(target)
    return report, inventory


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--parent-output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.parent_output.exists():
        raise FileExistsError("fresh audit paths required")
    out = WORK.parent / "outputs"
    # Re-execute the previously inspected full-chain audit, rather than accept
    # an old green marker whose bound status document has since changed.
    parent_script = WORK / "audit_angular_stage_current_bundle.py"
    run = subprocess.run([sys.executable, str(parent_script), "--output", str(args.parent_output)],
                         check=False)
    if run.returncode:
        raise ValueError("prior stage full-chain current replay failed")
    parent = json.loads(args.parent_output.read_text())
    if not parent["current_bound_bytes_rechecked"] or not parent["same_root_entire_disk_cover_replayed"]:
        raise ValueError("prior full-chain replay missing actual upper/lower obligations")
    inventory = [Path(__file__), parent_script, args.parent_output, out / "n26-STATUS.md",
                 out / "n26-local-and-stage-progress-20261010.md"]
    for path, digest in parent["files"].items():
        if sha(path) != digest:
            raise ValueError("prior replay dependency changed")
    stress_folder = out / "n26-positive-stress-v1"
    stress_report, files = bound_bundle(stress_folder)
    inventory.extend(files)
    stress_replay = out / "n26-positive-stress-published-replay-v1"
    replay_report, files = bound_bundle(stress_replay)
    inventory.extend(files)
    if replay_report != stress_report:
        raise ValueError("standalone same-root stress replay differs")
    original = json.loads((stress_folder / "ORIGINAL-SYSTEM.json").read_text())
    modified = json.loads((stress_folder / "SYSTEM.json").read_text())
    old_root = json.loads((stress_folder / "ORIGINAL-ROOT-CERTIFICATE.json").read_text())
    new_root = json.loads((stress_folder / "ROOT-CERTIFICATE.json").read_text())
    root_folder = out / "n26-same-root-cover-v2"
    if (sha(stress_folder / "ORIGINAL-SYSTEM.json") != sha(root_folder / "SYSTEM.json")
            or sha(stress_folder / "ORIGINAL-ROOT-CERTIFICATE.json") != sha(root_folder / "ROOT-CERTIFICATE.json")
            or new_root["system_sha256"] != sha(stress_folder / "SYSTEM.json")):
        raise ValueError("new stress root is not bound to the accepted covering root")
    polys = stress_checker.shape_gate(original, modified)
    old_check = stress_checker.exact.verify(original, old_root, F(1, 10**80))
    new_check = stress_checker.exact.verify(modified, new_root, F(1, 10**85))
    old_z, old_box = stress_checker.interval_root(old_root, F(1, 10**80))
    new_z, new_box = stress_checker.interval_root(new_root, F(1, 10**85))
    if any(not old_box[i][0] < new_box[i][0] < new_box[i][1] < old_box[i][1] for i in range(26)):
        raise ValueError("same-root uniqueness containment failed")
    transported = stress_checker.transport_checks(original, new_root, polys)
    if transported != json.loads((stress_folder / "STRESS-LEDGER.json").read_text()):
        raise ValueError("full-coordinate equilibrium ledger differs from exact replay")
    if old_check != stress_report["original_root_check"] or new_check != stress_report["modified_root_check"]:
        raise ValueError("root contraction report differs")
    local_folder = out / "n26-local-barrier-v2"
    local_report, files = bound_bundle(local_folder)
    inventory.extend(files)
    local_replay_folder = out / "n26-local-barrier-published-replay-v2"
    local_replay_report, files = bound_bundle(local_replay_folder)
    inventory.extend(files)
    if local_replay_report != local_report or not local_report["local_optimality_proved"]:
        raise ValueError("published local lower replay differs")
    local = module_at("bound_current_local_checker", local_folder / "verify_local_barrier.py")
    proposal = json.loads((local_folder / "CERTIFICATE.json").read_text())
    local_original, local_root, records = local.source_gate(stress_folder, proposal)
    local_result = local.derive(local_original, local_root, records, proposal, progress=True)
    if any(local_report[key] != value for key, value in local_result.items()):
        raise ValueError("unrestricted local-neighbourhood lower report overclaims")
    folder = out / "n26-force-stage-v3"
    stage_report, files = bound_bundle(folder)
    inventory.extend(files)
    published_path = out / "n26-force-stage-published-replay-v3.json"
    if json.loads(published_path.read_text()) != stage_report:
        raise ValueError("new 2400-event published replay differs")
    inventory.append(published_path)
    area_folder = out / "n26-multislope-area-lower-v1"
    _, source, old, multi, native, trace = stage_checker.input_gate(folder, area_folder)
    if source != json.loads((out / "n26-force-stage-v2/FRONTIER.json").read_text()):
        raise ValueError("third stage did not continue the fully accepted second-stage frontier")
    arcs = stage_checker.load_trig(folder)[0]
    frontier, ledger, margins = stage_checker.replay_trace(folder, source, old, multi, native, trace, arcs)
    if frontier != json.loads((folder / "FRONTIER.json").read_text()):
        raise ValueError("third stage frontier differs")
    if ledger != json.loads((folder / "LOWER-LEDGER.json").read_text()):
        raise ValueError("third stage lower ledger differs")
    counts = {kind: sum(row[kind] for row in frontier["families"]) for kind in stage_checker.KINDS}
    if counts != stage_report["event_counts"] or len(frontier["pending_states"]) != stage_report["pending_cover_transport_subtrees"]:
        raise ValueError("third stage report overclaims")
    control_folder = out / "n26-candidate-transport-control-v1"
    control = json.loads((control_folder / "VERIFIED.json").read_text())
    if not control["verified"] or not control["native_final_state_independently_matched"]:
        raise ValueError("known full-cover positive control absent")
    for path, digest in control["files"].items():
        if sha(path) != digest:
            raise ValueError("candidate transport positive-control input changed")
        inventory.append(Path(path))
    inventory.append(control_folder / "VERIFIED.json")
    candidate_path = json.loads((control_folder / "CANDIDATE-PATH.json").read_text())
    p = candidate_path["prefix"]
    owners = [row for row in frontier["pending_states"] if row["B"] == 16 and p[:len(row["prefix"])] == row["prefix"]]
    if len(owners) != 1:
        raise ValueError("known feasible candidate was lost or duplicated in the current frontier")
    inventory.extend((WORK / "verify_positive_stress.py", WORK / "verify_force_stage.py",
                      WORK / "audit_candidate_transport.py"))
    report = {
        "schema": "N26-current-local-lower-and-third-stage-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True,
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": new_check["r_strict_interval"],
        "same_root_stress_transport_and_uniqueness_replayed": True,
        "full_52_coordinate_nonnegative_equilibrium_replayed": True,
        "strictly_positive_contact_stresses": 36, "exactly_zero_contact_stresses": 10,
        "entire_51_coordinate_local_barrier_and_contact_stability_replayed": True,
        "local_optimality_proved": True,
        "local_neighbourhood_in_original_52_coordinates": local_result["unrestricted_center_neighbourhood_halfwidth_before_rotation"],
        "local_equality_scope": "Only overall rotations of the specified labelled root within the stated neighbourhood",
        "prior_full_chain_replayed": True,
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
    publish(args.output, report)
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
