"""Current upper/lower chain, complete partial sharp-angle tree, and stage v5."""

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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--parent-output", type=Path, required=True)
    parser.add_argument("--older-parent-output", type=Path, required=True)
    parser.add_argument("--oldest-parent-output", type=Path, required=True)
    args = parser.parse_args()
    paths = (args.output, args.parent_output, args.older_parent_output, args.oldest_parent_output)
    if any(p.exists() for p in paths):
        raise FileExistsError("fresh current audit paths required")
    out = WORK.parent / "outputs"
    parent_script = WORK / "audit_pinning_stage_current_bundle.py"
    run = subprocess.run([
        sys.executable, str(parent_script), "--output", str(args.parent_output),
        "--parent-output", str(args.older_parent_output),
        "--grandparent-output", str(args.oldest_parent_output),
    ], check=False)
    if run.returncode:
        raise ValueError("prior complete upper/scope/lower/stage chain failed current replay")
    parent = json.loads(args.parent_output.read_text())
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["same_root_entire_disk_cover_replayed"]
            or not parent["nonlocal_anchor_energy_to_local_neighbourhood_interface_replayed"]
            or parent["current_pending_cover_transport_subtrees"] != 2025):
        raise ValueError("prior stage v4 obligations were not actually replayed")
    inventory = [Path(__file__), parent_script, args.parent_output, args.older_parent_output,
                 args.oldest_parent_output, out / "n26-STATUS.md",
                 out / "n26-sharp-angle-and-stage-progress-20261010.md"]
    for path, digest in parent["files"].items():
        if sha(path) != digest:
            raise ValueError("prior current replay source changed")
        inventory.append(Path(path))
    folder = out / "n26-force-stage-v5"
    report, files = bound_bundle(folder)
    inventory.extend(files)
    published = out / "n26-force-stage-published-replay-v5.json"
    if json.loads(published.read_text()) != report:
        raise ValueError("fifth-stage published replay differs")
    inventory.append(published)
    _, source, old, multi, native, trace = stage.input_gate(folder, out / "n26-multislope-area-lower-v1")
    if source != json.loads((out / "n26-force-stage-v4/FRONTIER.json").read_text()):
        raise ValueError("fifth stage did not continue accepted fourth-stage frontier")
    frontier, ledger, margins = stage.replay_trace(folder, source, old, multi, native, trace, stage.load_trig(folder)[0])
    if (frontier != json.loads((folder / "FRONTIER.json").read_text())
            or ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("fifth-stage frontier or lower ledger differs")
    counts = {kind: sum(r[kind] for r in frontier["families"]) for kind in stage.KINDS}
    if (counts != report["event_counts"]
            or frontier["families"] != report["families"]
            or len(frontier["pending_states"]) != report["pending_cover_transport_subtrees"]):
        raise ValueError("fifth-stage count overclaim")
    candidate = json.loads((out / "n26-candidate-transport-control-v1/CANDIDATE-PATH.json").read_text())["prefix"]
    owners = [r for r in frontier["pending_states"] if r["B"] == 16 and candidate[:len(r["prefix"])] == r["prefix"]]
    if len(owners) != 1:
        raise ValueError("known feasible candidate was lost or duplicated")
    sharp_folder = out / "n26-sharp-candidate-angles-v1"
    sharp_report, files = bound_bundle(sharp_folder)
    inventory.extend(files)
    sharp_replay_report, files = bound_bundle(out / "n26-sharp-candidate-angles-published-replay-v1")
    inventory.extend(files)
    if sharp_report != sharp_replay_report:
        raise ValueError("published sharp candidate angle partition replay differs")
    for path, digest in sharp_report["source_files"].items():
        if sha(path) != digest:
            raise ValueError("sharp angle partition source changed")
        inventory.append(Path(path))
    sharp = module_at("current_complete_partial_sharp_tree", sharp_folder / "n26_sharp_candidate_angles.py")
    proposal = json.loads((sharp_folder / "CERTIFICATE.json").read_text())
    spec, radius_upper, cells, sources, inputs = sharp.input_gate(
        out / "n26-positive-stress-v1", out / "n26-local-barrier-v3",
        out / "n26-candidate-transport-control-v1", out / "n26-anchor-pinning-v3", proposal)
    inventory.extend(inputs)
    result, pending, angle_ledger = sharp.replay(spec, radius_upper, cells, proposal["nodes"],
                                               stage.load_trig(sharp_folder)[0])
    if (any(sharp_report[key] != value for key, value in result.items())
            or pending != json.loads((sharp_folder / "PENDING-ANGLES.json").read_text())
            or angle_ledger != json.loads((sharp_folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("sharp angular partition, actual lower bounds, or retained OPEN leaves differ")
    direct = sys.modules["n26_direct_arc_force"]
    if sha(direct.__file__) != sharp_report["files"]["n26_direct_arc_force.py"]:
        raise ValueError("direct arc checker differs from the published exact arithmetic")
    controls = direct.regular_ring_controls(stage.load_trig(sharp_folder)[0])
    if controls != sharp_report["direct_arc_force_positive_controls"]:
        raise ValueError("direct arc positive controls failed")
    below_U = sum(F(r["required_radius_lower"]) <= stage.U for r in angle_ledger if r["kind"] == "FORCE")
    if (result["counts"] != {"SPLIT": 154, "FORCE": 116, "LOCAL": 1, "EMPTY": 0, "OPEN": 38}
            or below_U != 9 or result["candidate_transport_global_lower_bound_proved"]):
        raise ValueError("current sharp angular narrative overclaims")
    current = {
        "schema": "N26-current-sharp-candidate-angle-and-fifth-stage-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True, "all_prior_upper_scope_and_lower_chain_replayed": True,
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": parent["r_strict_interval"],
        "full_52_coordinate_nonnegative_equilibrium_replayed": True,
        "larger_entire_51_coordinate_local_barrier_replayed": True,
        "local_neighbourhood_in_original_52_coordinates": parent["local_neighbourhood_in_original_52_coordinates"],
        "local_optimality_proved": True,
        "nonlocal_anchor_energy_to_local_neighbourhood_interface_replayed": True,
        "direct_exact_circle_arc_force_divergence_and_radius_bounds_replayed": True,
        "direct_arc_force_positive_controls": controls,
        "entire_candidate_necessary_angle_domain_partitioned_with_all_complements_retained": True,
        "candidate_angle_tree_counts": result["counts"],
        "candidate_angle_force_certificates_strictly_above_Rstar_upper_but_at_most_U": below_U,
        "candidate_angle_minimum_strict_force_margin_above_Rstar_upper": result["minimum_strict_force_margin_above_Rstar_upper"],
        "candidate_transport_global_lower_bound_proved": False,
        "candidate_angle_unresolved_closed_boxes": len(pending),
        "candidate_angle_classification_global_combinatorial_nodes_removed": 0,
        "new_native_events_and_all_siblings_replayed": len(trace["events"]),
        "new_stage_event_counts": counts,
        "new_stage_whole_transport_subtrees_strictly_excluded": report["strictly_excluded_whole_transport_subtrees"],
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
