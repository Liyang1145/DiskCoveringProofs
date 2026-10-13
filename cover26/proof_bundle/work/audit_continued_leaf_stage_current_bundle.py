"""Current full chain: continued leaf angles, stage v11 and selected terminal types."""

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
    parser.add_argument("--parent-prefix", type=Path, required=True)
    args = parser.parse_args()
    parent_output = args.parent_prefix.with_name(args.parent_prefix.name + "-leaf-v10.json")
    older_prefix = args.parent_prefix.with_name(args.parent_prefix.name + "-older")
    if args.output.exists() or parent_output.exists():
        raise FileExistsError("fresh continued-leaf audit paths required")
    out = WORK.parent / "outputs"
    parent_script = WORK / "audit_leaf_pinned_stage_current_bundle.py"
    run = subprocess.run([sys.executable, str(parent_script), "--output", str(parent_output),
                          "--parent-prefix", str(older_prefix)], check=False)
    if run.returncode:
        raise ValueError("complete leaf-pinned and tenth-stage chain failed current replay")
    parent = json.loads(parent_output.read_text())
    if (not parent["current_bound_bytes_rechecked"] or parent["candidate_angle_unresolved_closed_boxes"] != 77
            or parent["current_pending_cover_transport_subtrees"] != 3331
            or parent["current_unresolved_terminal_subtrees"] != 10):
        raise ValueError("prior full-chain obligations not actually replayed")
    inventory = [Path(__file__), parent_script, parent_output, out / "n26-STATUS.md",
                 out / "n26-continued-leaf-and-terminal-stage-progress-20261010.md"]
    for path, digest in parent["files"].items():
        if sha(path) != digest:
            raise ValueError("fresh parent bound bytes changed")
        inventory.append(Path(path))
    folder = out / "n26-continued-leaf-candidate-angles-v1"
    accepted = report_and_replay(
        folder, out / "n26-continued-leaf-candidate-angles-published-replay-v1", inventory)
    angle = module_at("current_continued_leaf_checker", folder / "verify_continued_leaf_angles.py")
    for module, name in ((angle, "verify_continued_leaf_angles.py"),
                         (angle.current, "n26_current_leaf_angle_source.py"),
                         (angle.leaf, "verify_leaf_pinned_candidate_angles.py")):
        if sha(module.__file__) != accepted["files"][name]:
            raise ValueError("current continuation imported different sealed arithmetic")
        inventory.append(Path(module.__file__))
    source_folder = out / "n26-leaf-pinned-candidate-angles-v2"
    values = angle.current.input_gate(
        source_folder, out / "n26-correlated-candidate-angles-v1",
        out / "n26-sharp-constraint-candidate-angles-v2", out / "n26-continued-candidate-angles-v1",
        out / "n26-anchor-pinning-v3", out / "n26-positive-stress-v1",
        out / "n26-centered-local-barrier-v2", out / "n26-candidate-transport-control-v1",
        out / "n26-refined-anchor-pinning-v2", out / "n26-sharp-radius-angle-caps-v2")
    inventory.extend(values["inventory"])
    proposal = json.loads((folder / "PROPOSAL.json").read_text())
    angle.proposal_gate(values["source"], source_folder, proposal)
    nodes, result, pending, ledger, empty, local = angle.replay_and_close(
        values, proposal, stage.load_trig(folder)[0])
    sources = {"starting_partition": sha(source_folder / "VERIFIED.json"),
               "pinning_reference": sha(out / "n26-refined-anchor-pinning-v2/VERIFIED.json"),
               "sharp_caps": sha(out / "n26-sharp-radius-angle-caps-v2/VERIFIED.json"),
               "stress": sha(out / "n26-positive-stress-v1/VERIFIED.json"),
               "local": sha(out / "n26-centered-local-barrier-v2/VERIFIED.json"),
               "transport": sha(out / "n26-candidate-transport-control-v1/VERIFIED.json")}
    certificate = {"schema": "N26-continued-leaf-pinned-closed-angular-tree-v1",
                   "radius_scope": "same-root-Rstar", "spec": values["source"]["spec"],
                   "source_acceptance_sha256": sources, "nodes": nodes}
    expected = {"SPLIT": 1080, "FORCE": 215, "LOCAL": 13, "EMPTY": 0, "OPEN": 103,
                "SHARP_FORCE": 549, "SHARP_LOCAL": 0, "SHARP_EMPTY": 3,
                "SHARP_CORRELATED_FORCE": 93, "SHARP_HULL_LOCAL": 105}
    if (any(accepted[key] != value for key, value in result.items())
            or certificate != json.loads((folder / "CERTIFICATE.json").read_text())
            or pending != json.loads((folder / "PENDING-ANGLES.json").read_text())
            or ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())
            or result["counts"] != expected or accepted["new_strict_force_leaves"] != 473
            or accepted["new_paid_hull_local_leaves"] != 5 or accepted["new_complete_closed_splits"] != 504
            or empty != accepted["automatically_paid_sharp_empty_indices"]
            or local != accepted["automatically_paid_sharp_local_indices"]):
        raise ValueError("continued partition, new force/hull payments or pending cells differ")
    below_U = sum(F(row["required_radius_lower"]) <= stage.U for row in ledger
                  if row["kind"] in ("FORCE", "SHARP_FORCE", "SHARP_CORRELATED_FORCE"))
    folder = out / "n26-force-stage-v11"
    stage_report, files = bound_bundle(folder)
    inventory.extend(files)
    published = out / "n26-force-stage-published-replay-v11.json"
    if json.loads(published.read_text()) != stage_report:
        raise ValueError("eleventh-stage published replay differs")
    inventory.append(published)
    _, incoming, old, multi, native, trace = stage.input_gate(folder, out / "n26-multislope-area-lower-v1")
    if incoming != json.loads((out / "n26-force-stage-v10/FRONTIER.json").read_text()):
        raise ValueError("eleventh-stage source frontier changed")
    frontier, stage_ledger, margins = stage.replay_trace(
        folder, incoming, old, multi, native, trace, stage.load_trig(folder)[0])
    inventory.extend(folder / name for name in native["files"])
    if (frontier != json.loads((folder / "FRONTIER.json").read_text())
            or stage_ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())
            or frontier["families"] != stage_report["families"]):
        raise ValueError("eleventh-stage actual frontier or lower ledger differs")
    candidate = values["data"][3]["prefix"]
    owners = [row for row in frontier["pending_states"] if row["B"] == 16
              and candidate[:len(row["prefix"])] == row["prefix"]]
    if (len(owners) != 1 or owners[0]["prefix"] != candidate
            or candidate not in trace["terminal_pending_prefixes"]["16"]):
        raise ValueError("known full candidate terminal lost or duplicated")
    catalog_folder = out / "n26-selected-terminal-catalog-v2"
    catalog, files = bound_bundle(catalog_folder)
    inventory.extend(files)
    catalog_published = out / "n26-selected-terminal-catalog-published-replay-v2.json"
    if json.loads(catalog_published.read_text()) != catalog:
        raise ValueError("selected terminal published replay differs")
    inventory.append(catalog_published)
    terminal = module_at("current_terminal_catalogue_checker", catalog_folder / "verify_terminal_catalog.py")
    manifest, actual_stage, accepted_stage, actual_frontier, actual_trace, candidate_data, runs = terminal.input_gate(catalog_folder)
    table = terminal.reconstruct(catalog_folder, actual_stage, accepted_stage, actual_frontier,
                                 actual_trace, candidate_data, runs)
    if (actual_stage != folder or accepted_stage != stage_report or actual_frontier != frontier
            or table != json.loads((catalog_folder / "CATALOG.json").read_text())
            or table["selected_terminal_paths"] != 10 or table["distinct_selected_canonical_types"] != 7
            or table["selected_candidate_type_paths"] != 1):
        raise ValueError("selected terminal scope, explicit maps or deduplication overclaimed")
    for path, digest in parent["files"].items():
        if sha(path) != digest:
            raise ValueError("prior full-chain bytes changed during latest audit")
    if (report_and_replay(out / "n26-continued-leaf-candidate-angles-v1",
                          out / "n26-continued-leaf-candidate-angles-published-replay-v1", []) != accepted
            or bound_bundle(folder)[0] != stage_report or bound_bundle(catalog_folder)[0] != catalog
            or any(sha(folder / name) != digest for name, digest in native["files"].items())):
        raise ValueError("new bound bytes changed during latest replay")
    report = {
        "schema": "N26-current-continued-leaf-terminal-and-eleventh-stage-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True, "all_prior_upper_scope_and_lower_chain_replayed": True,
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": parent["r_strict_interval"],
        "full_52_coordinate_nonnegative_equilibrium_replayed": True,
        "centered_unrestricted_local_barrier_and_all_pinning_sources_replayed": True,
        "local_neighbourhood_in_original_52_coordinates": "7/800000", "local_optimality_proved": True,
        "prior_all_proved_angular_nodes_and_closed_splits_preserved": True,
        "new_candidate_angle_strict_force_leaves": 473, "new_candidate_angle_hull_local_leaves": 5,
        "new_complete_closed_angle_splits": 504, "candidate_angle_tree_counts": result["counts"],
        "candidate_angle_unresolved_closed_boxes": len(pending),
        "candidate_force_bounds_above_Rstar_upper_but_at_most_U": below_U,
        "candidate_transport_global_lower_bound_proved": False,
        "candidate_angle_classification_global_combinatorial_nodes_removed": 0,
        "new_native_events_and_all_siblings_replayed": len(trace["events"]),
        "new_stage_event_counts": stage_report["event_counts"],
        "new_stage_whole_transport_subtrees_strictly_excluded": stage_report["strictly_excluded_whole_transport_subtrees"],
        "current_families": frontier["families"], "current_pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "current_unresolved_terminal_subtrees": 10, "selected_terminal_distinct_canonical_types": 7,
        "selected_candidate_type_paths": 1, "selected_terminal_native_codes_and_all_bijections_replayed": True,
        "terminal_catalogue_geometric_lower_bounds_added": 0,
        "known_feasible_candidate_survives_in_exactly_one_current_subtree": owners[0]["prefix"],
        "known_candidate_owner_is_complete_34_face_terminal": True,
        "all_old_forests_and_original_native_queues_preserved": True,
        "unrestricted_reduction_final_joint_acceptance": False, "full_catalog_complete": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "files": {str(path): sha(path) for path in inventory}}
    publish(args.output, report)
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
