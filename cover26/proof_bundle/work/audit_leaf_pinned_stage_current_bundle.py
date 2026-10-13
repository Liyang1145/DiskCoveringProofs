"""Current complete chain through 100 leaf hulls and global stage v10."""

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
    parent_names = {"parent-output": "sharp-constraint", "continued-parent-output": "continued",
                    "centered-parent-output": "centered", "sharp-parent-output": "direct",
                    "pin-parent-output": "pin", "local-parent-output": "local", "angle-parent-output": "angle"}
    parent = args.parent_prefix.with_name(args.parent_prefix.name + "-correlated.json")
    parents = {flag: args.parent_prefix.with_name(args.parent_prefix.name + "-" + label + ".json")
               for flag, label in parent_names.items()}
    if any(path.exists() for path in (args.output, parent, *parents.values())):
        raise FileExistsError("fresh leaf-pinning full-chain audit paths required")
    out = WORK.parent / "outputs"
    parent_script = WORK / "audit_correlated_stage_current_bundle.py"
    command = [sys.executable, str(parent_script), "--output", str(parent)]
    for flag, path in parents.items():
        command.extend(("--" + flag, str(path)))
    run = subprocess.run(command, check=False)
    if run.returncode:
        raise ValueError("prior complete correlated and ninth-stage chain failed current replay")
    old = json.loads(parent.read_text())
    if (not old["current_bound_bytes_rechecked"]
            or old["candidate_angle_unresolved_closed_boxes"] != 177
            or old["current_pending_cover_transport_subtrees"] != 2868):
        raise ValueError("ninth-stage and correlated source obligations were not actually replayed")
    inventory = [Path(__file__), parent_script, parent, *parents.values(),
                 out / "n26-STATUS.md", out / "n26-leaf-pinning-and-stage-progress-20261010.md"]
    for text, digest in old["files"].items():
        if sha(text) != digest:
            raise ValueError("fresh prior full-chain bound bytes changed")
        inventory.append(Path(text))
    folder = out / "n26-leaf-pinned-candidate-angles-v2"
    accepted = report_and_replay(
        folder, out / "n26-leaf-pinned-candidate-angles-published-replay-v2", inventory)
    leaf = module_at("current_leaf_specific_root_hull_checker", folder / "verify_leaf_pinned_candidate_angles.py")
    for module, name in ((leaf, "verify_leaf_pinned_candidate_angles.py"),
                         (leaf.previous, "verify_correlated_candidate_angles.py"),
                         (leaf.refined, "verify_refined_anchor_pinning.py")):
        if sha(module.__file__) != accepted["files"][name]:
            raise ValueError("current leaf pinning imported changed accepted arithmetic")
        inventory.append(Path(module.__file__))
    source_folder = out / "n26-correlated-candidate-angles-v1"
    source, source_report, radius, cells, matrix, cap, reference, data, incoming_angles, inputs = leaf.source_gate(
        source_folder, out / "n26-sharp-constraint-candidate-angles-v2",
        out / "n26-continued-candidate-angles-v1", out / "n26-anchor-pinning-v3",
        out / "n26-positive-stress-v1", out / "n26-centered-local-barrier-v2",
        out / "n26-candidate-transport-control-v1", out / "n26-refined-anchor-pinning-v2",
        out / "n26-sharp-radius-angle-caps-v2")
    inventory.extend(inputs)
    discovery = json.loads((folder / "DISCOVERY.json").read_text())
    nodes = leaf.build_nodes(source, source_folder, out / "n26-refined-anchor-pinning-v2", discovery)
    result, pending, ledger = leaf.replay(source["spec"], radius, cells, matrix, cap, reference, data,
                                          nodes, stage.load_trig(folder)[0], progress=True)
    sources = {"starting_partition": sha(source_folder / "VERIFIED.json"),
               "pinning_reference": sha(out / "n26-refined-anchor-pinning-v2/VERIFIED.json"),
               "sharp_caps": sha(out / "n26-sharp-radius-angle-caps-v2/VERIFIED.json"),
               "stress": sha(out / "n26-positive-stress-v1/VERIFIED.json"),
               "local": sha(out / "n26-centered-local-barrier-v2/VERIFIED.json"),
               "transport": sha(out / "n26-candidate-transport-control-v1/VERIFIED.json")}
    certificate = {"schema": "N26-leaf-specific-root-hull-pinned-angular-tree-v1",
                   "radius_scope": "same-root-Rstar", "spec": source["spec"],
                   "source_acceptance_sha256": sources, "nodes": nodes}
    expected = {"SPLIT": 576, "FORCE": 215, "LOCAL": 13, "EMPTY": 0, "OPEN": 77,
                "SHARP_FORCE": 76, "SHARP_LOCAL": 0, "SHARP_EMPTY": 3,
                "SHARP_CORRELATED_FORCE": 93, "SHARP_HULL_LOCAL": 100}
    if (any(accepted[key] != value for key, value in result.items())
            or certificate != json.loads((folder / "CERTIFICATE.json").read_text())
            or pending != json.loads((folder / "PENDING-ANGLES.json").read_text())
            or ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())
            or reference != json.loads((folder / "REFERENCE-PINNING.json").read_text())
            or result["counts"] != expected or len(incoming_angles) - len(pending) != 100
            or discovery["proposed_paid_LOCAL_indices"] != accepted["new_paid_source_OPEN_indices"]
            or accepted["unchanged_original_coordinate_local_allowance"] != "7/800000"):
        raise ValueError("leaf hulls, root geometry, error bounds, old payments or pending boxes differ")
    tiny = [tuple(map(F, row)) for row in cap["known_candidate_tiny_angle_cells"]]
    retained = any(row["kind"] in ("LOCAL", "SHARP_LOCAL") and all(
        F(lo) <= a <= b <= F(hi) for lo, hi, (a, b) in zip(
            row.get("sharp_lower", row["lower"]), row.get("sharp_upper", row["upper"]), tiny))
        for row in ledger if row["kind"] in ("LOCAL", "SHARP_LOCAL"))
    if not retained or not accepted["known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf"]:
        raise ValueError("exact candidate root lost from old paid local positive control")
    for row in ledger:
        if row["kind"] == leaf.HULL_LOCAL:
            proof = row["leaf_specific_nonlocal_pinning"]
            if (F(proof["maximum_center_to_exact_rotated_root_euclidean_error_upper"]) >= F(7, 800000)
                    or not proof["no_prior_center_or_internal_witness_neighbourhood_hypothesis"]
                    or proof["closed_anchor_angle_cells"] != leaf.hull_for(row, tiny)):
                raise ValueError("leaf-specific local scope or entire hull inclusion overclaimed")
    folder = out / "n26-force-stage-v10"
    accepted_stage, files = bound_bundle(folder)
    inventory.extend(files)
    published = out / "n26-force-stage-published-replay-v10.json"
    if json.loads(published.read_text()) != accepted_stage:
        raise ValueError("tenth-stage published replay differs")
    inventory.append(published)
    _, incoming, area_old, multi, native, trace = stage.input_gate(folder, out / "n26-multislope-area-lower-v1")
    if incoming != json.loads((out / "n26-force-stage-v9/FRONTIER.json").read_text()):
        raise ValueError("tenth-stage source changed")
    frontier, stage_ledger, margins = stage.replay_trace(
        folder, incoming, area_old, multi, native, trace, stage.load_trig(folder)[0])
    inventory.extend(folder / name for name in native["files"])
    if (frontier != json.loads((folder / "FRONTIER.json").read_text())
            or stage_ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("tenth-stage pending siblings or lower ledger changed")
    counts = {kind: sum(row[kind] for row in frontier["families"]) for kind in stage.KINDS}
    if (counts != accepted_stage["event_counts"] or frontier["families"] != accepted_stage["families"]
            or len(frontier["pending_states"]) != accepted_stage["pending_cover_transport_subtrees"]):
        raise ValueError("tenth-stage event or family counts overclaimed")
    candidate = data[3]["prefix"]
    owners = [row for row in frontier["pending_states"] if row["B"] == 16
              and candidate[:len(row["prefix"])] == row["prefix"]]
    if (len(owners) != 1 or owners[0]["prefix"] != candidate
            or owners[0]["next"] != 26 or owners[0]["faces"] != data[3]["states"][-1]["faces"]
            or candidate not in trace["terminal_pending_prefixes"]["16"]):
        raise ValueError("known candidate not uniquely retained on its complete terminal transport")
    terminal_prefixes = [(b, p) for b in stage.FAMILIES for p in trace["terminal_pending_prefixes"][str(b)]]
    if len(terminal_prefixes) != counts["terminal"]:
        raise ValueError("unresolved complete graphs disappeared from terminal list")
    if any(not any(row["B"] == b and row["prefix"] == p for row in frontier["pending_states"])
           for b, p in terminal_prefixes):
        raise ValueError("unresolved terminal graph not present in actual current frontier")
    for text, digest in old["files"].items():
        if sha(text) != digest:
            raise ValueError("prior bound bytes changed during latest full-chain audit")
    if (report_and_replay(
            out / "n26-leaf-pinned-candidate-angles-v2",
            out / "n26-leaf-pinned-candidate-angles-published-replay-v2", []) != accepted
            or bound_bundle(folder)[0] != accepted_stage
            or json.loads(published.read_text()) != accepted_stage
            or any(sha(folder / name) != digest for name, digest in native["files"].items())):
        raise ValueError("new accepted bundle or native bound bytes changed during latest audit")
    current = {
        "schema": "N26-current-leaf-specific-pinning-and-tenth-stage-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True, "all_prior_upper_scope_and_lower_chain_replayed": True,
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": old["r_strict_interval"],
        "full_52_coordinate_nonnegative_equilibrium_replayed": True,
        "centered_entire_51_coordinate_Hessian_and_contact_stability_replayed": True,
        "local_neighbourhood_in_original_52_coordinates": "7/800000", "local_optimality_proved": True,
        "sharp_necessary_constraints_and_correlated_force_replayed": True,
        "all_100_actual_closed_leaf_root_hulls_and_energy_errors_reconstructed": True,
        "no_initial_center_or_witness_neighbourhood_assumption": True,
        "new_candidate_angle_SHARP_HULL_LOCAL_leaves": 100,
        "leaf_specific_pinning_maximum_center_error_upper": result["leaf_specific_pinning_maximum_center_error_upper"],
        "leaf_specific_pinning_minimum_strict_entry_margin": result["leaf_specific_pinning_minimum_strict_entry_margin"],
        "prior_all_proved_angular_nodes_and_closed_splits_preserved": True,
        "candidate_angle_tree_counts": result["counts"], "candidate_angle_unresolved_closed_boxes": len(pending),
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": retained,
        "candidate_transport_global_lower_bound_proved": False,
        "candidate_angle_classification_global_combinatorial_nodes_removed": 0,
        "new_native_events_and_all_siblings_replayed": len(trace["events"]), "new_stage_event_counts": counts,
        "new_stage_whole_transport_subtrees_strictly_excluded": accepted_stage["strictly_excluded_whole_transport_subtrees"],
        "current_families": frontier["families"],
        "current_pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "current_unresolved_terminal_subtrees": len(terminal_prefixes),
        "all_unresolved_terminal_graphs_retained_in_current_frontier": True,
        "known_feasible_candidate_survives_in_exactly_one_current_subtree": owners[0]["prefix"],
        "known_candidate_owner_is_complete_34_face_terminal": True,
        "all_old_forests_and_original_native_queues_preserved": True,
        "unrestricted_reduction_final_joint_acceptance": False, "full_catalog_complete": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "files": {str(path): sha(path) for path in inventory}}
    publish(args.output, current)
    print(json.dumps({key: value for key, value in current.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
