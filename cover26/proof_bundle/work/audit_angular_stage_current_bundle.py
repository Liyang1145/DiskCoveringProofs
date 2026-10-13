"""Replay the full current chain, including ancestor angle trees and new stage."""

import argparse
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path

from audit_prefix_partition import WORK, publish
from build_transport_frontier import accepted, reconstruct
from new_upper_scope import gate, load_arcs, sha
import verify_force_forest as first
import verify_angular_closures as coarse
import verify_force_stage as stage
import verify_multislope_area as area


def module_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def same_report_replay(folder, filename, inventory):
    report, files = accepted(folder)
    replay_path = folder.parent / filename
    if json.loads(replay_path.read_text()) != report:
        raise ValueError("published report replay differs: " + filename)
    inventory.extend((*files, replay_path))
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    out = WORK.parent / "outputs"
    inventory = [Path(__file__), out / "n26-STATUS.md", out / "n26-angular-stage-progress-20261009.md",
                 WORK / "verify_force_stage.py", WORK / "verify_angular_closures.py",
                 WORK / "n26_force_angles.py"]
    root_folder = out / "n26-same-root-cover-v2"
    root_report, files = accepted(root_folder)
    inventory.extend(files)
    root = module_at("angular_stage_current_root", root_folder / "verify_same_root_cover.py")
    if sha(root.root.__file__) != root_report["files"]["verify_contact_root.py"]:
        raise ValueError("same-root acceptance code changed")
    system = json.loads((root_folder / "SYSTEM.json").read_text())
    cert = json.loads((root_folder / "ROOT-CERTIFICATE.json").read_text())
    if cert["system_sha256"] != sha(root_folder / "SYSTEM.json"):
        raise ValueError("same-root system not bound")
    upper_result = root.root.verify(system, cert, F(1, 10**80))
    if upper_result != root_report["root"] or root.geometry_check(system, cert) != root_report["geometry"]:
        raise ValueError("same-root continuous cover failed exact replay")
    print("Current same-root continuous upper replay passed.", flush=True)
    scope = out / "n26-new-scope-v1"
    constants = json.loads((scope / "CONSTANTS.json").read_text())
    rational_upper_path = out / "n26-rational-upper-v1/VERIFIED.json"
    rational_upper = json.loads(rational_upper_path.read_text())
    for path, digest in rational_upper["files"].items():
        if sha(path) != digest:
            raise ValueError("rational upper source changed")
    gate(constants, rational_upper, load_arcs())
    if not F(upper_result["r_strict_interval"][1]) < F(constants["radius_upper"]):
        raise ValueError("scope threshold does not contain sharp counterexamples")
    inventory.extend((rational_upper_path, scope / "CONSTANTS.json", scope / "DEPENDENCIES.json",
                      scope / "VERIFIED.json"))
    area_folder = out / "n26-multislope-area-lower-v1"
    area_report, files = accepted(area_folder)
    inventory.extend(files)
    old, _, _ = area.base_gate(area_folder)
    multi = json.loads((area_folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    area.parameter_gate(multi)
    arcs = area.base.load_trig(area_folder)[0]
    maxima = area.derive_tables(old, arcs, progress=True)
    area.table_claim_gate(multi, maxima)
    for index, d in enumerate(range(2, 26)):
        actual = area.base.U**2 * F(d, 2) * area.base.sin_iv(arcs, F(1, d))[1]
        if F(old["interior_area_upper_integers"][index], area.C) < actual:
            raise ValueError("interior area coefficients do not replay")
    original_frontier, files = reconstruct()
    inventory.extend(files)
    forest_folder = out / "n26-force-forest-v1"
    first_report = same_report_replay(forest_folder, "n26-force-forest-published-replay-v1.json", inventory)
    _, source, old, multi, native, trace = first.input_gate(forest_folder, area_folder)
    if {key: value for key, value in source.items() if key != "files"} != original_frontier:
        raise ValueError("initial force forest source differs from current reconstruction")
    first_frontier, forces, areas = first.replay_trace(forest_folder, source, old, multi, native, trace, arcs)
    if first_frontier != json.loads((forest_folder / "FRONTIER.json").read_text()):
        raise ValueError("first force frontier changed")
    if {"force_leaves": forces, "area_leaves": areas} != json.loads((forest_folder / "LOWER-LEDGER.json").read_text()):
        raise ValueError("first force ledger changed")
    coarse_folder = out / "n26-angular-coarse-closures-v1"
    coarse_report = same_report_replay(coarse_folder, "n26-angular-coarse-published-replay-v1.json", inventory)
    _, source, trace, native = coarse.load_inputs(coarse_folder)
    if source != first_frontier:
        raise ValueError("coarse ancestor source disagrees with previous exact stage")
    coarse_frontier, ledger = coarse.replay(coarse_folder, source, trace, native, arcs)
    if coarse_frontier != json.loads((coarse_folder / "FRONTIER.json").read_text()):
        raise ValueError("ancestor angular frontier changed")
    if ledger != json.loads((coarse_folder / "LOWER-LEDGER.json").read_text()):
        raise ValueError("ancestor angular ledger changed")
    stage_folder = out / "n26-force-stage-v2"
    stage_report = same_report_replay(stage_folder, "n26-force-stage-published-replay-v2.json", inventory)
    _, source, old, multi, native, trace = stage.input_gate(stage_folder, area_folder)
    if source != coarse_frontier:
        raise ValueError("new stage restarted from a different frontier")
    frontier, ledger, margins = stage.replay_trace(stage_folder, source, old, multi, native, trace, arcs)
    if frontier != json.loads((stage_folder / "FRONTIER.json").read_text()):
        raise ValueError("new force/angular frontier changed")
    if ledger != json.loads((stage_folder / "LOWER-LEDGER.json").read_text()):
        raise ValueError("new force/angular ledger changed")
    counts = {kind: sum(row[kind] for row in frontier["families"]) for kind in stage.KINDS}
    if (counts != stage_report["event_counts"] or frontier["families"] != stage_report["families"]
            or len(frontier["pending_states"]) != stage_report["pending_cover_transport_subtrees"]):
        raise ValueError("new stage progress overclaim")
    if stage.regular_ring_controls(arcs) != stage_report["feasible_regular_ring_regression_controls"]:
        raise ValueError("feasible ring regression failed")
    report = {
        "schema": "N26-current-angular-tree-successive-stage-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True,
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": upper_result["r_strict_interval"],
        "four_family_scope_exact_arithmetic_replayed": True,
        "external_published_n8_theorem_still_explicit": True,
        "multi_slope_entire_angle_gap_coefficients_replayed": True,
        "selected_catalog_graphs_strictly_excluded": area_report["strictly_excluded_graphs"],
        "first_force_stage_native_events_replayed": first_report["native_events_independently_replayed"],
        "coarse_complete_ancestor_angular_trees_replayed": coarse_report["whole_ancestor_subtrees_strictly_excluded"],
        "coarse_source_prefixes_strictly_covered": coarse_report["source_pending_prefixes_covered"],
        "new_stage_start_frontier_bound": len(source["pending_states"]),
        "new_native_events_and_all_siblings_replayed": len(trace["events"]),
        "new_stage_event_counts": counts,
        "new_stage_whole_transport_subtrees_strictly_excluded": stage_report["strictly_excluded_whole_transport_subtrees"],
        "all_angle_tree_incoming_domains_replayed": True,
        "current_families": frontier["families"],
        "current_pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "all_old_forests_and_original_native_queues_preserved": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "local_optimality_proved": False, "global_optimality_proved": False, "n27_started": False,
        "files": {str(path): sha(path) for path in inventory}}
    publish(args.output, report)
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
