"""Derive a conditional-format acceptance from an exact force-stage replay.

The stage's original verify_force_stage acceptance is preserved as
VERIFIED-FORCE.json. This script reruns the unchanged conditional input gate
and replay, confirms the old frontier/ledger and force acceptance, then emits
only the missing conditional metadata needed by current-chain composition.
No new geometric payment is created.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import verify_conditional_force_stage as conditional
import verify_force_stage as force_stage


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--area-bundle", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    stage = args.stage.resolve()
    force_acceptance = conditional.read(stage / "VERIFIED-FORCE.json")
    if not force_acceptance["verified"] or force_acceptance["global_optimality_proved"]:
        raise ValueError("preserved force acceptance has wrong scope")
    values = conditional.input_gate(stage, args.area_bundle)
    manifest, source, old_acceptance, basis, old, multi, native, trace, inventory = values
    candidate = conditional.read(stage / "CANDIDATE-PATH.json")
    arcs = conditional.force.load_trig(stage)[0]
    frontier, ledger, margins = conditional.replay(
        stage, source, old, multi, native, trace, arcs,
        F(manifest["radius_upper"]), candidate)
    frozen_frontier = conditional.read(stage / "FRONTIER.json")
    frontier_core = {key: value for key, value in frontier.items()
                     if key in ("N", "families", "pending_states",
                                "older_forests_and_original_native_queues_preserved",
                                "full_catalog_complete", "global_optimality_proved")}
    frozen_core = {key: value for key, value in frozen_frontier.items()
                   if key in frontier_core}
    if frontier_core != frozen_core:
        raise ValueError("conditional replay differs from frozen frontier")
    if ledger != conditional.read(stage / "LOWER-LEDGER.json"):
        raise ValueError("conditional replay differs from frozen ledger")
    if force_acceptance["event_counts"] != {
        kind: sum(row[kind] for row in frontier["families"])
        for kind in force_stage.KINDS
    }:
        raise ValueError("force acceptance event counts do not match conditional replay")
    if force_acceptance["families"] != frontier["families"]:
        raise ValueError("force acceptance families do not match conditional replay")
    kinds = {kind: sum(row[kind] for row in frontier["families"])
             for kind in force_stage.KINDS}
    basis_acceptance = conditional.read(
        conditional.local_path(manifest["radius_basis"]) / "VERIFIED.json")
    report = {
        "schema": "N26-successive-radius-conditional-stage-compat-acceptance-v1",
        "verified": True,
        "radius_scope": conditional.SCOPE,
        "radius_upper": str(F(manifest["radius_upper"])),
        "r_strict_interval": basis_acceptance["r_strict_interval"],
        "screen_radius_threshold": manifest["screen_radius_threshold"],
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "radius_basis_acceptance_sha256": manifest["radius_basis_acceptance_sha256"],
        "source_conditional_pending_subtrees": len(source["pending_states"]),
        "native_events_independently_replayed": len(trace["events"]),
        "event_counts": kinds,
        "new_strict_radius_conditional_whole_transport_subtrees_excluded":
            kinds["force"] + kinds["force_tree"] + kinds["area"],
        "new_combinatorially_empty_subtrees": kinds["empty"],
        "complete_angle_tree_nodes": sum(row["nodes"] for row in
                                        conditional.read(stage / "LOWER-LEDGER.json")
                                        if row["kind"] == "force_tree"),
        "all_incoming_angle_boxes_covered": True,
        "minimum_strict_force_margin_above_conservative_U":
            str(min(margins)) if margins else None,
        "U_force_area_and_screen_bounds_used_only_as_sufficient_conditions_on_Rstar_source": True,
        "inherited_source_is_unconditional_at_U": False,
        "feasible_regular_ring_regression_controls":
            force_acceptance["feasible_regular_ring_regression_controls"],
        "families": frontier["families"],
        "pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "known_candidate_unique_complete_34_face_terminal": candidate["prefix"],
        "older_forests_and_original_native_queues_preserved": True,
        "angular_regression_control_from_current_stage": False,
        "angular_regression_positive_tree_nodes": 0,
        "angular_regression_control_new_geometric_payments": 0,
        "original_exact_semantic_replayer_sha256": conditional.sha(conditional.__file__),
        "unrestricted_reduction_final_joint_acceptance": False,
        "formal_machine_geometry_proof": False,
        "full_catalog_complete": False,
        "global_lower_bound_proved": False,
        "global_optimality_proved": False,
        "n27_started": False,
        "negative_controls_rejected": force_acceptance["negative_controls_rejected"],
        "files": {name: conditional.sha(stage / name)
                  for name in force_acceptance["files"]},
        "source_files": {conditional.combinatorics.linux(path): conditional.sha(path)
                         for path in inventory},
        "executed_checker_file": "verify_conditional_force_stage.py",
        "executed_checker_sha256": conditional.sha(conditional.__file__),
        "derived_from_force_acceptance_sha256":
            conditional.sha(stage / "VERIFIED-FORCE.json"),
        "conditional_replay_frontier_and_ledger_exactly_match_force_acceptance": True,
        "new_geometric_payments": 0,
    }
    if report["files"]["verify_conditional_force_stage.py"] != report["executed_checker_sha256"]:
        raise ValueError("stage does not bind the unchanged conditional replayer")
    target = args.report if args.report is not None else stage / "VERIFIED.json"
    if target.exists():
        raise FileExistsError(target)
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("files", "source_files")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
