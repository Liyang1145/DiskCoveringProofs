"""Current chain replay from the same-root cover to the new 542-state forest."""

import argparse
import importlib.util
import json
from pathlib import Path

from audit_prefix_partition import WORK, publish
from build_transport_frontier import accepted, reconstruct
from new_upper_scope import gate, load_arcs, sha
import verify_force_forest as force_forest
import verify_multislope_area as area


def module_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    out = WORK.parent / "outputs"
    files = [Path(__file__), out / "n26-STATUS.md", out / "n26-force-progress-20261009.md"]
    root_folder = out / "n26-same-root-cover-v2"
    root_report, inventory = accepted(root_folder)
    files.extend(inventory)
    root = module_at("force_current_cover_checker", root_folder / "verify_same_root_cover.py")
    if sha(root.root.__file__) != root_report["files"]["verify_contact_root.py"]:
        raise ValueError("same-root checker changed")
    system = json.loads((root_folder / "SYSTEM.json").read_text())
    certificate = json.loads((root_folder / "ROOT-CERTIFICATE.json").read_text())
    if certificate["system_sha256"] != sha(root_folder / "SYSTEM.json"):
        raise ValueError("root input not bound")
    result = root.root.verify(system, certificate, root.F(1, 10**80))
    if result != root_report["root"] or root.geometry_check(system, certificate) != root_report["geometry"]:
        raise ValueError("same-root covering failed current exact replay")
    print("Same-root entire-disk upper replay passed.", flush=True)
    upper_path = out / "n26-rational-upper-v1/VERIFIED.json"
    upper = json.loads(upper_path.read_text())
    for path, digest in upper["files"].items():
        if sha(path) != digest:
            raise ValueError("rational upper input changed")
    scope = out / "n26-new-scope-v1"
    constants = json.loads((scope / "CONSTANTS.json").read_text())
    gate(constants, upper, load_arcs())
    if not root.F(result["r_strict_interval"][1]) < root.F(constants["radius_upper"]):
        raise ValueError("upper/scope thresholds reversed")
    files.extend((upper_path, scope / "CONSTANTS.json", scope / "DEPENDENCIES.json", scope / "VERIFIED.json"))
    area_folder = out / "n26-multislope-area-lower-v1"
    area_report, inventory = accepted(area_folder)
    files.extend(inventory)
    old, _, _ = area.base_gate(area_folder)
    multi = json.loads((area_folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    arcs = area.base.load_trig(area_folder)[0]
    maxima = area.derive_tables(old, arcs, progress=True)
    area.table_claim_gate(multi, maxima)
    parent_frontier, inventory = reconstruct()
    files.extend(inventory)
    folder = out / "n26-force-forest-v1"
    report, inventory = accepted(folder)
    files.extend(inventory)
    replay_path = out / "n26-force-forest-published-replay-v1.json"
    if json.loads(replay_path.read_text()) != report:
        raise ValueError("published force forest replay differs")
    files.append(replay_path)
    manifest, source, old, multi, native, trace = force_forest.input_gate(folder, area_folder)
    if {k: v for k, v in source.items() if k != "files"} != parent_frontier:
        raise ValueError("force forest starting partition differs from complete current-chain reconstruction")
    partial_report = json.loads((out / "n26-partial-area-closures-v1/VERIFIED.json").read_text())
    if sha(folder / "verify_partial_area_closures.py") != partial_report["files"]["verify_partial_area_closures.py"]:
        raise ValueError("forest imports a different partial-area checker")
    frontier, forces, areas = force_forest.replay_trace(folder, source, old, multi, native, trace, arcs)
    if frontier != json.loads((folder / "FRONTIER.json").read_text()):
        raise ValueError("force forest frontier differs")
    if {"force_leaves": forces, "area_leaves": areas} != json.loads((folder / "LOWER-LEDGER.json").read_text()):
        raise ValueError("force/area lower ledger differs")
    if (len(forces) != report["force_subtrees_strictly_excluded"]
            or len(areas) != report["area_subtrees_strictly_excluded"]
            or len(frontier["pending_states"]) != report["pending_cover_transport_subtrees"]):
        raise ValueError("force progress report overclaims")
    if force_forest.regular_ring_controls(arcs) != report["feasible_regular_ring_regression_controls"]:
        raise ValueError("regular ring controls failed")
    new_report = {
        "schema": "N26-current-force-forest-full-chain-audit-v1",
        "current_bound_bytes_rechecked": True,
        "same_root_entire_disk_cover_replayed": True, "r_strict_interval": result["r_strict_interval"],
        "four_family_scope_exact_arithmetic_replayed": True,
        "external_published_n8_theorem_still_explicit": True,
        "multi_slope_continuous_coefficients_replayed": True,
        "selected_catalog_graphs_strictly_excluded": area_report["strictly_excluded_graphs"],
        "parent_transport_frontier_reconstructed": len(parent_frontier["pending_states"]),
        "native_events_and_all_sibling_transitions_replayed": len(trace["events"]),
        "new_force_subtrees_strictly_excluded": len(forces),
        "new_area_subtrees_strictly_excluded": len(areas),
        "new_empty_combinatorial_subtrees": sum(row["empty"] for row in frontier["families"]),
        "current_families": frontier["families"],
        "current_pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "original_native_queues_preserved": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "local_optimality_proved": False, "global_optimality_proved": False,
        "n27_started": False,
        "files": {str(path): sha(path) for path in files}}
    publish(args.output, new_report)
    print(json.dumps({key: value for key, value in new_report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
