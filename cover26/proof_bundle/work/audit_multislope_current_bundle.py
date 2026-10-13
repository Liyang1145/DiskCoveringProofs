"""Current content-bound replay of cover, multi-slope lower and prefix closures."""

import argparse
import importlib.util
import json
from pathlib import Path

from audit_prefix_partition import WORK, publish
from build_transport_frontier import accepted, reconstruct
from new_upper_scope import gate, load_arcs, local_path, sha
import verify_multislope_area as area


def load_module(name, path):
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
    inventory = [Path(__file__), WORK / "build_transport_frontier.py", out / "n26-STATUS.md",
                 out / "n26-multislope-progress-20261009.md",
                 out / "n26-unrestricted-interface-review-v2.md"]
    root_folder = out / "n26-same-root-cover-v2"
    root_report, files = accepted(root_folder)
    inventory.extend(files)
    checker = load_module("current_multislope_root_cover", root_folder / "verify_same_root_cover.py")
    if sha(checker.root.__file__) != root_report["files"]["verify_contact_root.py"]:
        raise ValueError("current root checker differs from frozen covering proof")
    system = json.loads((root_folder / "SYSTEM.json").read_text())
    root_cert = json.loads((root_folder / "ROOT-CERTIFICATE.json").read_text())
    if root_cert["system_sha256"] != sha(root_folder / "SYSTEM.json"):
        raise ValueError("root system not bound")
    root_result = checker.root.verify(system, root_cert, checker.F(1, 10**80))
    if (root_result != root_report["root"]
            or checker.geometry_check(system, root_cert) != root_report["geometry"]):
        raise ValueError("same-root full-disk cover failed current replay")
    print("Current same-root upper replay passed.", flush=True)
    upper_path = out / "n26-rational-upper-v1/VERIFIED.json"
    upper = json.loads(upper_path.read_text())
    for path, digest in upper["files"].items():
        if sha(path) != digest:
            raise ValueError("changed rational upper evidence")
    scope = out / "n26-new-scope-v1"
    constants = json.loads((scope / "CONSTANTS.json").read_text())
    gate(constants, upper, load_arcs())
    if not checker.F(root_result["r_strict_interval"][1]) < checker.F(constants["radius_upper"]):
        raise ValueError("sharper root not below enumeration threshold")
    inventory.extend((upper_path, scope / "CONSTANTS.json", scope / "DEPENDENCIES.json",
                      scope / "VERIFIED.json"))
    folder = out / "n26-multislope-area-lower-v1"
    lower_report, files = accepted(folder)
    inventory.extend(files)
    replay_path = out / "n26-multislope-area-published-replay-v1.json"
    if json.loads(replay_path.read_text()) != lower_report:
        raise ValueError("published multi-slope replay differs")
    inventory.append(replay_path)
    old, _, _ = area.base_gate(folder)
    cert = json.loads((folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    area.parameter_gate(cert)
    arcs, _ = area.base.load_trig(folder)
    maxima = area.derive_tables(old, arcs, progress=True)
    area.table_claim_gate(cert, maxima)
    for index, d in enumerate(range(2, 26)):
        actual = area.base.U**2 * checker.F(d, 2) * area.base.sin_iv(arcs, checker.F(1, d))[1]
        if checker.F(old["interior_area_upper_integers"][index], area.C) < actual:
            raise ValueError("interior upper bound does not replay")
    source = json.loads((folder / "SOURCE.json").read_text())
    for path, digest in source["original_files"].items():
        if sha(path) != digest:
            raise ValueError("changed original selected catalog provenance")
        inventory.append(local_path(path))
    partial_folder = out / "n26-partial-area-closures-v1"
    partial_report, files = accepted(partial_folder)
    inventory.extend(files)
    partial_replay_path = out / "n26-partial-area-published-replay-v1.json"
    if json.loads(partial_replay_path.read_text()) != partial_report:
        raise ValueError("published whole-subtree replay differs")
    inventory.append(partial_replay_path)
    frontier, files = reconstruct()
    inventory.extend(files)
    frontier_path = out / "n26-current-cover-transport-frontier-v1.json"
    bound_frontier = json.loads(frontier_path.read_text())
    for path, digest in bound_frontier["files"].items():
        if sha(path) != digest:
            raise ValueError("frontier input changed")
    if {k: v for k, v in bound_frontier.items() if k != "files"} != frontier:
        raise ValueError("current counterexample frontier differs from exhaustive reconstruction")
    inventory.append(frontier_path)
    report = {
        "schema": "N26-current-multislope-and-subtree-lower-bundle-audit-v1",
        "current_bound_bytes_rechecked": True,
        "same_root_entire_disk_cover_replayed": True,
        "r_strict_interval": root_result["r_strict_interval"],
        "four_family_scope_exact_arithmetic_replayed": True,
        "external_published_n8_theorem_still_explicit": True,
        "multi_slope_full_continuous_interval_tables_replayed": True,
        "all_selected_graph_rational_duals_replayed": True,
        "selected_graphs_strictly_excluded": lower_report["strictly_excluded_graphs"],
        "selected_graphs_unresolved": 0,
        "whole_subtree_duals_and_all_degree_completions_replayed": True,
        "whole_subtrees_strictly_excluded": partial_report["strictly_excluded_whole_transport_subtrees"],
        "active_cover_transport_families": frontier["families"],
        "active_cover_transport_frontier": frontier["active_cover_transport_subtrees_total"],
        "native_combinatorial_pending_preserved": frontier["native_pending_preserved_total"],
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "local_optimality_proved": False, "global_optimality_proved": False,
        "n27_started": False,
        "files": {str(path): sha(path) for path in inventory}}
    publish(args.output, report)
    print(json.dumps({k: v for k, v in report.items() if k != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
