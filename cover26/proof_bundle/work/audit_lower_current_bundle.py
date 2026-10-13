"""Current upper/scope/catalog/strict-area-ledger content and arithmetic audit."""

import argparse
from functools import lru_cache
import importlib.util
import json
from pathlib import Path

from audit_prefix_partition import WORK, publish
from audit_area_prefix_envelopes import completion_degree_bounds, degree_budget_dp
from new_upper_scope import gate, load_arcs, local_path, sha
from run_new_scope_batch import audit, report_values


def module_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def bound_report(folder, name="VERIFIED.json"):
    path = folder / name
    data = json.loads(path.read_text(encoding="utf-8"))
    files = [path]
    for key, digest in data["files"].items():
        p = folder / key
        if sha(p) != digest:
            raise ValueError("changed published evidence: " + str(p))
        files.append(p)
    return data, files


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    out = WORK.parent / "outputs"
    inventory = [Path(__file__), out / "n26-STATUS.md",
                 out / "n26-unrestricted-interface-review-v2.md",
                 out / "n26-lower-progress-20261009.md"]
    root_folder = out / "n26-same-root-cover-v2"
    root_report, files = bound_report(root_folder)
    inventory.extend(files)
    checker = module_at("current_root_cover", root_folder / "verify_same_root_cover.py")
    if sha(checker.root.__file__) != root_report["files"]["verify_contact_root.py"]:
        raise ValueError("root verifier differs from bound source")
    system = json.loads((root_folder / "SYSTEM.json").read_text())
    root_cert = json.loads((root_folder / "ROOT-CERTIFICATE.json").read_text())
    if root_cert["system_sha256"] != sha(root_folder / "SYSTEM.json"):
        raise ValueError("root system not bound")
    root_result = checker.root.verify(system, root_cert, checker.F(1, 10**80))
    geometry = checker.geometry_check(system, root_cert)
    if root_result != root_report["root"] or geometry != root_report["geometry"]:
        raise ValueError("root/continuous cover differs from exact replay")
    print("Current same-root continuous covering replay passed.", flush=True)
    upper_path = out / "n26-rational-upper-v1/VERIFIED.json"
    upper = json.loads(upper_path.read_text())
    for key, digest in upper["files"].items():
        if sha(key) != digest:
            raise ValueError("changed rational upper evidence")
    scope = out / "n26-new-scope-v1"
    constants = json.loads((scope / "CONSTANTS.json").read_text())
    scope_result = gate(constants, upper, load_arcs())
    if not checker.F(root_result["r_strict_interval"][1]) < checker.F(constants["radius_upper"]):
        raise ValueError("scope threshold below root")
    inventory.extend((upper_path, scope / "CONSTANTS.json", scope / "DEPENDENCIES.json",
                      scope / "VERIFIED.json"))
    lower_folder = out / "n26-degree-area-lower-v1"
    lower_report, files = bound_report(lower_folder)
    inventory.extend(files)
    replay_path = out / "n26-degree-area-lower-published-replay-v1.json"
    replay = json.loads(replay_path.read_text())
    if replay != lower_report or not lower_report["verified"]:
        raise ValueError("published area replay differs")
    inventory.append(replay_path)
    lower = module_at("current_area_checker", lower_folder / "verify_degree_area.py")
    cert = json.loads((lower_folder / "CERTIFICATE.json").read_text())
    lower.parameter_gate(cert)
    arcs, _ = lower.load_trig(lower_folder)
    maxima, interior, _, _ = lower.derive_tables(cert, arcs, progress=True)
    lower.table_claim_gate(cert, maxima, interior)
    graphs, _ = lower.source_gate(lower_folder, cert)
    profiles, graph_rows, counts = lower.ledger_for(graphs, cert)
    if profiles != json.loads((lower_folder / "PROFILE-LEDGER.json").read_text()):
        raise ValueError("profile ledger changed")
    if graph_rows != json.loads((lower_folder / "GRAPH-LEDGER.json").read_text()):
        raise ValueError("graph ledger changed")
    if any(lower_report[key] != value for key, value in counts.items()):
        raise ValueError("lower report overclaims exact ledger")
    source = json.loads((lower_folder / "SOURCE.json").read_text())
    for path, digest in source["original_files"].items():
        if sha(path) != digest:
            raise ValueError("source/progress provenance changed")
        inventory.append(local_path(path))
    prefix_path = out / "n26-area-prefix-envelopes-v1.json"
    prefix_report = json.loads(prefix_path.read_text())
    for path, digest in prefix_report["files"].items():
        if sha(path) != digest:
            raise ValueError("prefix envelope dependency changed")
    envelope_rows = {(r["B"], tuple(r["prefix"])): r for r in prefix_report["subtree_envelopes"]}
    boundary_c = tuple(cert["boundary_intercept_upper_integers"])
    interior_c = tuple(cert["interior_area_upper_integers"])

    @lru_cache(None)
    def envelope(b, key):
        bd, inside = key
        rows = [(lo, hi, boundary_c) for lo, hi in bd]
        rows += [(lo, hi, interior_c) for lo, hi in inside]
        value = degree_budget_dp(rows, 150 - 2 * b)
        return None if value is None else value + int(lower.SLOPE * lower.COEFFICIENT_SCALE)

    families, rechecked_prefixes = [], set()
    for b in (14, 15, 16, 17):
        progress_path = out / f"n26-new-B{b}-progress-v1.json"
        progress = json.loads(progress_path.read_text())
        checkpoint_path = local_path(progress["latest_checkpoint"])
        if sha(checkpoint_path) != progress["checkpoint_sha256"]:
            raise ValueError("changed fresh-scope checkpoint")
        manifest = json.loads(checkpoint_path.read_text())
        result = audit(manifest)
        values = report_values(result)
        if any(progress[key] != value for key, value in values.items()):
            raise ValueError("queue progress overclaim")
        for prefix, state in result["pending"].items():
            row = envelope_rows[b, prefix]
            bounds = completion_degree_bounds(26, b, state)
            value = None if bounds is None else envelope(
                b, (tuple(sorted(bounds[:b])), tuple(sorted(bounds[b:]))))
            if (row["degree_bounds"] != (None if bounds is None else [list(v) for v in bounds])
                    or row["area_dual_upper_scaled_integer"] != value
                    or row["degree_completion_domain_empty"] != (value is None)
                    or row["strictly_excluded_as_cover_transport_subtree"] != (value is not None and value < 0)):
                raise ValueError("prefix area DP overclaim")
            rechecked_prefixes.add((b, prefix))
        families.append({"B": b, **values})
        inventory.extend((progress_path, checkpoint_path))
    if rechecked_prefixes != set(envelope_rows):
        raise ValueError("prefix envelope scope lost/duplicated")
    inventory.append(prefix_path)
    report = {
        "schema": "N26-current-upper-catalog-partial-lower-bundle-audit-v1",
        "current_bound_bytes_rechecked": True,
        "same_root_entire_disk_cover_replayed": True,
        "r_strict_interval": root_result["r_strict_interval"],
        "new_scope_exact_arithmetic_replayed": True,
        "external_published_n8_theorem_still_explicit": True,
        "strict_n8_core_gap": scope_result["strict_n8_core_gap"],
        "area_lower_coefficients_and_all_graph_ledgers_replayed": True,
        "selected_graphs": counts["selected_graphs"],
        "strictly_excluded_cover_transport_types": counts["strictly_excluded_graphs"],
        "selected_unresolved_graphs": counts["still_unresolved_graphs"],
        "area_exclusion_is_not_all_weak_rod_realization_exclusion": True,
        "four_family_checkpoints_replayed": families,
        "pending_subtree_area_envelopes_replayed": len(rechecked_prefixes),
        "pending_subtrees_deleted_by_area": 0,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {str(path): sha(path) for path in inventory}}
    publish(args.output, report)
    print(json.dumps({k: v for k, v in report.items() if k != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
