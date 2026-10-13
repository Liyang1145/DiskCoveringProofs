"""Reconstruct the current counterexample-transport frontier without deleting logs."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import WORK, publish
from new_upper_scope import local_path, sha
from run_new_scope_batch import audit, report_values
import verify_multislope_area as area
import verify_partial_area_closures as partial


def accepted(folder):
    path = folder / "VERIFIED.json"
    report = json.loads(path.read_text())
    if not report["verified"] or report["global_optimality_proved"]:
        raise ValueError("wrong accepted evidence scope")
    files = [path]
    for name, digest in report["files"].items():
        target = folder / name
        if sha(target) != digest:
            raise ValueError("changed accepted transport evidence")
        files.append(target)
    return report, files


def reconstruct():
    out = WORK.parent / "outputs"
    area_folder = out / "n26-multislope-area-lower-v1"
    lower_report, files = accepted(area_folder)
    if not lower_report["all_selected_graphs_excluded"] or lower_report["still_unresolved_graphs"]:
        raise ValueError("selected completed catalogs still contain unresolved graphs")
    old, _, _ = area.base_gate(area_folder)
    multi = json.loads((area_folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    cases = json.loads((area_folder / "CASE-CERTIFICATES.json").read_text())
    graphs, _ = area.base.source_gate(area_folder, old)
    ledger, counts = area.graph_ledger(graphs, cases, multi, old)
    if ledger != json.loads((area_folder / "MULTISLOPE-GRAPH-LEDGER.json").read_text()):
        raise ValueError("current selected graph exclusions differ")
    if counts["still_unresolved_graphs"] or counts["selected_graphs"] != 13237:
        raise ValueError("selected source scope changed")
    partial_folder = out / "n26-partial-area-closures-v1"
    partial_report, part_files = accepted(partial_folder)
    files.extend(part_files)
    if partial_report["area_bundle_acceptance_sha256"] != sha(area_folder / "VERIFIED.json"):
        raise ValueError("partial subtree duals refer to another area bundle")
    cert = json.loads((partial_folder / "PARTIAL-CERTIFICATE.json").read_text())
    initial = json.loads((partial_folder / "INITIAL-FRONTIER.json").read_text())
    reference = partial.OriginReference(26, 14, "dfs", caps=area.CAPS, scale=area.D)
    pending14, excluded14, splits = partial.partition_for(cert, reference, initial)
    for case in cert["cases"]:
        if partial.partial_bound(case, excluded14[tuple(case["prefix"])], old, multi) >= 0:
            raise ValueError("nonnegative whole-subtree area bound")
    closure_prefixes = tuple(excluded14)
    families, states = [], []
    for b in (14, 15, 16, 17):
        progress_path = out / f"n26-new-B{b}-progress-v1.json"
        progress = json.loads(progress_path.read_text())
        checkpoint_path = local_path(progress["latest_checkpoint"])
        if sha(checkpoint_path) != progress["checkpoint_sha256"]:
            raise ValueError("changed native queue checkpoint")
        native = audit(json.loads(checkpoint_path.read_text()))
        values = report_values(native)
        if any(progress[key] != value for key, value in values.items()):
            raise ValueError("native queue overclaim")
        files.extend((progress_path, checkpoint_path))
        if b == 14:
            def covered(prefix):
                return any(prefix[:len(p)] == p for p in closure_prefixes)
            covered_pending = sum(covered(p) for p in native["pending"])
            covered_closed = sum(covered(p) for p in native["completed"])
            if covered_pending != 20 or covered_closed != 6:
                raise ValueError("coarse closure/native checkpoint relationship changed")
            active = pending14
        else:
            if native["union"]["orbits"]:
                raise ValueError("unbound newer completed graphs")
            covered_pending = covered_closed = 0
            active = {p: partial.OriginReference(26, b, "dfs", caps=area.CAPS, scale=area.D).resolve(p)
                      for p in native["pending"]}
        ref = partial.OriginReference(26, b, "dfs", caps=area.CAPS, scale=area.D)
        active = {p: ref.normalize(state) for p, state in active.items()}
        states.extend({"B": b, **ref.entry(p, state, ref.children(state))}
                      for p, state in sorted(active.items()))
        families.append({
            "B": b, "I": 26 - b,
            "native_pending_preserved": len(native["pending"]),
            "native_completed_subtrees": len(native["completed"]),
            "native_pending_wholly_covered_by_area_closure": covered_pending,
            "native_completed_wholly_covered_by_area_closure": covered_closed,
            "active_cover_transport_subtrees": len(active),
            "family_exhausted": False})
    result = {
        "schema": "N26-current-cover-transport-frontier-v1",
        "families": families, "pending_states": states,
        "selected_completed_catalog_graphs": counts["selected_graphs"],
        "selected_unresolved_catalog_graphs": 0,
        "native_pending_preserved_total": sum(r["native_pending_preserved"] for r in families),
        "active_cover_transport_subtrees_total": len(states),
        "B14_whole_area_excluded_prefixes": [list(p) for p in sorted(excluded14)],
        "B14_all_prefix_splits": splits,
        "original_native_checkpoints_unchanged": True,
        "complete_cover_transport_partition_reconstructed": True,
        "full_catalog_complete": False,
        "unrestricted_reduction_final_joint_acceptance": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False}
    return result, files


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    result, files = reconstruct()
    result["files"] = {str(path): sha(path) for path in [Path(__file__), *files]}
    publish(args.output, result)
    print(json.dumps({k: v for k, v in result.items() if k not in ("pending_states", "files")}, indent=2),
          flush=True)


if __name__ == "__main__":
    main()
