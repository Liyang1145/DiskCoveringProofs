"""Publish a subsequent force/angular stage with its accepted starting frontier."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import WORK
from new_upper_scope import local_path, sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    proposed = json.loads(args.proposal.read_text())
    source = local_path(proposed["source_frontier_original_path"].replace("\\", "/"))
    accepted_path = local_path(proposed["source_acceptance_original_path"].replace("\\", "/"))
    accepted = json.loads(accepted_path.read_text())
    if (not accepted["verified"]
            or accepted["files"][proposed["source_acceptance_key"]] != sha(source)
            or sha(source) != proposed["source_frontier_sha256"]
            or sha(accepted_path) != proposed["source_acceptance_sha256"]):
        raise ValueError("stage proposal has a changed accepted source")
    out = WORK.parent / "outputs"
    base_folder = out / "n26-force-forest-v1"
    area_folder = out / "n26-multislope-area-lower-v1"
    if sha(area_folder / "VERIFIED.json") != proposed["area_acceptance_sha256"]:
        raise ValueError("changed accepted area inputs")
    args.output.mkdir(parents=True)
    trace = {
        "schema": "N26-successive-force-angular-stage-trace-v1", "N": 26,
        "radius_threshold": proposed["radius_threshold"], "events": proposed["events"],
        "pending_prefixes": proposed["pending_prefixes"],
        "terminal_pending_prefixes": proposed["terminal_pending_prefixes"],
        "full_catalog_complete": False, "global_optimality_proved": False}
    (args.output / "TRACE.json").write_text(json.dumps(trace, separators=(",", ":")) + "\n", encoding="utf-8")
    copies = [
        (source, "SOURCE-FRONTIER.json"), (accepted_path, "SOURCE-ACCEPTANCE.json"),
        (base_folder / "n26_force.py", "n26_force.py"),
        (out / "n26-angular-coarse-closures-v1/n26_force_angles.py", "n26_force_angles.py"),
        (base_folder / "verify_degree_area.py", "verify_degree_area.py"),
        (base_folder / "verify_multislope_area.py", "verify_multislope_area.py"),
        (base_folder / "verify_partial_area_closures.py", "verify_partial_area_closures.py"),
        (base_folder / "verify_force_forest.py", "verify_force_forest.py"),
        (base_folder / "exact_arcs.py", "exact_arcs.py"),
        (base_folder / "audit_prefix_origin.py", "audit_prefix_origin.py"),
        (base_folder / "audit_prefix_partition.py", "audit_prefix_partition.py"),
        (base_folder / "peel_prefix_origin.cpp", "peel_prefix_origin.cpp"),
        (base_folder / "peel_prefix_origin.linux", "peel_prefix_origin.linux"),
        (base_folder / "audit_force_forest_native.py", "audit_force_forest_native.py"),
        (WORK / "verify_force_stage.py", "verify_force_stage.py"),
        (WORK / "n26-force-stage-proof.md", "PROOF.md")]
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest = {
        "schema": "N26-successive-force-stage-input-bindings-v1",
        "source_frontier_original_path": str(source),
        "source_acceptance_original_path": str(accepted_path),
        "source_acceptance_key": proposed["source_acceptance_key"],
        "source_frontier_sha256": sha(source), "source_acceptance_sha256": sha(accepted_path),
        "area_acceptance_sha256": sha(area_folder / "VERIFIED.json"),
        "kernel_source_sha256": sha(base_folder / "peel_prefix_origin.cpp"),
        "kernel_binary_sha256": sha(base_folder / "peel_prefix_origin.linux"),
        "trace_sha256": sha(args.output / "TRACE.json"),
        "copied_files": {name: sha(args.output / name) for original, name in copies},
        "builder_sha256": sha(__file__), "verified": False, "global_optimality_proved": False}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False, "new_events": len(trace["events"])}), flush=True)


if __name__ == "__main__":
    main()
