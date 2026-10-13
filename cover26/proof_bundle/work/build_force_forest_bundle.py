"""Publish proposed forest inputs; no accepting flag is written by this builder."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import WORK
from new_upper_scope import sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    out = WORK.parent / "outputs"
    frontier = out / "n26-current-cover-transport-frontier-v1.json"
    source_acceptance = out / "n26-multislope-current-bundle-audit-v1.json"
    area_folder = out / "n26-multislope-area-lower-v1"
    area_report = json.loads((area_folder / "VERIFIED.json").read_text())
    proposal = json.loads(args.proposal.read_text())
    if (proposal["source_frontier_sha256"] != sha(frontier)
            or proposal["area_acceptance_sha256"] != sha(area_folder / "VERIFIED.json")):
        raise ValueError("proposal source changed")
    for name, digest in area_report["files"].items():
        if sha(area_folder / name) != digest:
            raise ValueError("changed accepted area input")
    args.output.mkdir(parents=True)
    events = []
    for row in proposal["events"]:
        event = {"B": row["B"], "prefix": row["prefix"], "kind": row["kind"]}
        if row["kind"] == "force":
            event["cert"] = row["force_certificate_proposal"]
        elif row["kind"] == "area":
            event["cert"] = row["area_case_proposal"]
        elif row["kind"] == "split":
            event["all_child_count"] = row["all_child_count"]
        events.append(event)
    trace = {
        "schema": "N26-area-force-forest-trace-v1", "N": 26,
        "radius_threshold": proposal["radius_threshold"], "events": events,
        "pending_prefixes": proposal["pending_prefixes"],
        "terminal_pending_prefixes": proposal["terminal_pending_prefixes"],
        "full_catalog_complete": False, "global_optimality_proved": False}
    (args.output / "TRACE.json").write_text(json.dumps(trace, separators=(",", ":")) + "\n", encoding="utf-8")
    copies = [
        (frontier, "SOURCE-FRONTIER.json"), (source_acceptance, "SOURCE-ACCEPTANCE.json"),
        (WORK / "n26_force.py", "n26_force.py"),
        (WORK / "verify_force_forest.py", "verify_force_forest.py"),
        (WORK / "audit_force_forest_native.py", "audit_force_forest_native.py"),
        (WORK / "audit_prefix_origin.py", "audit_prefix_origin.py"),
        (WORK / "audit_prefix_partition.py", "audit_prefix_partition.py"),
        (out / "n26-partial-area-closures-v1/verify_partial_area_closures.py",
         "verify_partial_area_closures.py"),
    ]
    copies += [
        (area_folder / "verify_multislope_area.py", "verify_multislope_area.py"),
        (area_folder / "verify_degree_area.py", "verify_degree_area.py"),
        (area_folder / "exact_arcs.py", "exact_arcs.py"),
        (WORK / "prefix-origin-v1/peel_prefix_origin.cpp", "peel_prefix_origin.cpp"),
        (WORK / "prefix-origin-v1/peel_prefix_origin.linux", "peel_prefix_origin.linux"),
        (WORK / "n26-force-forest-proof.md", "PROOF.md")]
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest = {
        "schema": "N26-force-forest-input-bindings-v1",
        "source_frontier_original_key": str(frontier),
        "source_frontier_sha256": sha(frontier), "source_acceptance_sha256": sha(source_acceptance),
        "area_acceptance_sha256": sha(area_folder / "VERIFIED.json"),
        "kernel_source_sha256": sha(WORK / "prefix-origin-v1/peel_prefix_origin.cpp"),
        "kernel_binary_sha256": sha(WORK / "prefix-origin-v1/peel_prefix_origin.linux"),
        "trace_sha256": sha(args.output / "TRACE.json"),
        "copied_files": {name: sha(args.output / name) for original, name in copies},
        "builder_source_sha256": sha(__file__),
        "verified": False, "global_optimality_proved": False}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False, "events": len(events)}), flush=True)


if __name__ == "__main__":
    main()
