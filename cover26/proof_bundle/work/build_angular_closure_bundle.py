"""Publish proposed ancestor angular trees without altering the accepted forest."""

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
    folder = out / "n26-force-forest-v1"
    source = folder / "FRONTIER.json"
    source_acceptance = out / "n26-force-current-bundle-audit-v1.json"
    proposed = json.loads(args.proposal.read_text())
    if (proposed["source_frontier_sha256"] != sha(source)
            or proposed["source_acceptance_sha256"] != sha(source_acceptance)):
        raise ValueError("proposed ancestor tree has a changed source")
    if any(row["kind"] != "force_tree" for row in proposed["closures"]):
        raise ValueError("this evidence bundle contains angular-tree closures only")
    args.output.mkdir(parents=True)
    trace = {
        "schema": "N26-ancestor-angular-closure-trace-v1", "N": 26,
        "closures": [{"B": row["B"], "prefix": row["prefix"], "nodes": row["nodes"],
                      "source_active_descendants": row["source_active_descendants"]}
                     for row in proposed["closures"]],
        "pending_prefixes": proposed["pending_prefixes"],
        "full_catalog_complete": False, "global_optimality_proved": False}
    (args.output / "TRACE.json").write_text(json.dumps(trace, separators=(",", ":")) + "\n", encoding="utf-8")
    copies = [
        (source, "SOURCE-FRONTIER.json"), (folder / "VERIFIED.json", "SOURCE-FOREST-ACCEPTANCE.json"),
        (source_acceptance, "SOURCE-CHAIN-ACCEPTANCE.json"),
        (folder / "n26_force.py", "n26_force.py"),
        (folder / "verify_degree_area.py", "verify_degree_area.py"),
        (folder / "exact_arcs.py", "exact_arcs.py"),
        (folder / "audit_prefix_origin.py", "audit_prefix_origin.py"),
        (folder / "audit_prefix_partition.py", "audit_prefix_partition.py"),
        (folder / "peel_prefix_origin.cpp", "peel_prefix_origin.cpp"),
        (folder / "peel_prefix_origin.linux", "peel_prefix_origin.linux"),
        (WORK / "n26_force_angles.py", "n26_force_angles.py"),
        (WORK / "verify_angular_closures.py", "verify_angular_closures.py"),
        (WORK / "audit_angular_closures_native.py", "audit_angular_closures_native.py"),
        (WORK / "n26-angular-closure-proof.md", "PROOF.md")]
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest = {
        "schema": "N26-ancestor-angular-closure-input-bindings-v1",
        "source_frontier_original_key": str(source),
        "source_frontier_sha256": sha(source),
        "source_forest_acceptance_sha256": sha(folder / "VERIFIED.json"),
        "source_chain_acceptance_sha256": sha(source_acceptance),
        "trace_sha256": sha(args.output / "TRACE.json"),
        "copied_files": {name: sha(args.output / name) for original, name in copies},
        "builder_sha256": sha(__file__), "verified": False, "global_optimality_proved": False}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"built": True, "verified": False, "angular_subtree_closures": len(trace["closures"])}), flush=True)


if __name__ == "__main__":
    main()
