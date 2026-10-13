"""Unaccepted bounded fresh-kernel forests for every actual remaining source OPEN."""

import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


def validate(proposal, kernels, older_hash, registry_hash, spec, box):
    if (proposal["verified"] is not False or proposal["source_acceptance_sha256"] != older_hash
            or proposal["source_registry_acceptance_sha256"] != registry_hash
            or proposal["spec"] != spec or proposal["source_closed_OPEN_box"] != box
            or proposal["source_OPEN_index"] != box["index"] or sha(kernels) != proposal["kernels_sha256"]):
        raise ValueError("saved residual discovery is not the same exact old/current source OPEN")


def main():
    parser = argparse.ArgumentParser()
    for key in ("older-source", "older-replay", "registry", "current-overlay", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=30)
    parser.add_argument("--branch-depth", type=int, default=8)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    old, _ = bound(args.older_source)
    current, _ = bound(args.current_overlay)
    base, _ = bound(args.registry)
    older_hash, registry_hash = sha(args.older_source / "VERIFIED.json"), sha(args.registry / "VERIFIED.json")
    if (read(args.older_replay) != old or old["source_acceptance_sha256"] != registry_hash
            or old["radius_scope"] != current["radius_scope"]
            or old["r_strict_interval"] != current["r_strict_interval"]
            or old["r_strict_interval"] != base["r_strict_interval"]):
        raise ValueError("remaining residual discovery changed actual old/current source or root")
    older_pending = {row["group_index"]: row for row in read(args.older_source / "PENDING-TYPES.json")}
    targets = read(args.current_overlay / "PENDING-TYPES.json")
    records = []
    for group in targets:
        index, spec = group["group_index"], group["spec"]
        for box in group["closed_OPEN_boxes"]:
            before = next(item for item in older_pending[index]["closed_OPEN_boxes"] if item["index"] == box["index"])
            if older_pending[index]["spec"] != spec or before != box:
                raise ValueError("remaining source OPEN changed after sibling payments")
            stem = f"n26-other-residual-g{index}-p{box['index']}-hybrid"
            proposal_path = Path(__file__).with_name(stem + "-proposal-v1.json")
            kernels_path = Path(__file__).with_name(stem + "-kernels-v1.json")
            if index == 26 and box["index"] == 99:
                proposal_path = Path(__file__).with_name("n26-type26-residual99-hybrid-proposal-v1.json")
                kernels_path = Path(__file__).with_name("n26-type26-residual99-hybrid-kernels-v1.json")
            if proposal_path.exists() != kernels_path.exists():
                raise ValueError("partial saved residual artifacts retained; inspect before resuming")
            if not proposal_path.exists():
                print(json.dumps({"verified": False, "starting_group": index,
                                  "source_OPEN_index": box["index"]}), flush=True)
                subprocess.run([
                    sys.executable, str(Path(__file__).with_name("propose_hybrid_quadratic_residual.py")),
                    "--source", str(args.older_source), "--source-replay", str(args.older_replay),
                    "--registry", str(args.registry), "--group", str(index),
                    "--source-OPEN", str(box["index"]), "--checks", str(args.checks),
                    "--branch-depth", str(args.branch_depth), "--output", str(proposal_path),
                    "--kernels-output", str(kernels_path)], check=True)
            proposal = read(proposal_path)
            validate(proposal, kernels_path, older_hash, registry_hash, spec, box)
            counts = dict(Counter(row["kind"] for row in proposal["nodes"]))
            record = {"group_index": index, "source_OPEN_index": box["index"],
                      "proposal": linux(proposal_path), "proposal_sha256": sha(proposal_path),
                      "kernels": linux(kernels_path), "kernels_sha256": sha(kernels_path),
                      "discovery_nodes": len(proposal["nodes"]), "discovery_counts": counts,
                      "discovery_proposed_closed": counts.get("OPEN", 0) == 0}
            records.append(record)
            print(json.dumps({"verified": False, **record}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-actual-remaining-OPEN-hybrid-batch-index-v1",
        "verified": False, "radius_scope": current["radius_scope"],
        "current_source_acceptance_sha256": sha(args.current_overlay / "VERIFIED.json"),
        "older_discovery_acceptance_sha256": older_hash, "registry_acceptance_sha256": registry_hash,
        "records": records, "global_optimality_proved": False,
        "all_sibling_proofs_unchanged_and_unvisited_closed_halves_retained": True,
        "independent_new_kernels_full_hybrid_coverage_and_current_lineage_acceptance_still_required": True,
    }, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "source_roots": len(records),
                      "proposed_closed_roots": sum(row["discovery_proposed_closed"] for row in records)}), flush=True)


if __name__ == "__main__":
    main()
