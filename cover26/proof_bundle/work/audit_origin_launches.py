"""Fresh content and executable-identity check of the origin-conditioned queue."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import WORK, expect_rejection, publish, sha
from run_origin_prefix_batch import audit_origin_manifest


def executable_gate(record, expected_binary):
    if record["command"][:2] != ["/lib64/ld-linux-x86-64.so.2", str(expected_binary)]:
        raise ValueError("launch used an unexpected loader or executable")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--progress", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    progress = json.loads(args.progress.read_text(encoding="utf-8"))
    checkpoint = Path(progress["latest_checkpoint"])
    if sha(checkpoint) != progress["checkpoint_sha256"]:
        raise ValueError("checkpoint changed")
    manifest = json.loads(checkpoint.read_text(encoding="utf-8"))
    result = audit_origin_manifest(manifest)
    pairs = {
        "completed_subtrees": len(result["completed"]),
        "pending_subtrees": len(result["pending"]),
        "reused_empty_subtrees": result["reused_empty"],
        "newly_completed_subtrees": result["native_completed"],
        "closed_rooted_graphs": result["native_rooted"],
        "closed_distinct_orbits": result["native_orbits"],
        "limited_tasks_split": result["limited"],
        "forced_nodes_refined": result["forced_refinements"],
    }
    if any(progress[field] != value for field, value in pairs.items()):
        raise ValueError("progress disagrees with reconstructed partition")
    old_binary = WORK / "peel_prefix_v1.linux"
    new_binary = WORK / "prefix-origin-v1/peel_prefix_origin.linux"
    for binary in (old_binary, new_binary):
        if sha(binary) != manifest["frozen_inputs"][str(binary)]:
            raise ValueError("executable bytes changed")
    executable_gate(manifest["initial_frontier_run"], new_binary)
    counts = {"origin_native_launches": 1, "legacy_empty_launches": 0}
    for event in manifest["events"]:
        if event["kind"] == "reused_empty":
            executable_gate(event["run"], old_binary)
            counts["legacy_empty_launches"] += 1
        elif event["kind"] == "closed":
            executable_gate(event["run"], new_binary)
            counts["origin_native_launches"] += 1
        elif event["kind"] in ("split", "refine"):
            executable_gate(event["frontier_run"], new_binary)
            counts["origin_native_launches"] += 1
            if event["kind"] == "split":
                executable_gate(event["limited_run"], new_binary)
                counts["origin_native_launches"] += 1
    negatives = []
    wrong = deepcopy(manifest["initial_frontier_run"])
    wrong["command"][1] = str(old_binary)
    expect_rejection("substituted-legacy-binary",
                     lambda: executable_gate(wrong, new_binary), negatives)
    wrong = deepcopy(manifest["initial_frontier_run"])
    wrong["command"][0] = "/unexpected-loader"
    expect_rejection("substituted-loader",
                     lambda: executable_gate(wrong, new_binary), negatives)
    report = {
        "schema": "N26-origin-current-content-and-launch-audit-v1",
        "current_content_reconstruction_passed": True,
        "bound_executable_identity_checks_passed": True,
        **pairs, **counts,
        "arbitrary_cover_reduction_accepted": False,
        "N26_complete_catalog": False, "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "files": {
            str(p): sha(p) for p in (
                Path(__file__), args.progress, checkpoint,
                WORK / "run_origin_prefix_batch.py", old_binary, new_binary,
                WORK.parent / "outputs/n26-geometric-bridge-v1.md",
                WORK.parent / "outputs/n26-origin-screen-controls-v1.json",
            )
        },
        "scope": "Reconstructs current saved work and checks actual executable names and bytes; does not certify the continuous manuscript.",
    }
    publish(args.output, report)
    print(json.dumps({"current_content_recheck_passed": True, **pairs, **counts}), flush=True)


if __name__ == "__main__":
    main()
