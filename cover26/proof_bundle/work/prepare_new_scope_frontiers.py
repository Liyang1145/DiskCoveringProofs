"""Produce the four NEW-threshold frontiers; never reuse old prefix indices."""

import argparse
from copy import deepcopy
import json
from pathlib import Path
import subprocess

from audit_prefix_partition import WORK, check_frontier, native_command, publish
from audit_prefix_origin import OriginReference
from new_upper_scope import sha as source_sha


def sha(path):
    return source_sha(str(path).replace("\\", "/"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    scope = WORK.parent / "outputs/n26-new-scope-v1"
    gate = json.loads((scope / "VERIFIED.json").read_text(encoding="utf-8"))
    if not gate["arithmetic_verified"] or not gate["family_scope_valid_assuming_cited_n8_theorem"]:
        raise ValueError("new threshold scope not accepted arithmetically")
    for path, digest in gate["files"].items():
        if sha(path) != digest:
            raise ValueError("changed family-budget input")
    constants = json.loads((scope / "CONSTANTS.json").read_text(encoding="utf-8"))
    caps, D = constants["angle_caps"], constants["angle_scale"]
    if constants["families"] != [[14, 12], [15, 11], [16, 10], [17, 9]]:
        raise ValueError("wrong new family list")
    controls_path = WORK.parent / "outputs/n26-origin-screen-controls-v1.json"
    controls = json.loads(controls_path.read_text(encoding="utf-8"))
    for path, digest in controls["files"].items():
        if sha(path) != digest:
            raise ValueError("origin implementation changed")
    binary = WORK / "prefix-origin-v1/peel_prefix_origin.linux"
    args.output.mkdir(parents=True)
    families, negatives = [], []
    for b, inside in constants["families"]:
        path = args.output / f"N26-B{b}-frontier.json"
        logfile = args.output / f"N26-B{b}-launch.json"
        command = native_command(binary, [
            "26", str(b), str(path), str(D), *map(str, caps),
            "0", "dfs", "frontier", "-", "2", "1",
        ])
        run = subprocess.run(command, capture_output=True, timeout=90)
        publish(logfile, {
            "command": command, "exit_code": run.returncode,
            "stdout": run.stdout.decode("utf-8", errors="replace"),
            "stderr": run.stderr.decode("utf-8", errors="replace"),
        })
        if run.returncode:
            raise ValueError("frontier launch failed")
        data = json.loads(path.read_text(encoding="utf-8"))
        if not data["origin_screen"]:
            raise ValueError("origin condition omitted")
        reference = OriginReference(26, b, "dfs", caps=caps, scale=D)
        entries = check_frontier(data, reference, (), 2)
        roots = reference.children(reference.initial())
        counts = {}
        for row in entries:
            key = row["child_count"]
            counts[key] = counts.get(key, 0) + 1
        families.append({
            "N": 26, "B": b, "I": inside, "root_children": len(roots),
            "prefix_depth": 2, "frontier_nodes": len(entries),
            "child_count_histogram": counts,
            "full_enumeration_complete": False,
            "frontier_path": str(path), "frontier_sha256": sha(path),
            "launch_sha256": sha(logfile),
        })
        wrong = deepcopy(data)
        wrong["caps"][0] += 1
        try:
            check_frontier(wrong, reference, (), 2)
        except ValueError:
            negatives.append(f"B{b}-changed-cap-rejected")
        else:
            raise AssertionError("mixed old/new threshold accepted")
        print(json.dumps({"B": b, "I": inside, "root_children": len(roots),
                          "depth2_frontier_nodes": len(entries)}), flush=True)
    report = {
        "schema": "N26-new-upper-four-family-frontier-audit-v1",
        "frontier_generation_and_independent_reconstruction_verified": True,
        "new_radius_upper": constants["radius_upper"],
        "new_angle_caps": caps, "origin_condition_enabled": True,
        "external_published_n8_theorem_used": True,
        "families": families, "negative_controls_rejected": negatives,
        "global_optimality_proved": False, "N26_complete_catalog": False,
        "old_B18_queue_preserved_not_declared_exhausted": True,
        "files": {str(path): sha(path) for path in (
            Path(__file__), WORK / "audit_prefix_partition.py",
            WORK / "audit_prefix_origin.py",
            WORK / "prefix-origin-v1/peel_prefix_origin.cpp", binary,
            scope / "CONSTANTS.json", scope / "DEPENDENCIES.json", scope / "VERIFIED.json",
            controls_path,
        )},
    }
    publish(args.output / "VERIFIED.json", report)


if __name__ == "__main__":
    main()
