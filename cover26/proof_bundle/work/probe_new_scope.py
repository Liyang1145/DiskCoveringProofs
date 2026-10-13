"""Bounded fresh-scope runs. A node-limit result stays explicitly incomplete."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import time

from audit_prefix_partition import WORK, check_frontier, native_command, publish
from audit_prefix_origin import OriginReference, validate_disk
from new_upper_scope import sha as original_sha


def sha(path):
    return original_sha(str(path).replace("\\", "/"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=200000)
    parser.add_argument("--families", type=int, nargs="+", choices=(14, 15, 16, 17),
                        default=[14, 15, 16, 17])
    args = parser.parse_args()
    if args.output.exists() or args.limit < 1:
        raise ValueError("fresh output and positive node limit required")
    frontier_dir = WORK.parent / "outputs/n26-new-scope-frontiers-v1"
    gate_path = frontier_dir / "VERIFIED.json"
    gate = json.loads(gate_path.read_text(encoding="utf-8"))
    if not gate["frontier_generation_and_independent_reconstruction_verified"]:
        raise ValueError("unaccepted new-scope frontiers")
    for path, digest in gate["files"].items():
        if sha(path) != digest:
            raise ValueError("changed frontier dependency: " + path)
    constants_path = WORK.parent / "outputs/n26-new-scope-v1/CONSTANTS.json"
    constants = json.loads(constants_path.read_text(encoding="utf-8"))
    caps, scale = constants["angle_caps"], constants["angle_scale"]
    binary = WORK / "prefix-origin-v1/peel_prefix_origin.linux"
    args.output.mkdir(parents=True)
    records = []
    for b in args.families:
        entry = next(row for row in gate["families"] if row["B"] == b)
        frontier_path = Path(entry["frontier_path"])
        if sha(frontier_path) != entry["frontier_sha256"]:
            raise ValueError("changed frontier")
        reference = OriginReference(26, b, "dfs", caps=caps, scale=scale)
        check_frontier(json.loads(frontier_path.read_text()), reference, (), 2)
        target = args.output / f"N26-B{b}.json"
        log_path = args.output / f"N26-B{b}-launch.json"
        command = native_command(binary, [
            "26", str(b), str(target), str(scale), *map(str, caps), str(args.limit),
            "dfs", "solve", "-", "0", "1"])
        start = time.monotonic()
        run = subprocess.run(command, capture_output=True, timeout=90)
        text = (run.stdout + run.stderr).decode("utf-8", errors="replace")
        launch = {"command": command, "exit_code": run.returncode,
                  "seconds": time.monotonic() - start, "output": text}
        publish(log_path, launch)
        record = {"N": 26, "B": b, "I": 26 - b,
                  "exit_code": run.returncode, "seconds": launch["seconds"],
                  "launch_file": str(log_path), "launch_sha256": sha(log_path),
                  "arbitrary_cover_reduction_accepted": False,
                  "global_optimality_proved": False}
        if run.returncode:
            if target.exists() or Path(str(target) + ".partial").exists():
                raise ValueError("incomplete run left complete/partial publication")
            match = re.search(r"REJECTED NODE LIMIT:.*calls=(\d+) origin_prunes=(\d+) survivors=(\d+)", text)
            if match is None or int(match[1]) != args.limit:
                raise ValueError("unexpected run failure: " + text)
            record.update({"restricted_catalog_complete": False, "calls": int(match[1]),
                           "origin_prunes": int(match[2]),
                           "partial_survivor_count_not_a_catalog": int(match[3]),
                           "final_catalog_published": False})
        else:
            data = json.loads(target.read_text())
            if not (data["complete"] and data["family_complete"] and data["N"] == 26
                    and data["B"] == b and data["mode"] == "dfs" and data["prefix"] == []
                    and data["caps"] == caps and data["scale"] == scale
                    and data["origin_screen"] and data["screen"]
                    and not data["global_optimality_proved"] and not data["geometric_reduction_proved"]
                    and data["orbits"] == len(data["survivors"])):
                raise ValueError("wrong completed-run metadata")
            for graph in data["survivors"]:
                validate_disk(26, b, graph["faces"])
            record.update({"restricted_catalog_complete": True, "calls": data["calls"],
                           "orbits": data["orbits"], "rooted": data["rooted"],
                           "catalog_file": str(target), "catalog_sha256": sha(target),
                           "final_catalog_published": True})
        records.append(record)
        print(json.dumps(record), flush=True)
    publish(args.output / "RUNS.json", {
        "schema": "N26-fresh-scope-bounded-catalog-runs-v1", "runs": records,
        "files": {str(path): sha(path) for path in (
            Path(__file__), binary, WORK / "prefix-origin-v1/peel_prefix_origin.cpp",
            gate_path, constants_path)},
        "global_optimality_proved": False})


if __name__ == "__main__":
    main()
