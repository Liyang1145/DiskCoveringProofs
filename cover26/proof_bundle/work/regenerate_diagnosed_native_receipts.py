"""Create exact recovery candidates for diagnosed native receipts.

No historical targets are modified. Generated launch bytes are explicitly
historical recovery candidates, not the provenance of the actual new-path run.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from audit_prefix_partition import linux, native_command
from scan_current_inventory_integrity import local_path, sha


AUDIT_SHA = "6a46131202a5d2dd732b88622b1cec0e072c7b6ef888f37e70f420b291590203"
CPP_SHA = "a76a8ce6c0ee0ee0f513ae9eba086d5b6d1b6b3e39440ab0cac59ef5638620c9"
BINARY_SHA = "b07a612b71d7535a3d667dc764bcafadd104e14b6ce560f6810e56cfc9ba3a25"


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnosis", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.report.exists():
        raise FileExistsError("recovery candidates require fresh output paths")
    diagnosis_sha = sha(args.diagnosis)
    diagnosis = read(args.diagnosis)
    current_path = local_path(diagnosis["current_audit"])
    if (
        diagnosis["current_audit_sha256"] != AUDIT_SHA
        or sha(current_path) != AUDIT_SHA
        or diagnosis["current_audit_unchanged"] is not True
        or diagnosis["historical_targets_modified"] is not False
        or diagnosis["failure_count"] != len(diagnosis["failures"])
    ):
        raise ValueError("the complete diagnosis or its original inventory changed")
    inventory = read(current_path)["files"]
    expected = {str(local_path(text).resolve()): digest for text, digest in inventory.items()}

    def bound(path):
        digest = sha(path)
        if expected.get(str(path.resolve())) != digest:
            raise ValueError("recovery dependency is not an unchanged bound file: " + str(path))
        return digest

    groups = {}
    for failure in diagnosis["failures"]:
        path = local_path(failure["path"]).resolve()
        match = re.fullmatch(r"native-(\d{5})(-launch)?\.json", path.name)
        if (
            match is None
            or failure["status"] != "mismatch"
            or failure["stable_during_hash"] is not True
            or failure["snapshot_matches_observed_bytes"] is not True
            or expected.get(str(path)) != failure["expected_sha256"]
            or sha(path) != failure["actual_sha256"]
            or sha(local_path(failure["snapshot_file"])) != failure["actual_sha256"]
        ):
            raise ValueError("diagnosed receipt or its preserved original changed")
        groups.setdefault((path.parent, int(match[1])), []).append(failure)
    args.output.mkdir(parents=True)
    recovered = []
    for (stage, index), failures in groups.items():
        dependencies = {
            name: bound(stage / name)
            for name in ("MANIFEST.json", "TRACE.json", "NATIVE-VERIFIED.json",
                         "peel_prefix_origin.cpp", "peel_prefix_origin.linux")
        }
        manifest = read(stage / "MANIFEST.json")
        event = read(stage / "TRACE.json")["events"][index]
        record = read(stage / "NATIVE-VERIFIED.json")["runs"][index]
        if (
            dependencies["TRACE.json"] != manifest["trace_sha256"]
            or dependencies["peel_prefix_origin.cpp"] != CPP_SHA
            or dependencies["peel_prefix_origin.linux"] != BINARY_SHA
            or record["event_index"] != index
            or record["result"] != f"native-{index:05d}.json"
            or record["launch"] != f"native-{index:05d}-launch.json"
            or expected.get(str((stage / record["result"]).resolve())) != record["result_sha256"]
            or expected.get(str((stage / record["launch"]).resolve())) != record["launch_sha256"]
        ):
            raise ValueError("original native kernel, exact input or receipt binding changed")
        depth = 1 if event["kind"] == "split" else 0
        result_path = args.output / f"{stage.name}-native-{index:05d}.json"
        launch_path = args.output / f"{stage.name}-native-{index:05d}-launch.json"
        tail = [
            "26", str(event["B"]), linux(result_path), "10000000",
            "754112", "1555305", "2486507", "3880649", "0", "dfs",
            "frontier", ",".join(map(str, event["prefix"])) if event["prefix"] else "-",
            str(depth), "1",
        ]
        command = native_command(stage / "peel_prefix_origin.linux", tail)
        run = subprocess.run(command, capture_output=True, timeout=30)
        actual_receipt = {
            "actual_new_path_command": command,
            "actual_exit_code": run.returncode,
            "actual_stdout": run.stdout.decode("utf-8", errors="replace"),
            "actual_stderr": run.stderr.decode("utf-8", errors="replace"),
            "actual_result_sha256": sha(result_path) if result_path.exists() else None,
            "historical_targets_modified": False,
            "new_geometric_payments": 0,
        }
        actual_receipt_path = args.output / f"{stage.name}-native-{index:05d}-actual-run.json"
        with actual_receipt_path.open("x", encoding="utf-8", newline="\n") as output:
            output.write(json.dumps(actual_receipt, indent=2) + "\n")
        if run.returncode != 0 or sha(result_path) != record["result_sha256"]:
            raise ValueError("new-path native result does not match the original bytes: "
                             + json.dumps(actual_receipt))
        original_tail = list(tail)
        original_tail[2] = linux(stage / record["result"])
        historical_launch = {
            "event_index": index, "B": event["B"], "prefix": event["prefix"],
            "depth": depth, "exit_code": 0,
            "command": ["/lib64/ld-linux-x86-64.so.2",
                        linux(stage / "peel_prefix_origin.linux"), *original_tail],
            "stdout": run.stdout.decode("utf-8", errors="replace"),
            "stderr": run.stderr.decode("utf-8", errors="replace"),
        }
        payload = (json.dumps(historical_launch, indent=2) + "\n").encode("utf-8")
        if hashlib.sha256(payload).hexdigest() != record["launch_sha256"]:
            raise ValueError("historical launch recovery candidate is not byte-identical")
        with launch_path.open("xb") as output:
            output.write(payload)
        for name, digest in dependencies.items():
            if sha(stage / name) != digest:
                raise ValueError("original native dependency changed during recovery")
        mappings = []
        for failure in failures:
            target = local_path(failure["path"])
            candidate = launch_path if target.name.endswith("-launch.json") else result_path
            if sha(candidate) != failure["expected_sha256"]:
                raise ValueError("candidate differs from the exact original inventory")
            mappings.append({
                "historical_target": str(target.resolve()),
                "candidate_file": str(candidate.resolve()),
                "expected_original_sha256": failure["expected_sha256"],
                "diagnosed_corrupt_sha256": failure["actual_sha256"],
                "preserved_corrupt_snapshot": failure["snapshot_file"],
            })
        recovered.append({
            "stage": str(stage), "event_index": index,
            "original_bound_dependencies": dependencies,
            "actual_new_path_command": command,
            "actual_exit_code": run.returncode,
            "actual_stdout": historical_launch["stdout"],
            "actual_stderr": historical_launch["stderr"],
            "actual_new_path_receipt": str(actual_receipt_path.resolve()),
            "actual_new_path_receipt_sha256": sha(actual_receipt_path),
            "regenerated_result": str(result_path.resolve()),
            "regenerated_result_sha256": sha(result_path),
            "historical_launch_recovery_candidate": str(launch_path.resolve()),
            "historical_launch_recovery_candidate_sha256": sha(launch_path),
            "both_candidates_match_original_bound_bytes": True,
            "restoration_candidates": mappings,
        })
    if sha(current_path) != AUDIT_SHA or sha(args.diagnosis) != diagnosis_sha:
        raise ValueError("original current inventory or diagnosis changed during recovery")
    report = {
        "schema": "N26-diagnosed-native-byte-exact-recovery-candidates-v2",
        "diagnosis_sha256": diagnosis_sha,
        "current_audit_sha256": AUDIT_SHA,
        "recovered_native_events": recovered,
        "affected_target_count": sum(len(row["restoration_candidates"]) for row in recovered),
        "historical_launch_candidates_are_not_actual_new_run_provenance": True,
        "historical_targets_not_modified_by_this_script": True,
        "all_candidates_match_original_bound_bytes": True,
        "new_geometric_payments": 0,
        "executed_recovery_script_sha256": sha(Path(__file__)),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
