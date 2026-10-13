"""Regenerate one damaged historical receipt to NEW paths only.

No existing historical file is changed by this script. Exact original receipt
hashes, not merely equivalent JSON, are required before any separate restoration.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from audit_prefix_partition import linux, native_command
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--launch-output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if any(path.exists() for path in (args.output, args.launch_output, args.report)):
        raise FileExistsError("historical regeneration requires three fresh output paths")
    manifest = binding.read(args.stage / "MANIFEST.json")
    trace = binding.read(args.stage / "TRACE.json")
    native = binding.read(args.stage / "NATIVE-VERIFIED.json")
    event, record = trace["events"][2312], native["runs"][2312]
    binary = args.stage / "peel_prefix_origin.linux"
    if (
        binding.sha(binary) != "b07a612b71d7535a3d667dc764bcafadd104e14b6ce560f6810e56cfc9ba3a25"
        or binding.sha(args.stage / "peel_prefix_origin.cpp")
        != "a76a8ce6c0ee0ee0f513ae9eba086d5b6d1b6b3e39440ab0cac59ef5638620c9"
        or binding.sha(args.stage / "TRACE.json") != manifest["trace_sha256"]
        or record["event_index"] != 2312
        or record["result_sha256"] != "116de16073938ad3ee927cd0fe54f8ffe6f28ac16926bb695f1d9461528d9fb6"
        or record["launch_sha256"] != "fab64a7e16d4d6adcfb86ec8d790a40530c376884e8da983488b05fc4d346482"
        or event["kind"] != "split"
    ):
        raise ValueError("historical native recovery changed its exact original kernel/input/receipt")
    tail = [
        "26", str(event["B"]), linux(args.output), "10000000",
        "754112", "1555305", "2486507", "3880649", "0", "dfs",
        "frontier", ",".join(map(str, event["prefix"])), "1", "1",
    ]
    actual_command = native_command(binary, tail)
    run = subprocess.run(actual_command, capture_output=True, timeout=30)
    if run.returncode:
        raise ValueError("new-path historical native regeneration failed")
    if binding.sha(args.output) != record["result_sha256"]:
        raise ValueError("regenerated native output is not byte-identical to the original receipt")
    # This is explicitly a byte-recovery candidate for the historical record,
    # NOT a claim that the new-path invocation wrote to the historical path.
    original_tail = list(tail)
    original_tail[2] = linux(args.stage / record["result"])
    original_command = ["/lib64/ld-linux-x86-64.so.2", linux(binary), *original_tail]
    recovered_record = {
        "event_index": 2312, "B": event["B"], "prefix": event["prefix"],
        "depth": 1, "exit_code": 0, "command": original_command,
        "stdout": run.stdout.decode("utf-8", errors="replace"),
        "stderr": run.stderr.decode("utf-8", errors="replace"),
    }
    payload = (json.dumps(recovered_record, indent=2) + "\n").encode("utf-8")
    if hashlib.sha256(payload).hexdigest() != record["launch_sha256"]:
        raise ValueError("historical launch recovery candidate is not byte-identical")
    args.launch_output.write_bytes(payload)
    report = {
        "schema": "N26-byte-exact-historical-native-recovery-candidate-v1",
        "event_index": 2312, "actual_new_path_command": actual_command,
        "actual_stdout": recovered_record["stdout"], "actual_stderr": recovered_record["stderr"],
        "result_sha256": binding.sha(args.output),
        "historical_launch_recovery_candidate_sha256": binding.sha(args.launch_output),
        "both_candidates_match_original_bound_bytes": True,
        "historical_targets_not_modified_by_this_script": True,
        "new_geometric_payments": 0,
        "executed_recovery_script_sha256": binding.sha(__file__),
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
