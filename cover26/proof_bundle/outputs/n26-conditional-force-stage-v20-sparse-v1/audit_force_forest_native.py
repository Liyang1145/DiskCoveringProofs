"""Fresh native/Python agreement for every recorded forest event."""

import argparse
import json
from pathlib import Path
import subprocess

from audit_prefix_origin import OriginReference
from audit_prefix_partition import check_frontier, native_command, sha
from n26_force import CAPS, D


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    args = parser.parse_args()
    target_report = args.input / "NATIVE-VERIFIED.json"
    if target_report.exists():
        raise FileExistsError(target_report)
    manifest = json.loads((args.input / "MANIFEST.json").read_text())
    binary = args.input / "peel_prefix_origin.linux"
    if sha(binary) != manifest["kernel_binary_sha256"]:
        raise ValueError("native binary changed")
    trace_path = args.input / "TRACE.json"
    if sha(trace_path) != manifest["trace_sha256"]:
        raise ValueError("trace changed")
    trace = json.loads(trace_path.read_text())
    references = {b: OriginReference(26, b, "dfs", caps=CAPS, scale=D) for b in (14, 15, 16, 17)}
    runs, files = [], [trace_path, binary, args.input / "peel_prefix_origin.cpp", Path(__file__)]
    for index, event in enumerate(trace["events"]):
        b, prefix = event["B"], tuple(event["prefix"])
        depth = 1 if event["kind"] == "split" else 0
        output = args.input / f"native-{index:05d}.json"
        launch = args.input / f"native-{index:05d}-launch.json"
        command = native_command(binary, [
            "26", str(b), str(output), str(D), *map(str, CAPS), "0", "dfs",
            "frontier", ",".join(map(str, prefix)) if prefix else "-", str(depth), "1"])
        run = subprocess.run(command, capture_output=True, timeout=30)
        record = {"event_index": index, "B": b, "prefix": list(prefix), "depth": depth,
                  "exit_code": run.returncode, "command": command,
                  "stdout": run.stdout.decode("utf-8", errors="replace"),
                  "stderr": run.stderr.decode("utf-8", errors="replace")}
        launch.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        if run.returncode:
            raise ValueError("native frontier invocation failed")
        data = json.loads(output.read_text())
        if not data["origin_screen"]:
            raise ValueError("native origin screen disabled")
        check_frontier(data, references[b], prefix, depth)
        runs.append({"event_index": index, "result": output.name, "result_sha256": sha(output),
                     "launch": launch.name, "launch_sha256": sha(launch)})
        files.extend((output, launch))
        if (index + 1) % 100 == 0:
            print(json.dumps({"native_events_independently_matched": index + 1}), flush=True)
    report = {
        "schema": "N26-force-forest-native-reference-agreement-v1",
        "verified_implementation_agreement": True, "native_events_checked": len(runs),
        "runs": runs, "geometric_lower_bound_accepted_by_this_report": False,
        "global_optimality_proved": False, "files": {p.name: sha(p) for p in files}}
    target_report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"native_events_checked": len(runs), "finite_implementation_agreement": True}), flush=True)


if __name__ == "__main__":
    main()
