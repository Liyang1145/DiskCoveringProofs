"""Native zero-depth state/child checks for all proposed coarse ancestors."""

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
    report_path = args.input / "NATIVE-VERIFIED.json"
    if report_path.exists():
        raise FileExistsError(report_path)
    trace_path = args.input / "TRACE.json"
    manifest = json.loads((args.input / "MANIFEST.json").read_text())
    if sha(trace_path) != manifest["trace_sha256"]:
        raise ValueError("changed angular trace")
    binary = args.input / "peel_prefix_origin.linux"
    if sha(binary) != manifest["copied_files"][binary.name]:
        raise ValueError("changed native binary")
    trace = json.loads(trace_path.read_text())
    runs, files = [], [Path(__file__), trace_path, binary]
    for i, closure in enumerate(trace["closures"]):
        b, p = closure["B"], tuple(closure["prefix"])
        path, log = args.input / f"native-{i:03d}.json", args.input / f"native-{i:03d}-launch.json"
        command = native_command(binary, ["26", str(b), str(path), str(D), *map(str, CAPS),
                                         "0", "dfs", "frontier", ",".join(map(str, p)), "0", "1"])
        run = subprocess.run(command, capture_output=True, timeout=30)
        launch = {"exit_code": run.returncode, "command": command,
                  "stdout": run.stdout.decode("utf-8", errors="replace"),
                  "stderr": run.stderr.decode("utf-8", errors="replace")}
        log.write_text(json.dumps(launch, indent=2) + "\n", encoding="utf-8")
        if run.returncode:
            raise ValueError("coarse native invocation failed")
        data = json.loads(path.read_text())
        reference = OriginReference(26, b, "dfs", caps=CAPS, scale=D)
        if not data["origin_screen"]:
            raise ValueError("origin screen omitted")
        check_frontier(data, reference, p, 0)
        files.extend((path, log))
        runs.append({"closure_index": i, "result": path.name, "result_sha256": sha(path),
                     "launch": log.name, "launch_sha256": sha(log)})
    report = {
        "schema": "N26-coarse-angular-native-state-audit-v1",
        "verified_implementation_agreement": True, "runs": runs,
        "geometric_lower_bound_accepted_by_this_report": False, "global_optimality_proved": False,
        "files": {p.name: sha(p) for p in files}}
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"native_ancestor_states_matched": len(runs)}), flush=True)


if __name__ == "__main__":
    main()
