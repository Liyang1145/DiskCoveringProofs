"""Build fresh native checks for every explicit current unresolved terminal."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux, native_command
from n26_force import CAPS, D
from verify_terminal_catalog import sha, local_path, BINARY_SHA, CPP_SHA


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-stage", type=Path, required=True)
    parser.add_argument("--candidate-control", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted = json.loads((args.source_stage / "VERIFIED.json").read_text())
    for name, digest in accepted["files"].items():
        if sha(args.source_stage / name) != digest:
            raise ValueError("terminal catalogue source changed")
    if not accepted["verified"] or accepted["global_optimality_proved"]:
        raise ValueError("terminal catalogue source has wrong scope")
    if (sha(args.source_stage / "peel_prefix_origin.linux") != BINARY_SHA
            or sha(args.source_stage / "peel_prefix_origin.cpp") != CPP_SHA):
        raise ValueError("terminal native kernel changed")
    trace = json.loads((args.source_stage / "TRACE.json").read_text())
    selected = sorted((int(b), p) for b, rows in trace["terminal_pending_prefixes"].items() for p in rows)
    if not selected:
        raise ValueError("no explicit unresolved terminal to catalogue")
    args.output.mkdir(parents=True)
    copies = [(args.source_stage / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
              (args.source_stage / "FRONTIER.json", "SOURCE-FRONTIER.json"),
              (args.source_stage / "TRACE.json", "SOURCE-TRACE.json"),
              (args.candidate_control / "VERIFIED.json", "CANDIDATE-ACCEPTANCE.json"),
              (args.candidate_control / "CANDIDATE-PATH.json", "CANDIDATE-PATH.json")]
    control = json.loads((args.candidate_control / "VERIFIED.json").read_text())
    candidate_key = next(name for name in control["files"] if local_path(name).name == "CANDIDATE-PATH.json")
    copies.extend((args.source_stage / name, name) for name in
                  ("audit_prefix_partition.py", "audit_prefix_origin.py", "n26_force.py",
                   "verify_degree_area.py", "exact_arcs.py"))
    copies.extend((Path(__file__).with_name(name), name) for name in
                  ("n26_terminal_canonical.py", "verify_terminal_catalog.py", "build_terminal_catalog.py"))
    copies.append((Path(__file__).with_name("n26-terminal-catalog-proof.md"), "PROOF.md"))
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    runs = []
    for index, (b, prefix) in enumerate(selected):
        target, launch = args.output / f"terminal-{index:03d}.json", args.output / f"terminal-{index:03d}-launch.json"
        command = native_command(args.source_stage / "peel_prefix_origin.linux", [
            "26", str(b), linux(target), str(D), *map(str, CAPS), "1", "dfs", "solve",
            ",".join(map(str, prefix)), "0", "1"])
        run = subprocess.run(command, capture_output=True, timeout=30)
        launch.write_text(json.dumps({"command": command, "exit_code": run.returncode,
                                     "stdout": run.stdout.decode("utf-8", errors="replace"),
                                     "stderr": run.stderr.decode("utf-8", errors="replace")}, indent=2) + "\n", encoding="utf-8")
        if run.returncode:
            raise ValueError("selected terminal native canonical check failed")
        runs.append({"index": index, "B": b, "prefix": prefix, "result": target.name,
                     "result_sha256": sha(target), "launch": launch.name, "launch_sha256": sha(launch)})
    (args.output / "NATIVE-RUNS.json").write_text(json.dumps(runs, separators=(",", ":")) + "\n", encoding="utf-8")
    manifest = {"schema": "N26-selected-terminal-catalogue-input-bindings-v1",
                "source_stage": linux(args.source_stage),
                "source_acceptance_sha256": sha(args.source_stage / "VERIFIED.json"),
                "candidate_path_key": candidate_key,
                "copied_files": {name: sha(args.output / name) for original, name in copies}}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    run = subprocess.run([sys.executable, str(args.output / "verify_terminal_catalog.py"),
                          "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=False)
    if run.returncode:
        raise ValueError("selected terminal catalogue exact acceptance failed")


if __name__ == "__main__":
    main()
