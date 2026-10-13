"""Actual Linux missing-catalogue readiness; no proof or geometry writes."""

import argparse
import json
import os
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", type=int, required=True)
    args = parser.parse_args()
    if not sys.platform.startswith("linux") or not 20 <= args.stage <= 1000:
        raise ValueError("this scoped catalogue readiness must execute in Linux on an explicit n26stage")
    print("ACTUAL_LINUX_MISSING_CATALOGUE_READINESS", args.stage, sys.version, flush=True)
    root = Path(__file__).resolve().parent.parent
    stage = root / ("outputs/n26-conditional-force-stage-v"+str(args.stage)+"-sparse-v1")
    catalogue = root / ("outputs/n26-conditional-terminal-catalog-v"+str(args.stage)+"-sparse-native-v1")
    script = root / "work/build_terminal_catalog.py"
    accepted = json.loads((stage / "VERIFIED.json").read_text(encoding="utf-8"))
    matches = []
    for path in Path("/proc").iterdir():
        if not path.name.isdigit() or int(path.name) == os.getpid():
            continue
        try:
            command = (path / "cmdline").read_bytes().replace(b"\0", b" ").decode(
                "utf-8", errors="replace")
        except OSError:
            continue
        if "build_terminal_catalog.py" in command and (
                "stage-v"+str(args.stage) in command or "catalog-v"+str(args.stage) in command):
            matches.append({"pid": int(path.name), "command": command})
    print({"original_catalogue_script_exists": script.is_file(),
           "actual_source_own_verified": accepted["verified"],
           "actual_source_native_events": accepted["native_events_independently_replayed"],
           "catalogue_target_exists": catalogue.exists(), "matching_actual_linux_builders": matches}, flush=True)
    if (not script.is_file() or accepted["verified"] is not True
            or accepted["global_optimality_proved"] is not False
            or accepted["native_events_independently_replayed"] != 4800
            or catalogue.exists() or matches):
        raise ValueError("original missing-only catalogue readiness not established")
    print("ACTUAL_MISSING_ONLY_ORIGINAL_CATALOGUE_READINESS_PASSED", flush=True)


if __name__ == "__main__":
    main()
