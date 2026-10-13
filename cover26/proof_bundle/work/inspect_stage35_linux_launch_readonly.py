"""Observe actual Linux readiness only; never write native/geometry evidence."""

import argparse
import os
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", choices=("native", "catalogue"), required=True)
    args = parser.parse_args()
    if not sys.platform.startswith("linux"):
        raise ValueError("this readiness observation must actually run inside Linux")
    root = Path(__file__).resolve().parent.parent
    stage = root / "outputs/n26-conditional-force-stage-v35-sparse-v1"
    catalogue = root / "outputs/n26-conditional-terminal-catalog-v35-sparse-native-v1"
    script = (stage / "audit_force_forest_native.py" if args.phase == "native"
              else root / "work/build_terminal_catalog.py")
    target_files = (list(stage.glob("native-*")) if args.phase == "native" else [])
    acceptance = stage / "NATIVE-VERIFIED.json"
    workers = []
    for process in Path("/proc").iterdir():
        if not process.name.isdigit() or int(process.name) == os.getpid():
            continue
        try:
            command = (process / "cmdline").read_bytes().replace(b"\0", b" ").decode(
                "utf-8", errors="replace")
        except OSError:
            continue
        original_worker = (
            ("audit_force_forest_native.py" in command and "stage-v35" in command)
            or ("build_terminal_catalog.py" in command and "catalog-v35" in command)
        )
        other_interactive_worker = "python3 -i" in command
        if original_worker or other_interactive_worker:
            workers.append({"pid": int(process.name), "command": command})
    observation = {
        "actual_linux_readonly_phase": args.phase,
        "original_script_exists": script.is_file(),
        "fresh_stage_manifest_exists": (stage / "MANIFEST.json").is_file(),
        "native_event_or_launch_files": len(target_files),
        "native_acceptance_exists": acceptance.exists(),
        "stage_acceptance_exists": (stage / "VERIFIED.json").exists(),
        "stage_actual_publication_exists": (
            root / "outputs/n26-conditional-force-stage-published-replay-v35-sparse-v1.json"
        ).exists(),
        "catalogue_target_exists": catalogue.exists(),
        "actual_original_or_other_interactive_workers": workers,
    }
    print(observation, flush=True)
    if not script.is_file() or not (stage / "MANIFEST.json").is_file() or workers:
        raise ValueError("actual original script/manifest/worker readiness failed")
    if args.phase == "native" and (target_files or acceptance.exists()
                                   or (stage / "VERIFIED.json").exists()):
        raise ValueError("preserve stage35 native partials/acceptance; never restart")
    if args.phase == "catalogue" and (
        catalogue.exists() or not observation["stage_acceptance_exists"]
        or not observation["stage_actual_publication_exists"]
    ):
        raise ValueError("catalogue absent-target/source readiness failed")
    print("ACTUAL_STAGE35_MISSING_" + args.phase.upper() + "_READINESS_PASSED",
          flush=True)


if __name__ == "__main__":
    main()
