"""Actual Linux readiness observation; cannot write native/geometry evidence."""

import os
from pathlib import Path
import sys


def main():
    if not sys.platform.startswith("linux"):
        raise ValueError("native readiness must actually execute inside Linux")
    print("ACTUAL_STAGE34_LINUX_READONLY_PROBE", sys.version, flush=True)
    stage = Path(__file__).resolve().parent.parent / "outputs/n26-conditional-force-stage-v34-sparse-v1"
    script = stage / "audit_force_forest_native.py"
    native_files = list(stage.glob("native-*"))
    matches = []
    for path in Path("/proc").iterdir():
        if not path.name.isdigit() or int(path.name) == os.getpid():
            continue
        try:
            command = (path / "cmdline").read_bytes().replace(b"\0", b" ").decode(
                "utf-8", errors="replace")
        except OSError:
            continue
        if "audit_force_forest_native.py" in command and "stage-v34" in command:
            matches.append({"pid": int(path.name), "command": command})
    print({"original_native_script_exists": script.is_file(),
           "fresh_manifest_exists": (stage / "MANIFEST.json").is_file(),
           "native_event_or_launch_files": len(native_files),
           "native_acceptance_exists": (stage / "NATIVE-VERIFIED.json").exists(),
           "actual_original_native_workers": matches}, flush=True)
    if (not script.is_file() or not (stage / "MANIFEST.json").is_file()
            or native_files or (stage / "NATIVE-VERIFIED.json").exists() or matches):
        raise ValueError("preserve existing native evidence/live worker; do not restart")
    print("ACTUAL_STAGE34_MISSING_NATIVE_READINESS_PASSED", flush=True)


if __name__ == "__main__":
    main()
