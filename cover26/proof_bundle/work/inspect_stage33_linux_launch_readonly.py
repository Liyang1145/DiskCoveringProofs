"""Read-only actual Linux readiness probe for the missing stage33 catalogue."""

import os
from pathlib import Path
import sys


def main():
    if not sys.platform.startswith("linux"):
        raise ValueError("this readiness observation must actually execute inside Linux")
    print("ACTUAL_LINUX_READONLY_PROBE", sys.version, os.getpid(), flush=True)
    root = Path(__file__).resolve().parent.parent
    script = root / "work/build_terminal_catalog.py"
    target = root / "outputs/n26-conditional-terminal-catalog-v33-sparse-native-v1"
    matches = []
    for path in Path("/proc").iterdir():
        if not path.name.isdigit() or int(path.name) == os.getpid():
            continue
        try:
            text = (path / "cmdline").read_bytes().replace(b"\0", b" ").decode(
                "utf-8", errors="replace")
        except OSError:
            continue
        if "build_terminal_catalog.py" in text and ("catalog-v33" in text or "stage-v33" in text):
            matches.append({"pid": int(path.name), "command": text})
    print({"actual_script_exists": script.is_file(), "missing_target_exists": target.exists(),
           "actual_stage33_catalogue_builders": matches}, flush=True)
    if not script.is_file() or target.exists() or matches:
        raise ValueError("original missing-only catalogue launch is not presently safe")
    print("ACTUAL_LINUX_STAGE33_MISSING_ONLY_READINESS_PASSED", flush=True)


if __name__ == "__main__":
    main()
