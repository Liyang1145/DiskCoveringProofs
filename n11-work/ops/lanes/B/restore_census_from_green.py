#!/usr/bin/env python3
"""Hash-pin the four residual-census parts to the last kernel-green commit.

Default mode is read-only.  ``--apply`` rewrites only the four literal census
parts, and only after every blob at the pinned commit has the expected SHA-256.
This script does not run Lean and therefore cannot establish kernel success.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

GREEN_COMMIT = "6937fb90"
ROOT = Path(__file__).resolve().parents[4]
SOURCE_DIR = ROOT / "n11-work" / "lean" / "N11Formalization"
PARTS = {
    "EnergyTerminalResidualCensusC01.lean": "d629d5bcd466dfa66c82352d2d214432bac2b8fa33bb884b83f759725b470499",
    "EnergyTerminalResidualCensusC02.lean": "ffc9ff2cd42538fdb5f76766a22514393ba9c1d93bf9ee42026099a808ce4a94",
    "EnergyTerminalResidualCensusC03.lean": "bc4a9bf45c5dcc9c9c762e1066999565914473561cbc20f286600b1e35b8e697",
    "EnergyTerminalResidualCensusC04.lean": "70d5ffd57515b97b88e25f48377ef196a9953cbe7c399c7cb089ebda49aef66b",
}

def blob(path: str) -> bytes:
    return subprocess.run(["git", "show", f"{GREEN_COMMIT}:{path}"], cwd=ROOT,
                          check=True, stdout=subprocess.PIPE).stdout

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    records: dict[str, object] = {}
    failures: list[str] = []
    blobs: dict[Path, bytes] = {}
    for name, expected_green in PARTS.items():
        rel = f"n11-work/lean/N11Formalization/{name}"
        live_path = SOURCE_DIR / name
        green = blob(rel)
        live = live_path.read_bytes()
        actual_green = digest(green)
        if actual_green != expected_green:
            failures.append(f"green blob drift: {name} {actual_green} != {expected_green}")
        if b"+revert" not in live:
            failures.append(f"live file has no +revert marker: {name}")
        records[name] = {"green_sha256": actual_green,
                         "live_sha256": digest(live),
                         "changed": green != live,
                         "revert_markers": live.count(b"+revert")}
        blobs[live_path] = green
    if not failures and args.apply:
        for path, data in blobs.items():
            path.write_bytes(data)
    report = {"ok": not failures,
              "scope": "byte restoration only; does not prove Lean kernel acceptance",
              "green_commit": GREEN_COMMIT,
              "mode": "apply" if args.apply else "check",
              "failures": failures, "parts": records}
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.report:
        args.report.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0 if not failures else 1

if __name__ == "__main__":
    raise SystemExit(main())
