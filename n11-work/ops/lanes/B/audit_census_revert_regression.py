#!/usr/bin/env python3
"""Pin the +revert census regression against the last green census source.

This is a source/byte audit, not a Lean kernel check.
"""
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work" / "lean" / "N11Formalization"
GREEN = "6937fb90"
NAMES = [f"EnergyTerminalResidualCensusC0{i}.lean" for i in range(1, 5)]
BARE = re.compile(r"decide \+kernel(?! \+revert)")
REVERT = re.compile(r"decide \+kernel \+revert")


def counts(text):
    return {"bare": len(BARE.findall(text)), "revert": len(REVERT.findall(text))}


rows = {}
for name in NAMES:
    path = LEAN / name
    live = path.read_text()
    old = subprocess.check_output(
        ["git", "-C", str(ROOT), "show", f"{GREEN}:n11-work/lean/N11Formalization/{name}"],
        text=True,
    )
    rows[name] = {
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest().upper(),
        "live": counts(live),
        "green": counts(old),
        "source_identical_to_green": live == old,
    }

failures = []
for name, row in rows.items():
    if row["live"] != {"bare": 0, "revert": row["green"]["bare"]}:
        failures.append(f"{name}: unexpected live census-decide counts")
    if row["green"]["revert"] != 0:
        failures.append(f"{name}: green snapshot already contains +revert")
    if row["source_identical_to_green"]:
        failures.append(f"{name}: source unexpectedly identical to green")

result = {
    "scope": "source/byte regression audit only; not a Lean kernel check",
    "green_commit": GREEN,
    "ok": not failures,
    "failures": failures,
    "parts": rows,
    "live_totals": {
        key: sum(row["live"][key] for row in rows.values()) for key in ("bare", "revert")
    },
    "green_totals": {
        key: sum(row["green"][key] for row in rows.values()) for key in ("bare", "revert")
    },
}
print(json.dumps(result, indent=2, sort_keys=True))
raise SystemExit(0 if result["ok"] else 1)
