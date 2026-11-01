#!/usr/bin/env python3
"""Check exact preservation of the q0 sector-peak proof split."""
from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work/lean/N11Formalization"
REL = "n11-work/lean/N11Formalization/SevenClassQ0Deg3SectorPeak.lean"
REV = "11f649b3"
SOURCE_SHA256 = "e124cce598be3ccc38916150bab052d6373b4e62e0e06ae2ad64868070c98bea"
ROW_MODULE = "SevenClassQ0Deg3SectorPeak{:02d}.lean"
ROWS = tuple(ROW_MODULE.format(i) for i in range(9))
PATTERN = re.compile(
    r"(?m)^theorem sectorPeakValid_(\d+) : SectorPeakValid \1 := by\n"
    r"(?:  [^\n]*\n|    [^\n]*\n)+"
)


def blocks(text: str) -> dict[int, str]:
    return {int(m.group(1)): m.group(0).rstrip("\n") for m in PATTERN.finditer(text)}


def main() -> int:
    raw = subprocess.check_output(["git", "show", f"{REV}:{REL}"], cwd=ROOT)
    digest = hashlib.sha256(raw).hexdigest()
    failures: list[str] = []
    if digest != SOURCE_SHA256:
        failures.append(f"source hash {digest} != {SOURCE_SHA256}")
    expected = blocks(raw.decode("utf-8"))
    actual_text = "\n".join((LEAN / name).read_text(encoding="utf-8") for name in ROWS)
    actual = blocks(actual_text)
    if sorted(expected) != list(range(9)):
        failures.append(f"frozen source has sector proofs {sorted(expected)}, expected 0..8")
    if sorted(actual) != list(range(9)):
        failures.append(f"proof indices are {sorted(actual)}, expected 0..8 once each")
    for index in set(expected) & set(actual):
        if expected[index] != actual[index]:
            failures.append(f"sectorPeakValid_{index}: proof bytes changed")
    for name in ("SevenClassQ0Deg3SectorPeakBase.lean", REL.split("/")[-1]):
        if blocks((LEAN / name).read_text(encoding="utf-8")):
            failures.append(f"{name}: still contains sector-peak proof bodies")
    targets = (ROOT / "n11-work/ops/lanes/A/TARGETS.txt").read_text(encoding="utf-8").splitlines()
    for name in (
        "SevenClassQ0Deg3SectorPeakBase",
        *(Path(row).stem for row in ROWS),
        "SevenClassQ0Deg3SectorPeak",
    ):
        if f"N11Formalization.{name}" not in targets:
            failures.append(f"TARGETS.txt misses {name}")
    if failures:
        print("FAIL")
        print("\n".join(failures))
        return 1
    print("PASS: 9 sector-peak proof bodies preserved byte-for-byte and declared once")
    return 0


if __name__ == "__main__":
    sys.exit(main())
