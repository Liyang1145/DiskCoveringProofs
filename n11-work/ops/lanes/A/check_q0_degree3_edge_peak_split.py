#!/usr/bin/env python3
"""Check exact preservation of the q0 edge-peak proof split."""
from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work/lean/N11Formalization"
REL = "n11-work/lean/N11Formalization/SevenClassQ0Deg3UpperReductionUnimodal.lean"
REV = "a0f0f971"
SOURCE_SHA256 = "69e6eabf59a15a034a8c3bb8b53b665a85f785a7191227960b8d2533ab92c367"
GROUPS = (
    "SevenClassQ0Deg3UpperReductionUnimodalPeaks0To6.lean",
    "SevenClassQ0Deg3UpperReductionUnimodalPeaks7To13.lean",
    "SevenClassQ0Deg3UpperReductionUnimodalPeaks14To20.lean",
)
ROW_MODULE = "SevenClassQ0Deg3UpperReductionUnimodalPeak{:02d}.lean"
ROWS = tuple(ROW_MODULE.format(i) for i in range(21))
PATTERN = re.compile(
    r"(?m)^theorem edgePeakValid_(\d+) : EdgePeakValid \1 := by\n"
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
    if sorted(actual) != list(range(21)):
        failures.append(f"proof indices are {sorted(actual)}, expected 0..20 once each")
    for index in set(expected) & set(actual):
        if expected[index] != actual[index]:
            failures.append(f"edgePeakValid_{index}: proof bytes changed")
    for name in (*GROUPS, "SevenClassQ0Deg3UpperReductionUnimodalBase.lean", REL.split("/")[-1]):
        if blocks((LEAN / name).read_text(encoding="utf-8")):
            failures.append(f"{name}: still contains edgePeak proof bodies")
    targets = (ROOT / "n11-work/ops/lanes/A/TARGETS.txt").read_text(encoding="utf-8").splitlines()
    for name in (
        "SevenClassQ0Deg3UpperReductionUnimodalBase",
        *(Path(row).stem for row in ROWS),
        *(Path(group).stem for group in GROUPS),
        "SevenClassQ0Deg3UpperReductionUnimodal",
    ):
        if f"N11Formalization.{name}" not in targets:
            failures.append(f"TARGETS.txt misses {name}")
    if failures:
        print("FAIL")
        print("\n".join(failures))
        return 1
    print("PASS: 21 edge-peak proof bodies preserved byte-for-byte and declared once")
    return 0


if __name__ == "__main__":
    sys.exit(main())
