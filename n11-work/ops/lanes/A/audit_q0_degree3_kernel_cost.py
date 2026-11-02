#!/usr/bin/env python3
"""Report the size of literals fed to terminal kernel checks in lane A.

This is a source-cost audit only.  It neither runs Lean nor proves any goal.
"""
from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
MODULES = ROOT / "n11-work/lean/N11Formalization"
TARGETS = [
    *(f"SevenClassQ0Deg3SectorPeak{i:02d}.lean" for i in range(9)),
    "SevenClassQ0Deg3UpperReductionUnimodalBase.lean",
]


def main() -> int:
    print("source-cost audit only; no Lean/kernel verdict")
    failed = False
    for name in TARGETS:
        text = (MODULES / name).read_text(encoding="utf-8")
        literals = [int(x) for x in re.findall(
            r"(?<![A-Za-z0-9_])(\d{20,})(?![A-Za-z0-9_])", text
        )]
        digits = max((len(str(x)) for x in literals), default=0)
        bits = max((x.bit_length() for x in literals), default=0)
        kernels = text.count("decide +kernel")
        print(f"{name}: kernel_sites={kernels} max_digits={digits} max_bits={bits}")
        if kernels == 0:
            failed = True
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
