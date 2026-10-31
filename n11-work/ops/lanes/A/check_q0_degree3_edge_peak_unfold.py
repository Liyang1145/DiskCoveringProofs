#!/usr/bin/env python3
"""Reject edge-peak peak checks that omit explicit unfoldings.

CI run 41182882564 showed that the local simp attribute alone does not unfold
`edgeUpper` when each proof supplies an explicit `norm_num` list.  This gate is
textual only; it complements, and does not replace, kernel acceptance.
"""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work/lean/N11Formalization/SevenClassQ0Deg3UpperReductionUnimodal.lean"
REQUIRED = ("EdgePeakValid", "edgeUpper", "edgeCoeff", "tableEdges", "nodeQ",
            "Fin.val_ofNat", "Fin.val_mk")


def main() -> int:
    text = LEAN.read_text(encoding="utf-8")
    blocks = re.findall(
        r"theorem edgePeakValid_(\d+) : EdgePeakValid \1 := by"
        r"((?:\n  (?:unfold EdgePeakValid|rw \[[^\n]*\]))*)\s+norm_num \[([^\]]*)\]",
        text,
    )
    indices = [int(i) for i, _, _ in blocks]
    failures = []
    if indices != list(range(21)):
        failures.append(f"expected indices 0..20 once each, got {indices}")
    for i, witness_rw, names_text in blocks:
        if "unfold EdgePeakValid" not in witness_rw:
            failures.append(f"edgePeakValid_{i}: witness rewrite precedes EdgePeakValid unfold")
        if "decide +kernel" not in witness_rw:
            failures.append(f"edgePeakValid_{i}: missing kernel-decided witness equality")
        names = {name.strip() for name in names_text.replace("\n", " ").split(",")}
        missing = [name for name in REQUIRED if name not in names]
        if missing:
            failures.append(f"edgePeakValid_{i}: missing {missing}")
    if failures:
        print("FAIL")
        print("\n".join(failures))
        return 1
    print(f"PASS: {len(blocks)} edge-peak checks explicitly unfold all required definitions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
