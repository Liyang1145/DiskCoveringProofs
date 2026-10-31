#!/usr/bin/env python3
"""Reject sector-peak regressions observed in Lane A CI.

The sector proofs depend on names imported from a separate namespace, and an
explicit `norm_num` list does not unfold definitions omitted from that list.
This textual gate requires the direct import/open and all nine complete lists.
It complements, but does not replace, kernel acceptance.
"""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work/lean/N11Formalization/SevenClassQ0Deg3SectorPeak.lean"
REQUIRED = (
    "sectorMax",
    "sectorUpper",
    "areaUpper",
    "nodeBin",
    "nodeBinAt",
    "binIndex",
    "mu",
    "lam",
    "nextSite",
    "ringSite",
    "nextRing",
    "nodeQ",
    "sinHiNLag",
    "sinLoNLag",
    "sinTQ",
    "RatInterval.piHi",
    "Fin.val_ofNat",
    "Fin.val_mk",
)


def main() -> int:
    text = LEAN.read_text(encoding="utf-8")
    failures = []
    if "import N11Formalization.ActualRingLinkBoundaryData" not in text:
        failures.append("missing direct ActualRingLinkBoundaryData import")
    if "open N11Formalization.ActualRingLinkBoundaryData" not in text:
        failures.append("missing absolute ActualRingLinkBoundaryData open")
    if not re.search(
        r"def SectorPeakValid \(i : Fin 9\) : Prop :=\n"
        r"  sectorUpper [^\n]*\n"
        r"    [^\n]*\n"
        r"      sectorMax i\n",
        text,
    ):
        failures.append("SectorPeakValid must target downstream sectorMax i")

    blocks = re.findall(
        r"theorem sectorPeakValid_(\d+) : SectorPeakValid \1 := by"
        r"((?:\n  (?:unfold SectorPeakValid|rw \[[^\n]*\]))*)\s+norm_num \[([^\]]*)\]",
        text,
    )
    indices = [int(i) for i, _, _ in blocks]
    if indices != list(range(9)):
        failures.append(f"expected indices 0..8 once each, got {indices}")
    for i, witness_rw, names_text in blocks:
        if "unfold SectorPeakValid" not in witness_rw:
            failures.append(f"sectorPeakValid_{i}: witness rewrite precedes SectorPeakValid unfold")
        if "decide +kernel" not in witness_rw:
            failures.append(f"sectorPeakValid_{i}: missing kernel-decided witness equality")
        names = {name.strip() for name in names_text.replace("\n", " ").split(",")}
        missing = [name for name in REQUIRED if name not in names]
        if missing:
            failures.append(f"sectorPeakValid_{i}: missing {missing}")

    if failures:
        print("FAIL")
        print("\n".join(failures))
        return 1
    print(f"PASS: {len(blocks)} sector-peak checks explicitly unfold all required definitions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
