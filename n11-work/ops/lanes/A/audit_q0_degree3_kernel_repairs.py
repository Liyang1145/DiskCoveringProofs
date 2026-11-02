#!/usr/bin/env python3
"""Audit the source repairs needed for the q0 degree-three kernel run.

This is a source preflight, not a Lean kernel verdict.  It catches the three
failure shapes observed in run 41378003343 without attempting a full build.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "n11-work/lean/N11Formalization"
TARGETS = ROOT / "n11-work/ops/lanes/A/TARGETS.txt"


def imported_names(text: str) -> list[str]:
    return re.findall(r"(?m)^import ([^\s]+)$", text)


def main() -> int:
    failures: list[str] = []

    repaired = (LEAN / "SevenClassQ0Deg3Repaired.lean").read_text(encoding="utf-8")
    imports = imported_names(repaired)
    if not imports:
        failures.append("SevenClassQ0Deg3Repaired: no imports found")
    else:
        first_non_import = re.search(r"(?m)^(?!import |$)", repaired)
        last_import_end = repaired.rfind("\n", 0, repaired.find(imports[-1])) + 1
        if first_non_import is None or first_non_import.start() < last_import_end:
            failures.append("SevenClassQ0Deg3Repaired: non-import text precedes final import")
    for required in (
        "N11Formalization.ActualHubTriangleCensus",
        "N11Formalization.ActualOrderedMetricGraphs",
        "N11Formalization.ActualMetricClassReduction",
        "N11Formalization.MetricAreaRationalCertificate",
    ):
        if required not in imports:
            failures.append(f"SevenClassQ0Deg3Repaired: missing {required}")
    if "open ActualRefinementEarCount" not in repaired:
        failures.append("SevenClassQ0Deg3Repaired: missing ActualRefinementEarCount open")

    edge_base = (LEAN / "SevenClassQ0Deg3UpperReductionUnimodalBase.lean").read_text(
        encoding="utf-8"
    )
    edge_repair = (
        "fin_cases i <;> norm_num [edgeCoeff, tableEdges, mu] <;> decide +kernel"
    )
    if edge_base.count(edge_repair) != 1:
        failures.append("edge base: coefficient reduction lacks the exact kernel suffix")

    sector_suffix = "Fin.val_ofNat, Fin.val_mk] <;> decide +kernel"
    for index in range(9):
        path = LEAN / f"SevenClassQ0Deg3SectorPeak{index:02d}.lean"
        text = path.read_text(encoding="utf-8")
        if text.count(sector_suffix) != 1:
            failures.append(f"{path.name}: sector peak lacks the exact kernel suffix")
        if f"theorem sectorPeakValid_{index} : SectorPeakValid {index} := by" not in text:
            failures.append(f"{path.name}: unexpected theorem statement")

    checked = [LEAN / "SevenClassQ0Deg3Repaired.lean", LEAN / "SevenClassQ0Deg3UpperReductionUnimodalBase.lean"]
    checked += [LEAN / f"SevenClassQ0Deg3SectorPeak{i:02d}.lean" for i in range(9)]
    banned = re.compile(r"\b(?:sorry|admit|native_decide|implemented_by)\b|sorryAx")
    for path in checked:
        match = banned.search(path.read_text(encoding="utf-8"))
        if match:
            failures.append(f"{path.name}: banned token {match.group(0)!r}")

    targets = set(TARGETS.read_text(encoding="utf-8").splitlines())
    for module in ("SevenClassQ0Deg3Repaired", "SevenClassQ0Deg3UpperReductionUnimodalBase"):
        if f"N11Formalization.{module}" not in targets:
            failures.append(f"TARGETS.txt: missing N11Formalization.{module}")
    for index in range(9):
        module = f"SevenClassQ0Deg3SectorPeak{index:02d}"
        if f"N11Formalization.{module}" not in targets:
            failures.append(f"TARGETS.txt: missing N11Formalization.{module}")

    if failures:
        print("FAIL")
        print("\n".join(failures))
        return 1
    print("PASS: q0 kernel-repair source preflight (no kernel verdict)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
