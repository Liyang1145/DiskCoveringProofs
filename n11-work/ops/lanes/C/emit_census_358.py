#!/usr/bin/env python3
"""Emit the structural 360 -> 358 census bridge from the reviewed 360 source."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
SOURCE = LEAN / "EnergyTerminalResidualCensusRefine360.lean"
OUTPUT = LEAN / "EnergyTerminalResidualCensusRefine358.lean"


def main() -> None:
    text = SOURCE.read_text()
    replacements = (
        ("EnergyTerminalResidualCensusRefine360", "EnergyTerminalResidualCensusRefine358"),
        ("EnergyTerminalResidualCensusRefine362", "EnergyTerminalResidualCensusRefine360"),
        ("b13_remaining_of_residual360", "b13_remaining_of_residual358"),
        ("b13_remaining_of_residual362", "b13_remaining_of_residual360"),
        ("refinedResidualIDs.card = 360", "refinedResidualIDs.card = 358"),
        ("exact residual of 360 ids", "exact residual of 358 ids"),
        ("from the 362-id", "from the 360-id"),
        ("mem_362_", "mem_360_"),
        ("newRefineIDs_subset_364", "newRefineIDs_subset_360"),
        ("3808", "3851"),
        ("3821", "4162"),
    )
    for old, new in replacements:
        text = text.replace(old, new)
    assert "Refine362" not in text and "Refine364" not in text
    assert "3808" not in text and "3821" not in text
    assert "def newRefineIDs : Finset (Fin 5011) := {3851, 4162}" in text
    assert "refinedResidualIDs.card = 358" in text
    assert "EnergyTerminalResidualCensusRefine360.b13_remaining_of_residual360" in text
    OUTPUT.write_text(text)


if __name__ == "__main__":
    main()
