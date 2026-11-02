#!/usr/bin/env python3
"""Emit the structural 358 -> 356 census bridge from the reviewed 358 source."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
SOURCE = LEAN / "EnergyTerminalResidualCensusRefine358.lean"
OUTPUT = LEAN / "EnergyTerminalResidualCensusRefine356.lean"


def main() -> None:
    text = SOURCE.read_text()
    replacements = (
        ("EnergyTerminalResidualCensusRefine358", "EnergyTerminalResidualCensusRefine356"),
        ("EnergyTerminalResidualCensusRefine360", "EnergyTerminalResidualCensusRefine358"),
        ("b13_remaining_of_residual358", "b13_remaining_of_residual356"),
        ("b13_remaining_of_residual360", "b13_remaining_of_residual358"),
        ("refinedResidualIDs.card = 358", "refinedResidualIDs.card = 356"),
        ("exact residual of 358 ids", "exact residual of 356 ids"),
        ("from the 360-id", "from the 358-id"),
        ("mem_360_", "mem_358_"),
        ("newRefineIDs_subset_360", "newRefineIDs_subset_358"),
        ("3851", "3040"),
        ("4162", "2965"),
    )
    for old, new in replacements:
        text = text.replace(old, new)
    assert "Refine360" not in text
    assert "3851" not in text and "4162" not in text
    assert "def newRefineIDs : Finset (Fin 5011) := {3040, 2965}" in text
    assert "refinedResidualIDs.card = 356" in text
    assert "EnergyTerminalResidualCensusRefine358.b13_remaining_of_residual358" in text
    OUTPUT.write_text(text)


if __name__ == "__main__":
    main()
