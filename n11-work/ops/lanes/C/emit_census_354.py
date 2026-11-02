#!/usr/bin/env python3
"""Emit the structural 356 -> 354 census bridge from the reviewed 356 source."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
SOURCE = LEAN / "EnergyTerminalResidualCensusRefine356.lean"
OUTPUT = LEAN / "EnergyTerminalResidualCensusRefine354.lean"


def main() -> None:
    text = SOURCE.read_text()
    replacements = (
        ("EnergyTerminalResidualCensusRefine356", "EnergyTerminalResidualCensusRefine354"),
        ("EnergyTerminalResidualCensusRefine358", "EnergyTerminalResidualCensusRefine356"),
        ("b13_remaining_of_residual356", "b13_remaining_of_residual354"),
        ("b13_remaining_of_residual358", "b13_remaining_of_residual356"),
        ("refinedResidualIDs.card = 356", "refinedResidualIDs.card = 354"),
        ("exact residual of 356 ids", "exact residual of 354 ids"),
        ("from the 358-id", "from the 356-id"),
        ("mem_358_", "mem_356_"),
        ("newRefineIDs_subset_358", "newRefineIDs_subset_356"),
        ("3040", "3440"),
        ("2965", "3520"),
    )
    for old, new in replacements:
        text = text.replace(old, new)
    assert "Refine358" not in text
    assert "3040" not in text and "2965" not in text
    assert "def newRefineIDs : Finset (Fin 5011) := {3440, 3520}" in text
    assert "refinedResidualIDs.card = 354" in text
    assert "EnergyTerminalResidualCensusRefine356.b13_remaining_of_residual356" in text
    OUTPUT.write_text(text)


if __name__ == "__main__":
    main()
