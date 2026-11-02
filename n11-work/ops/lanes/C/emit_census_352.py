#!/usr/bin/env python3
"""Emit the structural 354 -> 352 census bridge from the reviewed 356 source."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
SOURCE = LEAN / "EnergyTerminalResidualCensusRefine354.lean"
OUTPUT = LEAN / "EnergyTerminalResidualCensusRefine352.lean"


def main() -> None:
    text = SOURCE.read_text()
    replacements = (
        ("EnergyTerminalResidualCensusRefine354", "EnergyTerminalResidualCensusRefine352"),
        ("EnergyTerminalResidualCensusRefine356", "EnergyTerminalResidualCensusRefine354"),
        ("b13_remaining_of_residual354", "b13_remaining_of_residual352"),
        ("b13_remaining_of_residual356", "b13_remaining_of_residual354"),
        ("refinedResidualIDs.card = 354", "refinedResidualIDs.card = 352"),
        ("exact residual of 354 ids", "exact residual of 352 ids"),
        ("from the 356-id", "from the 354-id"),
        ("mem_356_", "mem_354_"),
        ("newRefineIDs_subset_356", "newRefineIDs_subset_354"),
        ("3440", "3589"),
        ("3520", "3623"),
    )
    for old, new in replacements:
        text = text.replace(old, new)
    assert "Refine356" not in text
    assert "3440" not in text and "3520" not in text
    assert "def newRefineIDs : Finset (Fin 5011) := {3589, 3623}" in text
    assert "refinedResidualIDs.card = 352" in text
    assert "EnergyTerminalResidualCensusRefine354.b13_remaining_of_residual354" in text
    OUTPUT.write_text(text)


if __name__ == "__main__":
    main()
