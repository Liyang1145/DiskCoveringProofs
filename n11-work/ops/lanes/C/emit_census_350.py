#!/usr/bin/env python3
"""Emit the structural 352 -> 350 census bridge from the reviewed 352 source."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
SOURCE = LEAN / "EnergyTerminalResidualCensusRefine352.lean"
OUTPUT = LEAN / "EnergyTerminalResidualCensusRefine350.lean"


def main() -> None:
    text = SOURCE.read_text()
    replacements = (
        ("EnergyTerminalResidualCensusRefine352", "EnergyTerminalResidualCensusRefine350"),
        ("EnergyTerminalResidualCensusRefine354", "EnergyTerminalResidualCensusRefine352"),
        ("b13_remaining_of_residual352", "b13_remaining_of_residual350"),
        ("b13_remaining_of_residual354", "b13_remaining_of_residual352"),
        ("refinedResidualIDs.card = 352", "refinedResidualIDs.card = 350"),
        ("exact residual of 352 ids", "exact residual of 350 ids"),
        ("from the 354-id", "from the 352-id"),
        ("mem_354_", "mem_352_"),
        ("newRefineIDs_subset_354", "newRefineIDs_subset_352"),
        ("3589", "3802"),
        ("3623", "3807"),
    )
    for old, new in replacements:
        text = text.replace(old, new)
    assert "Refine354" not in text
    assert "3589" not in text and "3623" not in text
    assert "def newRefineIDs : Finset (Fin 5011) := {3802, 3807}" in text
    assert "refinedResidualIDs.card = 350" in text
    assert "EnergyTerminalResidualCensusRefine352.b13_remaining_of_residual352" in text
    OUTPUT.write_text(text)


if __name__ == "__main__":
    main()
