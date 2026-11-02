#!/usr/bin/env python3
"""Emit the structural 350 -> 348 census bridge from the reviewed 350 source."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
SOURCE = LEAN / "EnergyTerminalResidualCensusRefine350.lean"
OUTPUT = LEAN / "EnergyTerminalResidualCensusRefine348.lean"


def main() -> None:
    text = SOURCE.read_text()
    replacements = (
        ("EnergyTerminalResidualCensusRefine350", "EnergyTerminalResidualCensusRefine348"),
        ("EnergyTerminalResidualCensusRefine352", "EnergyTerminalResidualCensusRefine350"),
        ("b13_remaining_of_residual350", "b13_remaining_of_residual348"),
        ("b13_remaining_of_residual352", "b13_remaining_of_residual350"),
        ("refinedResidualIDs.card = 350", "refinedResidualIDs.card = 348"),
        ("exact residual of 350 ids", "exact residual of 348 ids"),
        ("from the 352-id", "from the 350-id"),
        ("mem_352_", "mem_350_"),
        ("newRefineIDs_subset_352", "newRefineIDs_subset_350"),
        ("3802", "3810"),
        ("3807", "3863"),
    )
    for old, new in replacements:
        text = text.replace(old, new)
    assert "Refine352" not in text
    assert "3802" not in text and "3807" not in text
    assert "def newRefineIDs : Finset (Fin 5011) := {3810, 3863}" in text
    assert "refinedResidualIDs.card = 348" in text
    assert "EnergyTerminalResidualCensusRefine350.b13_remaining_of_residual350" in text
    OUTPUT.write_text(text)


if __name__ == "__main__":
    main()
