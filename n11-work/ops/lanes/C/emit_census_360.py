#!/usr/bin/env python3
"""Emit the structural 362 -> 360 census bridge from the reviewed 362 source."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
SOURCE = LEAN / "EnergyTerminalResidualCensusRefine362.lean"
OUTPUT = LEAN / "EnergyTerminalResidualCensusRefine360.lean"


def main() -> None:
    text = SOURCE.read_text()
    replacements = (
        ("EnergyTerminalResidualCensusRefine362", "EnergyTerminalResidualCensusRefine360"),
        ("b13_remaining_of_residual362", "b13_remaining_of_residual360"),
        ("refinedResidualIDs.card = 362", "refinedResidualIDs.card = 360"),
        ("exact residual of 362 ids", "exact residual of 360 ids"),
        ("Refine364", "Refine362"),
        ("b13_remaining_of_residual364", "b13_remaining_of_residual362"),
        ("mem_364_", "mem_362_"),
        ("364-id", "362-id"),
        ("3522", "3808"),
        ("3783", "3821"),
    )
    for old, new in replacements:
        text = text.replace(old, new)
    assert "3522" not in text and "3783" not in text
    assert "Refine364" not in text and "mem_364_" not in text
    assert "def newRefineIDs : Finset (Fin 5011) := {3808, 3821}" in text
    assert "refinedResidualIDs.card = 360" in text
    assert "EnergyTerminalResidualCensusRefine362.b13_remaining_of_residual362" in text
    OUTPUT.write_text(text)


if __name__ == "__main__":
    main()
