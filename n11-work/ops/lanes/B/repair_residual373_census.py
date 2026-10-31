#!/usr/bin/env python3
"""Repair the 373-id census block tactic from the CI timeout diagnostics."""
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
TARGET = ROOT / "lean/N11Formalization/EnergyTerminalBatchB13RefineSixteenResidualCensus.lean"
OLD_TACTIC = """    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;>\n      simp [residual373, chunk0, chunk1, chunk2, chunk3]"""
NEW_TACTIC = """    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;>\n      decide +kernel +revert"""
OLD_MP = "(residualIDs_eq_residual373).mp hn"
NEW_MP = "(by simpa [residualIDs_eq_residual373] using hn)"
source = TARGET.read_text(encoding="utf-8")
assert source.count(OLD_TACTIC) == 51
assert source.count(OLD_MP) == 2
source = source.replace(OLD_TACTIC, NEW_TACTIC).replace(OLD_MP, NEW_MP)
assert source.count("decide +kernel +revert") == 51
TARGET.write_text(source, encoding="utf-8")
print("repaired: blocks=51 membership_rewrites=2")
