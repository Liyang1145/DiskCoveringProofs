#!/usr/bin/env python3
"""Repair or audit census decisions over open Fin terms."""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
TARGET = ROOT / "lean/N11Formalization/EnergyTerminalBatchB13RefineSixteenResidualCensus.lean"
OLD = """  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;>
      decide +kernel +revert"""
NEW = """  rcases n with ⟨k, hk⟩
  interval_cases k <;>
    change ((⟨k, by decide⟩ : Fin 5011) ∈
        EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔
      (⟨k, by decide⟩ : Fin 5011) ∈ residual373) <;>
    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;>
      decide +kernel"""

source = TARGET.read_text(encoding="utf-8")
check_only = "--check" in sys.argv[1:]
if not check_only:
    assert source.count(OLD) == 51, source.count(OLD)
    assert source.count("decide +kernel +revert") == 51
    source = source.replace(OLD, NEW)
    TARGET.write_text(source, encoding="utf-8")
assert source.count(NEW) == 51
assert source.count("decide +kernel +revert") == 0
assert source.count("  rcases n with ⟨k, hk⟩") == 51
print(f"{'checked' if check_only else 'repaired'}: blocks=51 "
      "closed_term_changes=51 kernel_revert=0")
