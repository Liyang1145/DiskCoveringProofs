#!/usr/bin/env python3
"""Emit a structurally split proof for the restored N39 certificate.

The archive certificate bytes remain untouched.  This emitter only replaces the
monolithic, backtracking `pk_ok` tactic block, which CI showed timing out at
`EnergyRefineN0039.lean:48`, with explicit cases for the 13 vector entries.
False terminal branches use definitional reduction and the core
`Bool.false_ne_true` lemma, so the repaired theorem performs no kernel decision.
"""
import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = ROOT / "n11-work/lean/N11Formalization/EnergyRefineN0039.lean"
OUTPUT = ROOT / "n11-work/lean/N11Formalization/EnergyRefineN0039Repair.lean"
SOURCE_SHA256 = "5bbe2fdb17bff213685e3eab77e0ee35267aa2b54a8e0a8fc914599f45f29a3d"

OLD = """theorem pk_ok : ∀ l, (sub l).terminal = true → MValid (pk l) ∧ (pk l).D = (sub l).db ∧ (pk l).S = 1048576 := by
  intro l hl
  fin_cases l <;> first | exact absurd hl (by decide +kernel) | exact ⟨valid3, rfl, rfl⟩ | exact ⟨valid4, rfl, rfl⟩ | exact ⟨valid5, rfl, rfl⟩ | exact ⟨valid9, rfl, rfl⟩ | exact ⟨valid10, rfl, rfl⟩ | exact ⟨valid11, rfl, rfl⟩ | exact ⟨valid12, rfl, rfl⟩
"""

NEW = """theorem pk_ok : ∀ l, (sub l).terminal = true → MValid (pk l) ∧ (pk l).D = (sub l).db ∧ (pk l).S = 1048576 := by
  intro l hl
  fin_cases l
  · exact Bool.false_ne_true hl
  · exact Bool.false_ne_true hl
  · exact Bool.false_ne_true hl
  · exact ⟨valid3, rfl, rfl⟩
  · exact ⟨valid4, rfl, rfl⟩
  · exact ⟨valid5, rfl, rfl⟩
  · exact Bool.false_ne_true hl
  · exact Bool.false_ne_true hl
  · exact Bool.false_ne_true hl
  · exact ⟨valid9, rfl, rfl⟩
  · exact ⟨valid10, rfl, rfl⟩
  · exact ⟨valid11, rfl, rfl⟩
  · exact ⟨valid12, rfl, rfl⟩
"""


def main() -> None:
    source_bytes = SOURCE.read_bytes()
    actual = hashlib.sha256(source_bytes).hexdigest()
    if actual != SOURCE_SHA256:
        raise SystemExit(f"unexpected source hash: {actual}")
    source = source_bytes.decode("utf-8")
    if source.count(OLD) != 1:
        raise SystemExit("expected exactly one monolithic pk_ok block")
    output = source.replace(OLD, NEW, 1)
    OUTPUT.write_text(output, encoding="utf-8")
    print(OUTPUT)
    print("sha256", hashlib.sha256(OUTPUT.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
