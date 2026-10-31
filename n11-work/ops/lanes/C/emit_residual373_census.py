#!/usr/bin/env python3
"""Emit the conditional 373-id Lean census from the committed exact JSON."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SRC = HERE / "residual373-conditional-census.json"
OUT = ROOT / "n11-work/lean/N11Formalization/EnergyTerminalBatchB13RefineSixteenResidualCensus.lean"


def main():
    data = json.loads(SRC.read_text())
    ids = data["residual_ids"]
    assert len(ids) == 373 and len(set(ids)) == 373
    chunks = [ids[i:i + 100] for i in range(0, len(ids), 100)]
    assert [len(c) for c in chunks] == [100, 100, 100, 73]
    base = ROOT / "n11-work/lean/N11Formalization/EnergyTerminalResidualCensusBase.lean"
    assert base.is_file()
    lines = [
        "import N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual",
        "",
        "/-! Exact conditional census after the sixteen-refinement repair: 373",
        "terminal ids remain.  The four literal chunks keep kernel decisions below",
        "the measured size guard; the equality proof is split into 100-index",
        "source blocks.  This module proves cardinality only, not radius payment. -/",
        "set_option autoImplicit false",
        "set_option maxRecDepth 10000",
        "namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus",
        "open Finset",
        "noncomputable section",
        "",
    ]
    for i, chunk in enumerate(chunks):
        body = ",".join(map(str, chunk))
        lines += [f"def chunk{i} : Finset (Fin 5011) := {{{body}}}",
                  f"theorem chunk{i}_card : chunk{i}.card = {len(chunk)} := by decide +kernel"]
    lines += ["", "def residual373 : Finset (Fin 5011) :=",
              "  chunk0 ∪ (chunk1 ∪ (chunk2 ∪ chunk3))", ""]
    for i in range(4):
        for j in range(i + 1, 4):
            lines.append(f"private theorem disjoint_chunk{i}_{j} : Disjoint chunk{i} chunk{j} := by decide +kernel")
    lines += [
        "private theorem disjoint_chunk1_23 : Disjoint chunk1 (chunk2 ∪ chunk3) :=",
        "  disjoint_union_right.mpr ⟨disjoint_chunk1_2, disjoint_chunk1_3⟩",
        "private theorem disjoint_chunk0_123 :",
        "    Disjoint chunk0 (chunk1 ∪ (chunk2 ∪ chunk3)) :=",
        "  disjoint_union_right.mpr ⟨disjoint_chunk0_1, disjoint_union_right.mpr",
        "    ⟨disjoint_chunk0_2, disjoint_chunk0_3⟩⟩",
        "private theorem card_chunks : residual373.card = 373 := by",
        "  rw [residual373, card_union_of_disjoint disjoint_chunk0_123,",
        "    card_union_of_disjoint disjoint_chunk1_23, card_union_of_disjoint disjoint_chunk2_3,",
        "    chunk0_card, chunk1_card, chunk2_card, chunk3_card]",
        "  norm_num",
        "",
    ]
    blocks = []
    for lo in range(0, 5000, 100):
        hi = lo + 100
        name = f"block{lo // 100:02d}"
        blocks.append(name)
        lines += [f"theorem mem_iff_{name} (n : Fin 5011)",
                  f"    (hlo : {lo} ≤ n.val) (hhi : n.val < {hi}) :",
                  "    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔",
                  "      n ∈ residual373 := by",
                  "  rcases n with ⟨k, hk⟩",
                  "  interval_cases k <;>",
                  "    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;>",
                  "      simp [residual373, chunk0, chunk1, chunk2, chunk3]", ""]
    lines += [f"theorem mem_iff_block50 (n : Fin 5011) (hlo : 5000 ≤ n.val) :",
              "    n ∈ EnergyTerminalBatchB13RefineSixteenResidual.residualIDs ↔",
              "      n ∈ residual373 := by",
              "  rcases n with ⟨k, hk⟩",
              "  interval_cases k <;>",
              "    rw [EnergyTerminalBatchB13RefineSixteenResidual.mem_residualIDs_iff] <;>",
              "      simp [residual373, chunk0, chunk1, chunk2, chunk3]", ""]
    lines += ["theorem residualIDs_eq_residual373 :",
              "    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs = residual373 := by",
              "  ext n",
              "  have hcover : n.val < 100 ∨ (100 ≤ n.val ∧ n.val < 200) ∨ "
              "(200 ≤ n.val ∧ n.val < 300) ∨ (300 ≤ n.val ∧ n.val < 400) ∨ "
              "(400 ≤ n.val ∧ n.val < 500) ∨ (500 ≤ n.val ∧ n.val < 600) ∨ "
              "(600 ≤ n.val ∧ n.val < 700) ∨ (700 ≤ n.val ∧ n.val < 800) ∨ "
              "(800 ≤ n.val ∧ n.val < 900) ∨ (900 ≤ n.val ∧ n.val < 1000) ∨ "
              "(1000 ≤ n.val ∧ n.val < 1100) ∨ (1100 ≤ n.val ∧ n.val < 1200) ∨ "
              "(1200 ≤ n.val ∧ n.val < 1300) ∨ (1300 ≤ n.val ∧ n.val < 1400) ∨ "
              "(1400 ≤ n.val ∧ n.val < 1500) ∨ (1500 ≤ n.val ∧ n.val < 1600) ∨ "
              "(1600 ≤ n.val ∧ n.val < 1700) ∨ (1700 ≤ n.val ∧ n.val < 1800) ∨ "
              "(1800 ≤ n.val ∧ n.val < 1900) ∨ (1900 ≤ n.val ∧ n.val < 2000) ∨ "
              "(2000 ≤ n.val ∧ n.val < 2100) ∨ (2100 ≤ n.val ∧ n.val < 2200) ∨ "
              "(2200 ≤ n.val ∧ n.val < 2300) ∨ (2300 ≤ n.val ∧ n.val < 2400) ∨ "
              "(2400 ≤ n.val ∧ n.val < 2500) ∨ (2500 ≤ n.val ∧ n.val < 2600) ∨ "
              "(2600 ≤ n.val ∧ n.val < 2700) ∨ (2700 ≤ n.val ∧ n.val < 2800) ∨ "
              "(2800 ≤ n.val ∧ n.val < 2900) ∨ (2900 ≤ n.val ∧ n.val < 3000) ∨ "
              "(3000 ≤ n.val ∧ n.val < 3100) ∨ (3100 ≤ n.val ∧ n.val < 3200) ∨ "
              "(3200 ≤ n.val ∧ n.val < 3300) ∨ (3300 ≤ n.val ∧ n.val < 3400) ∨ "
              "(3400 ≤ n.val ∧ n.val < 3500) ∨ (3500 ≤ n.val ∧ n.val < 3600) ∨ "
              "(3600 ≤ n.val ∧ n.val < 3700) ∨ (3700 ≤ n.val ∧ n.val < 3800) ∨ "
              "(3800 ≤ n.val ∧ n.val < 3900) ∨ (3900 ≤ n.val ∧ n.val < 4000) ∨ "
              "(4000 ≤ n.val ∧ n.val < 4100) ∨ (4100 ≤ n.val ∧ n.val < 4200) ∨ "
              "(4200 ≤ n.val ∧ n.val < 4300) ∨ (4300 ≤ n.val ∧ n.val < 4400) ∨ "
              "(4400 ≤ n.val ∧ n.val < 4500) ∨ (4500 ≤ n.val ∧ n.val < 4600) ∨ "
              "(4600 ≤ n.val ∧ n.val < 4700) ∨ (4700 ≤ n.val ∧ n.val < 4800) ∨ "
              "(4800 ≤ n.val ∧ n.val < 4900) ∨ (4900 ≤ n.val ∧ n.val < 5000) ∨ "
              "5000 ≤ n.val := by omega"]
    branches = [f"  · exact mem_iff_block{lo // 100:02d} n {lo} ({lo + 100})".replace(
        f"({lo + 100})", f"h{lo // 100}") for lo in range(0, 5000, 100)]
    lines += ["  rcases hcover with " + " | ".join(f"h{i}" for i in range(51))]
    for lo in range(0, 5000, 100):
        i = lo // 100
        if lo == 0:
            lines.append(f"  · exact mem_iff_block00 n (Nat.zero_le _) h0")
        else:
            lines.append(f"  · exact mem_iff_block{i:02d} n h{i}.1 h{i}.2")
    lines += ["  · exact mem_iff_block50 n h50", "",
              "theorem residualIDs_card :",
              "    EnergyTerminalBatchB13RefineSixteenResidual.residualIDs.card = 373 := by",
              "  rw [residualIDs_eq_residual373, card_chunks]",
              "",
              "theorem remaining_of_residual373_radius_certificates",
              "    (h : ∀ n, n ∈ residual373 →",
              "      EnergyTerminalBatchB13.ResidualRadiusCertificate n) :",
              "    EnergyTerminalBatchB13RefineSixteenRepair.RemainingTerminalRadius :=",
              "  EnergyTerminalBatchB13RefineSixteenResidual.remaining_of_residual_radius_certificates",
              "    (fun n hn => h n ((residualIDs_eq_residual373).mp hn))",
              "",
              "theorem b13_remaining_of_residual373_radius_certificates",
              "    (h : ∀ n, n ∈ residual373 →",
              "      EnergyTerminalBatchB13.ResidualRadiusCertificate n) :",
              "    EnergyTerminalBatchB13.RemainingTerminalRadius :=",
              "  EnergyTerminalBatchB13RefineSixteenResidual.b13_remaining_of_residual_radius_certificates",
              "    (fun n hn => h n ((residualIDs_eq_residual373).mp hn))",
              "end", "end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus",
              "#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.residualIDs_card",
              "#check @N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.b13_remaining_of_residual373_radius_certificates",
              "#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.residualIDs_card",
              "#print axioms N11Formalization.EnergyTerminalBatchB13RefineSixteenResidualCensus.b13_remaining_of_residual373_radius_certificates"]
    OUT.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT} ({len(lines)} lines, {len(ids)} ids)")


if __name__ == "__main__":
    main()
