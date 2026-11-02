#!/usr/bin/env python3
"""Emit lane-B terminal-census Lean blocks from source data.

The emitted module is a census bridge only: it checks the finite terminal set and
its cardinality, and pays no residual radius.
"""
from __future__ import annotations

import hashlib
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
LEAN = ROOT / "n11-work/lean/N11Formalization"
OUT = LEAN / "EnergyTerminalBatchB13RefineSixteenTerminalCensus.lean"
BLOCK = 256


def terminal_ids() -> set[int]:
    text = (LEAN / "DBMSourceTreeData.lean").read_text(encoding="utf-8")
    pat = re.compile(
        r"def node(\d+) : Node 5011 where(.*?)(?=\ndef node\d+ : Node 5011 where|\ndef data)",
        re.S,
    )
    return {int(m.group(1)) for m in pat.finditer(text) if "terminal := true" in m.group(2)}


def main() -> None:
    ids = terminal_ids()
    blocks = [sorted(i for i in ids if i // BLOCK == b) for b in range((5011 + BLOCK - 1) // BLOCK)]
    assert len(ids) == sum(map(len, blocks)) == 2506
    lines = [
        "import N11Formalization.DBMSourceTreeData",
        "",
        "/-! Lane-B terminal census in bounded kernel blocks.",
        "",
        "Each chunk covers at most 256 source indices.  The per-chunk membership",
        "equivalence and cardinality are checked with `decide +kernel`; the top",
        "cardinality follows from `Finset.card_biUnion`.  This pays no radius. -/",
        "set_option autoImplicit false",
        "namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual",
        "open Finset",
        "noncomputable section",
        "",
        "def terminalIDs : Finset (Fin 5011) :=",
        "  Finset.univ.filter fun n => (DBMSourceTree.data n).terminal = true",
        "",
    ]
    for b, chunk in enumerate(blocks):
        off = b * BLOCK
        size = min(BLOCK, 5011 - off)
        lines += [
            f"def embed{b} (n : Fin {size}) : Fin 5011 := ⟨n.val + {off}, by omega⟩",
            f"def census{b} : Finset (Fin {size}) :=",
            f"  Finset.univ.filter fun n => (DBMSourceTree.data (embed{b} n)).terminal = true",
            "",
            f"theorem census{b}_spec (n : Fin {size}) :",
            f"    (DBMSourceTree.data (embed{b} n)).terminal = true ↔ n ∈ census{b} := by",
            f"  simp only [census{b}, Finset.mem_filter, Finset.mem_univ, true_and]",
            "",
            f"theorem census{b}_card : census{b}.card = {len(chunk)} := by",
            "  decide +kernel",
            "",
            f"def blockIDs{b} : Finset (Fin 5011) := census{b}.image embed{b}",
            "",
            f"theorem blockIDs{b}_card : blockIDs{b}.card = {len(chunk)} := by",
            f"  rw [blockIDs{b}, Finset.card_image_of_injective _ ?_, census{b}_card]",
            "  intro x y h",
            f"  apply Fin.ext",
            f"  have := congrArg Fin.val h",
            f"  simp [embed{b}] at this ⊢",
            "  omega",
            "",
        ]
        if b < len(blocks) - 1:
            lines += [
                f"theorem blockIDs{b}_upper : blockIDs{b} ⊆",
                f"    Finset.univ.filter (fun n : Fin 5011 => n.val < {off + size}) := by",
                f"  intro n hn",
                f"  rw [blockIDs{b}, Finset.mem_image] at hn",
                "  rcases hn with ⟨m, _, rfl⟩",
                f"  simp [embed{b}] <;> omega",
            ]
        lines += [
            f"theorem blockIDs{b}_lower : blockIDs{b} ⊆",
            f"    Finset.univ.filter (fun n : Fin 5011 => {off} ≤ n.val) := by",
            f"  intro n hn",
            f"  rw [blockIDs{b}, Finset.mem_image] at hn",
            "  rcases hn with ⟨m, _, rfl⟩",
            f"  simp [embed{b}] <;> omega",
            "",
            f"theorem block_mem{b} {{n : Fin 5011}} (ht : (DBMSourceTree.data n).terminal = true)",
            f"    (hlo : {off} ≤ n.val) (hhi : n.val < {off + size}) : n ∈ blockIDs{b} := by",
            f"  refine Finset.mem_image.mpr ⟨⟨n.val - {off}, by omega⟩, ?_, ?_⟩",
            f"  · exact (census{b}_spec _).mp (by",
            f"      have he : embed{b} ⟨n.val - {off}, by omega⟩ = n := by ext; simp [embed{b}] <;> omega",
            "      simpa [he] using ht)",
            f"  · ext; simp [embed{b}] <;> omega",
            "",
            f"theorem block_terminal{b} {{n : Fin 5011}} (hn : n ∈ blockIDs{b}) :",
            "    (DBMSourceTree.data n).terminal = true := by",
            f"  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩",
            f"  exact (census{b}_spec m).mpr hm",
            "",
        ]
        if b < len(blocks) - 1:
            lines += [
                f"theorem blockIDs{b}_interval : blockIDs{b} ⊆",
                f"    Finset.univ.filter (fun n : Fin 5011 => {off} ≤ n.val ∧ n.val < {off + size}) := by",
                "  intro n hn",
                f"  have hu := blockIDs{b}_upper hn",
                f"  have hl := blockIDs{b}_lower hn",
                "  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢",
                "  exact ⟨hl, hu⟩",
                "",
            ]
        else:
            lines += [
                f"theorem blockIDs{b}_interval : blockIDs{b} ⊆",
                f"    Finset.univ.filter (fun n : Fin 5011 => {off} ≤ n.val ∧ n.val < {off + BLOCK}) := by",
                "  intro n hn",
                f"  have hl := blockIDs{b}_lower hn",
                "  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢",
                "  exact ⟨hl, by omega⟩",
                "",
            ]
    part = ",\n    ".join(f"blockIDs{i}" for i in range(len(blocks)))
    lines += [
        f"def blockIDs : Fin {len(blocks)} → Finset (Fin 5011) := ![{part}]",
        "",
        f"theorem blockIDs_interval (i : Fin {len(blocks)}) :",
        "    blockIDs i ⊆ Finset.univ.filter",
        "      (fun n : Fin 5011 => i.val * 256 ≤ n.val ∧ n.val < i.val * 256 + 256) := by",
        "  fin_cases i",
    ]
    lines += [f"  · simpa [blockIDs] using blockIDs{b}_interval" for b in range(len(blocks))]
    lines += [
        "",
        "def censusIDs : Finset (Fin 5011) := Finset.univ.biUnion blockIDs",
        "",
        "theorem terminalIDs_eq_censusIDs : terminalIDs = censusIDs := by",
        "  ext n",
        "  constructor",
        "  · intro hn",
        "    simp only [terminalIDs, Finset.mem_filter, Finset.mem_univ, true_and] at hn",
    ]
    for b in range(len(blocks)):
        off = b * BLOCK
        size = min(BLOCK, 5011 - off)
        opener = "    by_cases h" + str(b) + f" : n.val < {off + size}"
        lines.append(opener)
        if b == 0:
            lines += [
                "    · rw [censusIDs, Finset.mem_biUnion]",
                "      refine ⟨⟨0, by decide⟩, Finset.mem_univ _, ?_⟩",
                "      simpa [blockIDs] using block_mem0 hn (by omega) h0",
            ]
        else:
            lines += [
                "    · rw [censusIDs, Finset.mem_biUnion]",
                f"      refine ⟨⟨{b}, by decide⟩, Finset.mem_univ _, ?_⟩",
                f"      simpa [blockIDs] using block_mem{b} hn (by omega) h{b}",
            ]
    lines += [
        "    · omega",
        "  · intro hn",
        "    rw [censusIDs, Finset.mem_biUnion] at hn",
        "    rcases hn with ⟨i, _, hi⟩",
        "    fin_cases i",
    ]
    lines += [f"    · exact block_terminal{b} hi" for b in range(len(blocks))]
    lines += [
        "",
        "theorem blockIDs_pairwiseDisjoint :",
        "    ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j → Disjoint (blockIDs i) (blockIDs j) := by",
        "  intro i _ j _ hij",
        "  rw [Finset.disjoint_left]",
        "  intro n hi hj",
        "  have hi' := blockIDs_interval i hi",
        "  have hj' := blockIDs_interval j hj",
        "  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'",
        "  have hvals : i.val < j.val ∨ j.val < i.val := by",
        "    have hne : i.val ≠ j.val := by",
        "      intro h",
        "      exact hij (Fin.ext h)",
        "    exact Nat.lt_or_gt_of_ne hne",
        "  omega",
        "",
        "theorem censusIDs_card : censusIDs.card = 2506 := by",
        "  rw [censusIDs, Finset.card_biUnion blockIDs_pairwiseDisjoint]",
        "  simp [Fin.sum_univ_succ, Fin.sum_univ_zero, blockIDs," + ", ".join(f"blockIDs{i}_card" for i in range(len(blocks))) + "]",
        "  norm_num",
        "",
        "theorem terminalIDs_card : terminalIDs.card = 2506 := by",
        "  rw [terminalIDs_eq_censusIDs, censusIDs_card]",
        "",
        "end",
        "end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual",
        "",
    ]
    rendered = "\n".join(lines)
    assert all(len(chunk) <= BLOCK for chunk in blocks)
    assert all(
        f"def census{b} : Finset (Fin {min(BLOCK, 5011 - b * BLOCK)}) :=\n"
        f"  Finset.univ.filter fun n => "
        f"(DBMSourceTree.data (embed{b} n)).terminal = true" in rendered
        for b in range(len(blocks))
    )
    assert all(
        f"theorem census{b}_spec (n : Fin {min(BLOCK, 5011 - b * BLOCK)}) :\n"
        f"    (DBMSourceTree.data (embed{b} n)).terminal = true ↔ n ∈ census{b} := by\n"
        f"  simp only [census{b}, Finset.mem_filter, Finset.mem_univ, true_and]"
        in rendered
        for b in range(len(blocks))
    )
    assert rendered.count("  decide +kernel") == len(blocks)
    assert not any(tok in rendered for tok in
                   ("sorry", "admit", "native_decide", "implemented_by", "maxHeartbeats 0"))
    OUT.write_text(rendered, encoding="utf-8")
    print(OUT)
    print(len(lines), "lines", len(ids), "terminals", "sha256", hashlib.sha256(OUT.read_bytes()).hexdigest().upper())


if __name__ == "__main__":
    main()
