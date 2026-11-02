#!/usr/bin/env python3
"""Emit the 348 -> 346 census bridge for repaired low ids 39 and 40."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
OUTPUT = LEAN / "EnergyTerminalResidualCensusRefine346.lean"

CHAIN = """    EnergyTerminalResidualCensusRefine350.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine352.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine354.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine356.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine358.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine360.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine362.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine364.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine366.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine368.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine371.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine373.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff"""


def member_block(i: int, module: str, batch: str, paid: str) -> str:
    return f"""private theorem mem_350_{i} :
    ({i} : Fin 5011) ∈ EnergyTerminalResidualCensusRefine350.refinedResidualIDs := by
  rw [
{CHAIN}]
  repeat' first
    | exact {module}.terminal
    | exact not_sharp_{i}
    | exact {batch}.{paid}
    | decide
    | constructor

private theorem mem_348_{i} :
    ({i} : Fin 5011) ∈ EnergyTerminalResidualCensusRefine348.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine348.mem_refinedResidualIDs_iff]
  exact ⟨mem_350_{i}, by decide, by decide⟩
"""


TEXT = f"""import N11Formalization.EnergyTerminalResidualCensusRefine348
import N11Formalization.EnergyTerminalBatchB13Refine0039
import N11Formalization.EnergyTerminalBatchB13Refine40

/-! Remove repaired archive refinements 39 and 40 from the 348-id residual
interface, leaving an exact residual of 346 ids. This module supplies no radius
certificate beyond those two wrappers and makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine346
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {{39, 40}}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine348.refinedResidualIDs \\ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_39 : (39 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_40 : (40 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

{member_block(39, 'EnergyRefineN0039', 'EnergyTerminalBatchB13Refine0039', 'not_paid_0039')}
{member_block(40, 'EnergyRefineN0040', 'EnergyTerminalBatchB13Refine40', 'not_paid_40')}
private theorem newRefineIDs_subset_348 : newRefineIDs ⊆
    EnergyTerminalResidualCensusRefine348.refinedResidualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · exact mem_348_39
  · exact mem_348_40

theorem newRefineIDs_card : newRefineIDs.card = 2 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 346 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_348,
    EnergyTerminalResidualCensusRefine348.refinedResidualIDs_card,
    newRefineIDs_card]
  norm_num

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine348.refinedResidualIDs ∧
        n ≠ 39 ∧ n ≠ 40 := by
  rw [refinedResidualIDs, Finset.mem_sdiff, newRefineIDs,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011, n ∈ refinedResidualIDs →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r →
          SourceExactRoot.sourceRadius ≤ r

theorem remaining_of_radius_certificates
    (h : ∀ n, n ∈ refinedResidualIDs →
      EnergyTerminalBatchB13.ResidualRadiusCertificate n) :
    RemainingTerminalRadius := by
  intro n hn y hy0 hy1 hc C Z r hf
  exact (h n hn).radius y hy0 hy1 hc C Z r hf

theorem b13_remaining_of_residual346 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine348.b13_remaining_of_residual348
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn39 : n = 39
  · subst n
    exact (EnergyRefineN0039.new_radius 39 (by simp [EnergyRefineN0039.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn40 : n = 40
    · subst n
      exact (EnergyRefineN0040.new_radius 40 (by simp [EnergyRefineN0040.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn39, hn40⟩)
        y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine346
#check @N11Formalization.EnergyTerminalResidualCensusRefine346.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine346.b13_remaining_of_residual346
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine346.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine346.b13_remaining_of_residual346
"""


def main() -> None:
    OUTPUT.write_text(TEXT)


if __name__ == "__main__":
    main()
