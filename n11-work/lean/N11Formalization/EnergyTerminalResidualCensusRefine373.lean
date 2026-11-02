import N11Formalization.EnergyTerminalResidualCensusRefine375
import N11Formalization.EnergyTerminalBatchB13Refine3794
import N11Formalization.EnergyTerminalBatchB13Refine3795

/-! Remove the CI-green 3794 and 3795 archive refinements from the 375-id
residual interface, leaving an exact residual of 373 ids. This module supplies
no new radius certificate beyond 3794 and 3795 and makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine373
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {3794, 3795}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine375.refinedResidualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_3794 : (3794 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_3795 : (3795 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem mem_375_3794 :
    (3794 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine375.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN3794.terminal
    | exact not_sharp_3794
    | exact EnergyTerminalBatchB13Refine3794.not_paid_3794
    | decide
    | constructor

private theorem mem_375_3795 :
    (3795 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine375.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN3795.terminal
    | exact not_sharp_3795
    | exact EnergyTerminalBatchB13Refine3795.not_paid_3795
    | decide
    | constructor

private theorem newRefineIDs_subset_375 : newRefineIDs ⊆
    EnergyTerminalResidualCensusRefine375.refinedResidualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · exact mem_375_3794
  · exact mem_375_3795

theorem newRefineIDs_card : newRefineIDs.card = 2 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 373 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_375,
    EnergyTerminalResidualCensusRefine375.refinedResidualIDs_card,
    newRefineIDs_card]
  norm_num

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine375.refinedResidualIDs ∧
        n ≠ 3794 ∧ n ≠ 3795 := by
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

theorem b13_remaining_of_residual373 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine375.b13_remaining_of_residual375
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn3794 : n = 3794
  · subst n
    exact (EnergyRefineN3794.new_radius 3794 (by simp [EnergyRefineN3794.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn3795 : n = 3795
    · subst n
      exact (EnergyRefineN3795.new_radius 3795 (by simp [EnergyRefineN3795.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn3794, hn3795⟩)
        y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine373
#check @N11Formalization.EnergyTerminalResidualCensusRefine373.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine373.b13_remaining_of_residual373
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine373.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine373.b13_remaining_of_residual373
