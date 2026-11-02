import N11Formalization.EnergyTerminalResidualCensusRefine373
import N11Formalization.EnergyTerminalBatchB13Refine3800
import N11Formalization.EnergyTerminalBatchB13Refine3803

/-! Remove the CI-green 3800 and 3803 archive refinements from the 373-id
residual interface, leaving an exact residual of 371 ids. This module supplies
no new radius certificate beyond 3800 and 3803 and makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine371
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {3800, 3803}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine373.refinedResidualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_3800 : (3800 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_3803 : (3803 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem mem_373_3800 :
    (3800 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine373.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine373.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN3800.terminal
    | exact not_sharp_3800
    | exact EnergyTerminalBatchB13Refine3800.not_paid_3800
    | decide
    | constructor

private theorem mem_373_3803 :
    (3803 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine373.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine373.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN3803.terminal
    | exact not_sharp_3803
    | exact EnergyTerminalBatchB13Refine3803.not_paid_3803
    | decide
    | constructor

private theorem newRefineIDs_subset_373 : newRefineIDs ⊆
    EnergyTerminalResidualCensusRefine373.refinedResidualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · exact mem_373_3800
  · exact mem_373_3803

theorem newRefineIDs_card : newRefineIDs.card = 2 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 371 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_373,
    EnergyTerminalResidualCensusRefine373.refinedResidualIDs_card,
    newRefineIDs_card]
  norm_num

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine373.refinedResidualIDs ∧
        n ≠ 3800 ∧ n ≠ 3803 := by
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

theorem b13_remaining_of_residual371 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine373.b13_remaining_of_residual373
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn3800 : n = 3800
  · subst n
    exact (EnergyRefineN3800.new_radius 3800 (by simp [EnergyRefineN3800.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn3803 : n = 3803
    · subst n
      exact (EnergyRefineN3803.new_radius 3803 (by simp [EnergyRefineN3803.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn3800, hn3803⟩)
        y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine371
#check @N11Formalization.EnergyTerminalResidualCensusRefine371.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine371.b13_remaining_of_residual371
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine371.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine371.b13_remaining_of_residual371
