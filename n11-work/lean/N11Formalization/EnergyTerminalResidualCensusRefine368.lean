import N11Formalization.EnergyTerminalResidualCensusRefine371
import N11Formalization.EnergyTerminalBatchB13Refine3979
import N11Formalization.EnergyTerminalBatchB13Refine3865
import N11Formalization.EnergyTerminalBatchB13Refine4684

/-! Remove the CI-green 3979, 3865, and 4684 archive refinements from the
371-id residual interface, leaving an exact residual of 368 ids. This module
supplies no new radius certificate beyond those three and makes no payment
claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine368
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {3979, 3865, 4684}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine371.refinedResidualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_3979 : (3979 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_3865 : (3865 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_4684 : (4684 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem mem_371_3979 :
    (3979 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine371.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine371.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine373.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN3979.terminal
    | exact not_sharp_3979
    | exact EnergyTerminalBatchB13Refine3979.not_paid_3979
    | decide
    | constructor

private theorem mem_371_3865 :
    (3865 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine371.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine371.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine373.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN3865.terminal
    | exact not_sharp_3865
    | exact EnergyTerminalBatchB13Refine3865.not_paid_3865
    | decide
    | constructor

private theorem mem_371_4684 :
    (4684 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine371.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine371.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine373.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN4684.terminal
    | exact not_sharp_4684
    | exact EnergyTerminalBatchB13Refine4684.not_paid_4684
    | decide
    | constructor

private theorem newRefineIDs_subset_371 : newRefineIDs ⊆
    EnergyTerminalResidualCensusRefine371.refinedResidualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl
  · exact mem_371_3979
  · exact mem_371_3865
  · exact mem_371_4684

theorem newRefineIDs_card : newRefineIDs.card = 3 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 368 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_371,
    EnergyTerminalResidualCensusRefine371.refinedResidualIDs_card,
    newRefineIDs_card]
  norm_num

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine371.refinedResidualIDs ∧
        n ≠ 3979 ∧ n ≠ 3865 ∧ n ≠ 4684 := by
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

theorem b13_remaining_of_residual368 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine371.b13_remaining_of_residual371
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn3979 : n = 3979
  · subst n
    exact (EnergyRefineN3979.new_radius 3979 (by simp [EnergyRefineN3979.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn3865 : n = 3865
    · subst n
      exact (EnergyRefineN3865.new_radius 3865 (by simp [EnergyRefineN3865.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · by_cases hn4684 : n = 4684
      · subst n
        exact (EnergyRefineN4684.new_radius 4684 (by simp [EnergyRefineN4684.newIDs])
          y hy0 hy1 hc C Z r hf).le
      · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn3979, hn3865, hn4684⟩)
          y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine368
#check @N11Formalization.EnergyTerminalResidualCensusRefine368.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine368.b13_remaining_of_residual368
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine368.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine368.b13_remaining_of_residual368
