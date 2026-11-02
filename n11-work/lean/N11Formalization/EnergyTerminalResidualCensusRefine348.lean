import N11Formalization.EnergyTerminalResidualCensusRefine350
import N11Formalization.EnergyTerminalBatchB13Refine3810
import N11Formalization.EnergyTerminalBatchB13Refine3863

/-! Remove the CI-green 3810 and 3863 archive refinements from the 350-id
residual interface, leaving an exact residual of 348 ids. This module supplies
no new radius certificate beyond those two and makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine348
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {3810, 3863}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine350.refinedResidualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_3810 : (3810 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_3863 : (3863 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem mem_350_3810 :
    (3810 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine350.refinedResidualIDs := by
  rw [
    EnergyTerminalResidualCensusRefine350.mem_refinedResidualIDs_iff,
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
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN3810.terminal
    | exact not_sharp_3810
    | exact EnergyTerminalBatchB13Refine3810.not_paid_3810
    | decide
    | constructor

private theorem mem_350_3863 :
    (3863 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine350.refinedResidualIDs := by
  rw [
    EnergyTerminalResidualCensusRefine350.mem_refinedResidualIDs_iff,
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
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN3863.terminal
    | exact not_sharp_3863
    | exact EnergyTerminalBatchB13Refine3863.not_paid_3863
    | decide
    | constructor

private theorem newRefineIDs_subset_350 : newRefineIDs ⊆
    EnergyTerminalResidualCensusRefine350.refinedResidualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · exact mem_350_3810
  · exact mem_350_3863

theorem newRefineIDs_card : newRefineIDs.card = 2 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 348 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_350,
    EnergyTerminalResidualCensusRefine350.refinedResidualIDs_card,
    newRefineIDs_card]
  norm_num

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine350.refinedResidualIDs ∧
        n ≠ 3810 ∧ n ≠ 3863 := by
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

theorem b13_remaining_of_residual348 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine350.b13_remaining_of_residual350
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn3810 : n = 3810
  · subst n
    exact (EnergyRefineN3810.new_radius 3810 (by simp [EnergyRefineN3810.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn3863 : n = 3863
    · subst n
      exact (EnergyRefineN3863.new_radius 3863 (by simp [EnergyRefineN3863.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn3810, hn3863⟩)
        y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine348
#check @N11Formalization.EnergyTerminalResidualCensusRefine348.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine348.b13_remaining_of_residual348
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine348.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine348.b13_remaining_of_residual348
