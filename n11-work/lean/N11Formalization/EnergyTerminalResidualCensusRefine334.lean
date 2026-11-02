import N11Formalization.EnergyTerminalResidualCensusRefine336
import N11Formalization.EnergyTerminalBatchB13Refine3578
import N11Formalization.EnergyTerminalBatchB13Refine3738

/-! Remove archive draft refinements 3578 and 3738 from the 336-id residual
interface, leaving an exact conditional residual of 334 ids. The archive drafts
are not compiled and this module makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine334
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {3578, 3738}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine336.refinedResidualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_3578 : (3578 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_3738 : (3738 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem mem_336_3578 :
    (3578 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine336.refinedResidualIDs := by
  rw [
    EnergyTerminalResidualCensusRefine336.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine340.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine342.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine344.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine346.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine348.mem_refinedResidualIDs_iff,
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
    | exact EnergyRefineN3578.terminal
    | exact not_sharp_3578
    | exact EnergyTerminalBatchB13Refine3578.not_paid_3578
    | decide
    | constructor

private theorem mem_336_3738 :
    (3738 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine336.refinedResidualIDs := by
  rw [
    EnergyTerminalResidualCensusRefine336.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine340.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine342.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine344.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine346.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine348.mem_refinedResidualIDs_iff,
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
    | exact EnergyRefineN3738.terminal
    | exact not_sharp_3738
    | exact EnergyTerminalBatchB13Refine3738.not_paid_3738
    | decide
    | constructor

private theorem newRefineIDs_subset_336 : newRefineIDs ⊆
    EnergyTerminalResidualCensusRefine336.refinedResidualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · exact mem_336_3578
  · exact mem_336_3738

theorem newRefineIDs_card : newRefineIDs.card = 2 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 334 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_336,
    EnergyTerminalResidualCensusRefine336.refinedResidualIDs_card,
    newRefineIDs_card]
  norm_num

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine336.refinedResidualIDs ∧
        n ≠ 3578 ∧ n ≠ 3738 := by
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

theorem b13_remaining_of_residual334 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine336.b13_remaining_of_residual336
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn3578 : n = 3578
  · subst n
    exact (EnergyRefineN3578.new_radius 3578 (by simp [EnergyRefineN3578.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn3738 : n = 3738
    · subst n
      exact (EnergyRefineN3738.new_radius 3738 (by simp [EnergyRefineN3738.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn3578, hn3738⟩)
        y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine334
#check @N11Formalization.EnergyTerminalResidualCensusRefine334.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine334.b13_remaining_of_residual334
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine334.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine334.b13_remaining_of_residual334
