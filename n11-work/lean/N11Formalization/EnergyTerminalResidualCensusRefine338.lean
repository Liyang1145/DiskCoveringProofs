import N11Formalization.EnergyTerminalResidualCensusRefine340
import N11Formalization.EnergyTerminalBatchB13Refine38
import N11Formalization.EnergyTerminalBatchB13Refine3781

/-! Remove archive draft refinements 38 and 3781 from the 340-id residual
interface, leaving an exact conditional residual of 338 ids. The archive drafts
are not compiled and this module makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine338
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {38, 3781}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine340.refinedResidualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_38 : (38 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_3781 : (3781 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem mem_340_38 :
    (38 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine340.refinedResidualIDs := by
  rw [
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
    | exact EnergyRefineN0038.terminal
    | exact not_sharp_38
    | exact EnergyTerminalBatchB13Refine38.not_paid_38
    | decide
    | constructor

private theorem mem_340_3781 :
    (3781 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine340.refinedResidualIDs := by
  rw [
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
    | exact EnergyRefineN3781.terminal
    | exact not_sharp_3781
    | exact EnergyTerminalBatchB13Refine3781.not_paid_3781
    | decide
    | constructor

private theorem newRefineIDs_subset_340 : newRefineIDs ⊆
    EnergyTerminalResidualCensusRefine340.refinedResidualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · exact mem_340_38
  · exact mem_340_3781

theorem newRefineIDs_card : newRefineIDs.card = 2 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 338 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_340,
    EnergyTerminalResidualCensusRefine340.refinedResidualIDs_card,
    newRefineIDs_card]
  norm_num

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine340.refinedResidualIDs ∧
        n ≠ 38 ∧ n ≠ 3781 := by
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

theorem b13_remaining_of_residual338 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine340.b13_remaining_of_residual340
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn38 : n = 38
  · subst n
    exact (EnergyRefineN0038.new_radius 38 (by simp [EnergyRefineN0038.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn3781 : n = 3781
    · subst n
      exact (EnergyRefineN3781.new_radius 3781 (by simp [EnergyRefineN3781.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn38, hn3781⟩)
        y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine338
#check @N11Formalization.EnergyTerminalResidualCensusRefine338.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine338.b13_remaining_of_residual338
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine338.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine338.b13_remaining_of_residual338
