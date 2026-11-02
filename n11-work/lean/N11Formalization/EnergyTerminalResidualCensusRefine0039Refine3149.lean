import N11Formalization.EnergyTerminalResidualCensusRefine0039
import N11Formalization.EnergyTerminalBatchB13Refine3149

/-! The combined singleton refinements for source terminals 39 and 3149 remove
two ids from the kernel-counted 389-id B13 residual.  This is a census and
interface theorem: the two new ids still rely on their archived certificates,
and the other 387 ids have no radius certificates here. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine0039Refine3149
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {39, 3149}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensus.residualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_3149 : (3149 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

theorem census_3149 : (3149 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  rw [← EnergyTerminalResidualCensus.residualIDs_eq,
    EnergyTerminalBatchB13.mem_residualIDs_iff]
  exact ⟨EnergyRefineN3149.terminal, not_sharp_3149,
    EnergyTerminalBatchB13Refine3149.not_paid_3149⟩

theorem newRefineIDs_subset_census :
    newRefineIDs ⊆ EnergyTerminalResidualCensus.residualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · exact EnergyTerminalResidualCensusRefine0039.census_0039
  · exact census_3149

theorem newRefineIDs_card : newRefineIDs.card = 2 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 387 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_census,
    EnergyTerminalResidualCensus.residualIDs_card, newRefineIDs_card]

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔ (DBMSourceTree.data n).terminal = true ∧
      n ∉ Patch120SharpDispatch.sharpIDs ∧
      n ∉ EnergyTerminalBatchB13.paidIDs ∧ n ≠ 39 ∧ n ≠ 3149 := by
  rw [refinedResidualIDs, Finset.mem_sdiff, newRefineIDs,
    Finset.mem_insert, Finset.mem_singleton,
    EnergyTerminalResidualCensus.residualIDs_eq,
    EnergyTerminalBatchB13.mem_residualIDs_iff]
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

theorem b13_remaining_of_residual387 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  intro n ht hs hp y hy0 hy1 hc C Z r hf
  by_cases hn39 : n = 39
  · subst n
    exact (EnergyRefineN0039.new_radius 39 (by simp [EnergyRefineN0039.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn3149 : n = 3149
    · subst n
      exact (EnergyRefineN3149.new_radius 3149 (by simp [EnergyRefineN3149.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · exact h n ((mem_refinedResidualIDs_iff n).mpr
        ⟨ht, hs, hp, hn39, hn3149⟩) y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine0039Refine3149
#check @N11Formalization.EnergyTerminalResidualCensusRefine0039Refine3149.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine0039Refine3149.b13_remaining_of_residual387
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine0039Refine3149.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine0039Refine3149.b13_remaining_of_residual387
