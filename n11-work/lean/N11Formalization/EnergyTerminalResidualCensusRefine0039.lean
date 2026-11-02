import N11Formalization.EnergyTerminalBatchB13Refine0039
import N11Formalization.EnergyTerminalResidualCensus

/-! The N39 refinement removes source terminal 39 from the kernel-counted
389-element residual.  This module proves the resulting set has cardinality
388 and relates its radius obligation to the conditional B13 refinement.
It is a census/interface theorem, not a radius certificate. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine0039
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {39}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensus.residualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_0039 : (39 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

theorem census_0039 : (39 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  rw [← EnergyTerminalResidualCensus.residualIDs_eq,
    EnergyTerminalBatchB13.mem_residualIDs_iff]
  exact ⟨EnergyRefineN0039.terminal, not_sharp_0039,
    EnergyTerminalBatchB13Refine0039.not_paid_0039⟩

theorem newRefineIDs_subset_census :
    newRefineIDs ⊆ EnergyTerminalResidualCensus.residualIDs := by
  intro n hn
  rw [newRefineIDs, Finset.mem_singleton] at hn
  subst n
  exact census_0039

theorem newRefineIDs_card : newRefineIDs.card = 1 := by
  simp [newRefineIDs]

theorem refinedResidualIDs_card : refinedResidualIDs.card = 388 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_census,
    EnergyTerminalResidualCensus.residualIDs_card, newRefineIDs_card]

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔ (DBMSourceTree.data n).terminal = true ∧
      n ∉ Patch120SharpDispatch.sharpIDs ∧
      n ∉ EnergyTerminalBatchB13.paidIDs ∧ n ≠ 39 := by
  rw [refinedResidualIDs, Finset.mem_sdiff, newRefineIDs,
    Finset.mem_singleton, EnergyTerminalResidualCensus.residualIDs_eq,
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

theorem refine0039_remaining_of_residual388 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13Refine0039.RemainingTerminalRadius := by
  intro n ht hs hp y hy0 hy1 hc C Z r hf
  apply h n _ y hy0 hy1 hc C Z r hf
  rw [mem_refinedResidualIDs_iff]
  refine ⟨ht, hs, ?_, ?_⟩
  · intro hb
    exact hp (Finset.mem_union_left _ hb)
  · intro hn
    subst n
    exact hp (Finset.mem_union_right _ (Finset.mem_singleton_self 39))

theorem b13_remaining_of_residual388 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius :=
  EnergyTerminalBatchB13Refine0039.remaining_of
    (refine0039_remaining_of_residual388 h)

end
end N11Formalization.EnergyTerminalResidualCensusRefine0039
#check @N11Formalization.EnergyTerminalResidualCensusRefine0039.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine0039.refine0039_remaining_of_residual388
#check @N11Formalization.EnergyTerminalResidualCensusRefine0039.b13_remaining_of_residual388
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine0039.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine0039.b13_remaining_of_residual388
