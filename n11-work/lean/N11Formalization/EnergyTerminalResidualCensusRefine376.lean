import N11Formalization.EnergyTerminalResidualCensusRefine377
import N11Formalization.EnergyTerminalBatchB13Refine3792

/-! Remove the CI-green 3792 archive refinement from the 377-id residual
interface, leaving an exact residual of 376 ids. This module supplies no new
radius certificate beyond 3792 and makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine376
open Finset
noncomputable section

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine377.refinedResidualIDs \ {3792}

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_3792 : (3792 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

theorem mem_377_3792 :
    (3792 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine377.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff]
  exact ⟨EnergyRefineN3792.terminal, not_sharp_3792,
    EnergyTerminalBatchB13Refine3792.not_paid_3792, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem refinedResidualIDs_card : refinedResidualIDs.card = 376 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset (by
      intro n hn
      rw [Finset.mem_singleton] at hn
      subst n
      exact mem_377_3792),
    EnergyTerminalResidualCensusRefine377.refinedResidualIDs_card]
  simp

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine377.refinedResidualIDs ∧ n ≠ 3792 := by
  rw [refinedResidualIDs, Finset.mem_sdiff, Finset.mem_singleton]

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

theorem b13_remaining_of_residual376 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine377.b13_remaining_of_residual377
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn3792 : n = 3792
  · subst n
    exact (EnergyRefineN3792.new_radius 3792 (by simp [EnergyRefineN3792.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn3792⟩)
      y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine376
#check @N11Formalization.EnergyTerminalResidualCensusRefine376.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine376.b13_remaining_of_residual376
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine376.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine376.b13_remaining_of_residual376
