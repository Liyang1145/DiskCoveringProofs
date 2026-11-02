import N11Formalization.EnergyTerminalResidualCensusRefine378
import N11Formalization.EnergyTerminalBatchB13Refine3841

/-! Remove the CI-green 3841 archive refinement from the 378-id residual
interface, leaving an exact residual of 377 ids. This module supplies no new
radius certificate beyond 3841 and makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine377
open Finset
noncomputable section

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine378.refinedResidualIDs \ {3841}

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_3841 : (3841 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

theorem mem_378_3841 :
    (3841 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine378.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff]
  exact ⟨EnergyRefineN3841.terminal, not_sharp_3841,
    EnergyTerminalBatchB13Refine3841.not_paid_3841, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem refinedResidualIDs_card : refinedResidualIDs.card = 377 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset (by
      intro n hn
      rw [Finset.mem_singleton] at hn
      subst n
      exact mem_378_3841),
    EnergyTerminalResidualCensusRefine378.refinedResidualIDs_card]
  simp

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine378.refinedResidualIDs ∧ n ≠ 3841 := by
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

theorem b13_remaining_of_residual377 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine378.b13_remaining_of_residual378
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn3841 : n = 3841
  · subst n
    exact (EnergyRefineN3841.new_radius 3841 (by simp [EnergyRefineN3841.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn3841⟩)
      y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine377
#check @N11Formalization.EnergyTerminalResidualCensusRefine377.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine377.b13_remaining_of_residual377
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine377.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine377.b13_remaining_of_residual377
