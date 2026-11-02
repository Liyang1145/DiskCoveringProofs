import N11Formalization.EnergyTerminalResidualCensusRefine376
import N11Formalization.EnergyTerminalBatchB13Refine3496

/-! Remove the CI-green 3496 archive refinement from the 376-id residual
interface, leaving an exact residual of 375 ids. This module supplies no new
radius certificate beyond 3496 and makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine375
open Finset
noncomputable section

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine376.refinedResidualIDs \ {3496}

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_3496 : (3496 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

theorem mem_376_3496 :
    (3496 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine376.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN3496.terminal
    | exact not_sharp_3496
    | exact EnergyTerminalBatchB13Refine3496.not_paid_3496
    | decide
    | constructor

theorem refinedResidualIDs_card : refinedResidualIDs.card = 375 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset (by
      intro n hn
      rw [Finset.mem_singleton] at hn
      subst n
      exact mem_376_3496),
    EnergyTerminalResidualCensusRefine376.refinedResidualIDs_card]
  simp

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine376.refinedResidualIDs ∧ n ≠ 3496 := by
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

theorem b13_remaining_of_residual375 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine376.b13_remaining_of_residual376
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn3496 : n = 3496
  · subst n
    exact (EnergyRefineN3496.new_radius 3496 (by simp [EnergyRefineN3496.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn3496⟩)
      y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine375
#check @N11Formalization.EnergyTerminalResidualCensusRefine375.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine375.b13_remaining_of_residual375
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine375.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine375.b13_remaining_of_residual375
