import N11Formalization.EnergyTerminalResidualCensusRefineTriple
import N11Formalization.EnergyTerminalBatchB13Refine3112

/-! Add the CI-green 3112 archive refinement to the three-id census bridge.
The resulting interface removes exactly `{37, 3112, 3149, 3853}` from the
389-id B13 residual.  No radius certificate is supplied for the remaining
385 ids. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine385
open Finset
noncomputable section

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs \ {3112}

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide +kernel

private theorem not_sharp_3112 : (3112 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

theorem census_3112 : (3112 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  rw [← EnergyTerminalResidualCensus.residualIDs_eq,
    EnergyTerminalBatchB13.mem_residualIDs_iff]
  exact ⟨EnergyRefineN3112.terminal, not_sharp_3112,
    EnergyTerminalBatchB13Refine3112.not_paid_3112⟩

theorem mem_triple_refined_3112 :
    (3112 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  exact ⟨EnergyRefineN3112.terminal, not_sharp_3112,
    EnergyTerminalBatchB13Refine3112.not_paid_3112, by decide, by decide, by decide⟩

theorem refinedResidualIDs_card : refinedResidualIDs.card = 385 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset (by
      intro n hn
      rw [Finset.mem_singleton] at hn
      subst n
      exact mem_triple_refined_3112),
    EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs_card]
  simp

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs ∧
        n ≠ 3112 := by
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

theorem b13_remaining_of_residual385 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefineTriple.b13_remaining_of_residual386
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn3112 : n = 3112
  · subst n
    exact (EnergyRefineN3112.new_radius 3112 (by simp [EnergyRefineN3112.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn3112⟩)
      y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine385
#check @N11Formalization.EnergyTerminalResidualCensusRefine385.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine385.b13_remaining_of_residual385
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine385.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine385.b13_remaining_of_residual385
