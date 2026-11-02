import N11Formalization.EnergyTerminalResidualCensus
import N11Formalization.EnergyTerminalBatchB13Refine0037
import N11Formalization.EnergyTerminalBatchB13Refine3149

/-! The two CI-green singleton refinements for source terminals 37 and 3149
remove two ids from the kernel-counted 389-id B13 residual.  This avoids the
still-red N39 repair while preserving the exact 387-id residual interface.
The two removed ids use their existing archive certificates; the other 387
ids have no radius certificates here. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine0037Refine3149
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {37, 3149}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensus.residualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_0037 : (37 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_3149 : (3149 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

theorem census_0037 : (37 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  rw [← EnergyTerminalResidualCensus.residualIDs_eq,
    EnergyTerminalBatchB13.mem_residualIDs_iff]
  exact ⟨EnergyRefineN0037.terminal, not_sharp_0037,
    EnergyTerminalBatchB13Refine0037.not_paid_0037⟩

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
  · exact census_0037
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
      n ∉ EnergyTerminalBatchB13.paidIDs ∧ n ≠ 37 ∧ n ≠ 3149 := by
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
  by_cases hn37 : n = 37
  · subst n
    exact (EnergyRefineN0037.new_radius 37 (by simp [EnergyRefineN0037.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn3149 : n = 3149
    · subst n
      exact (EnergyRefineN3149.new_radius 3149 (by simp [EnergyRefineN3149.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · exact h n ((mem_refinedResidualIDs_iff n).mpr
        ⟨ht, hs, hp, hn37, hn3149⟩) y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine0037Refine3149
#check @N11Formalization.EnergyTerminalResidualCensusRefine0037Refine3149.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine0037Refine3149.b13_remaining_of_residual387
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine0037Refine3149.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine0037Refine3149.b13_remaining_of_residual387
