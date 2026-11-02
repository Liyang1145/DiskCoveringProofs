import N11Formalization.EnergyTerminalResidualCensusRefine368
import N11Formalization.EnergyTerminalBatchB13Refine4650
import N11Formalization.EnergyTerminalBatchB13Refine4244

/-! Remove the CI-green 4650 and 4244 archive refinements from the 368-id
residual interface, leaving an exact residual of 366 ids. This module supplies
no new radius certificate beyond those two and makes no payment claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine366
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) := {4650, 4244}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine368.refinedResidualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp_4650 : (4650 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem not_sharp_4244 : (4244 : Fin 5011) ∉ Patch120SharpDispatch.sharpIDs := by
  intro hn
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hn
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  norm_num at hge

private theorem mem_368_4650 :
    (4650 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine368.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine368.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine371.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine373.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN4650.terminal
    | exact not_sharp_4650
    | exact EnergyTerminalBatchB13Refine4650.not_paid_4650
    | decide
    | constructor

private theorem mem_368_4244 :
    (4244 : Fin 5011) ∈ EnergyTerminalResidualCensusRefine368.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine368.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine371.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine373.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine375.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine376.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine377.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine378.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff,
    EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  repeat' first
    | exact EnergyRefineN4244.terminal
    | exact not_sharp_4244
    | exact EnergyTerminalBatchB13Refine4244.not_paid_4244
    | decide
    | constructor

private theorem newRefineIDs_subset_368 : newRefineIDs ⊆
    EnergyTerminalResidualCensusRefine368.refinedResidualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · exact mem_368_4650
  · exact mem_368_4244

theorem newRefineIDs_card : newRefineIDs.card = 2 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 366 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_368,
    EnergyTerminalResidualCensusRefine368.refinedResidualIDs_card,
    newRefineIDs_card]
  norm_num

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine368.refinedResidualIDs ∧
        n ≠ 4650 ∧ n ≠ 4244 := by
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

theorem b13_remaining_of_residual366 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine368.b13_remaining_of_residual368
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases hn4650 : n = 4650
  · subst n
    exact (EnergyRefineN4650.new_radius 4650 (by simp [EnergyRefineN4650.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases hn4244 : n = 4244
    · subst n
      exact (EnergyRefineN4244.new_radius 4244 (by simp [EnergyRefineN4244.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨hn, hn4650, hn4244⟩)
        y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine366
#check @N11Formalization.EnergyTerminalResidualCensusRefine366.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine366.b13_remaining_of_residual366
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine366.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine366.b13_remaining_of_residual366
