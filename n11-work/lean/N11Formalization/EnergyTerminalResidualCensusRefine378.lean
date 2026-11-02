import N11Formalization.EnergyTerminalResidualCensusRefine385
import N11Formalization.EnergyTerminalBatchB13Refine3116
import N11Formalization.EnergyTerminalBatchB13Refine3431
import N11Formalization.EnergyTerminalBatchB13Refine3573
import N11Formalization.EnergyTerminalBatchB13Refine3777
import N11Formalization.EnergyTerminalBatchB13Refine2337
import N11Formalization.EnergyTerminalBatchB13Refine2341
import N11Formalization.EnergyTerminalBatchB13Refine3633

/-! Remove seven additional CI-green archive refinements from the 385-id
residual interface. The resulting exact residual has 378 ids. This module
supplies no radius certificate for any remaining id and makes no payment
claim. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefine378
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) :=
  {3116, 3431, 3573, 3777, 2337, 2341, 3633}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensusRefine385.refinedResidualIDs \ newRefineIDs

private theorem patchID_val_ge_4436 (p : Fin 120) :
    4436 ≤ (Patch120DomainPacket.patchID p).val := by
  fin_cases p <;> decide

private theorem not_sharp (n : Fin 5011) (hn : n.val < 4436) :
    n ∉ Patch120SharpDispatch.sharpIDs := by
  intro hsharp
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hsharp
  have hge := patchID_val_ge_4436 p
  rw [hp] at hge
  exact (not_le_of_gt hn) hge

private theorem mem_triple_3116 :
    (3116 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  exact ⟨EnergyRefineN3116.terminal, not_sharp 3116 (by decide),
    EnergyTerminalBatchB13Refine3116.not_paid_3116, by decide, by decide, by decide⟩

private theorem mem_triple_3431 :
    (3431 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  exact ⟨EnergyRefineN3431.terminal, not_sharp 3431 (by decide),
    EnergyTerminalBatchB13Refine3431.not_paid_3431, by decide, by decide, by decide⟩

private theorem mem_triple_3573 :
    (3573 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  exact ⟨EnergyRefineN3573.terminal, not_sharp 3573 (by decide),
    EnergyTerminalBatchB13Refine3573.not_paid_3573, by decide, by decide, by decide⟩

private theorem mem_triple_3777 :
    (3777 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  exact ⟨EnergyRefineN3777.terminal, not_sharp 3777 (by decide),
    EnergyTerminalBatchB13Refine3777.not_paid_3777, by decide, by decide, by decide⟩

private theorem mem_triple_2337 :
    (2337 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  exact ⟨EnergyRefineN2337.terminal, not_sharp 2337 (by decide),
    EnergyTerminalBatchB13Refine2337.not_paid_2337, by decide, by decide, by decide⟩

private theorem mem_triple_2341 :
    (2341 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  exact ⟨EnergyRefineN2341.terminal, not_sharp 2341 (by decide),
    EnergyTerminalBatchB13Refine2341.not_paid_2341, by decide, by decide, by decide⟩

private theorem mem_triple_3633 :
    (3633 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefineTriple.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefineTriple.mem_refinedResidualIDs_iff]
  exact ⟨EnergyRefineN3633.terminal, not_sharp 3633 (by decide),
    EnergyTerminalBatchB13Refine3633.not_paid_3633, by decide, by decide, by decide⟩

private theorem mem_385_3116 :
    (3116 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefine385.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff]
  exact ⟨mem_triple_3116, by decide⟩

private theorem mem_385_3431 :
    (3431 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefine385.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff]
  exact ⟨mem_triple_3431, by decide⟩

private theorem mem_385_3573 :
    (3573 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefine385.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff]
  exact ⟨mem_triple_3573, by decide⟩

private theorem mem_385_3777 :
    (3777 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefine385.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff]
  exact ⟨mem_triple_3777, by decide⟩

private theorem mem_385_2337 :
    (2337 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefine385.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff]
  exact ⟨mem_triple_2337, by decide⟩

private theorem mem_385_2341 :
    (2341 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefine385.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff]
  exact ⟨mem_triple_2341, by decide⟩

private theorem mem_385_3633 :
    (3633 : Fin 5011) ∈
      EnergyTerminalResidualCensusRefine385.refinedResidualIDs := by
  rw [EnergyTerminalResidualCensusRefine385.mem_refinedResidualIDs_iff]
  exact ⟨mem_triple_3633, by decide⟩

theorem newRefineIDs_subset_385 :
    newRefineIDs ⊆ EnergyTerminalResidualCensusRefine385.refinedResidualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_385_3116
  · exact mem_385_3431
  · exact mem_385_3573
  · exact mem_385_3777
  · exact mem_385_2337
  · exact mem_385_2341
  · exact mem_385_3633

theorem newRefineIDs_card : newRefineIDs.card = 7 := by
  decide

theorem refinedResidualIDs_card : refinedResidualIDs.card = 378 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_385,
    EnergyTerminalResidualCensusRefine385.refinedResidualIDs_card,
    newRefineIDs_card]

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔
      n ∈ EnergyTerminalResidualCensusRefine385.refinedResidualIDs ∧
        n ≠ 3116 ∧ n ≠ 3431 ∧ n ≠ 3573 ∧ n ≠ 3777 ∧
        n ≠ 2337 ∧ n ≠ 2341 ∧ n ≠ 3633 := by
  rw [refinedResidualIDs, Finset.mem_sdiff, newRefineIDs,
    Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton]
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

theorem b13_remaining_of_residual378 (h : RemainingTerminalRadius) :
    EnergyTerminalBatchB13.RemainingTerminalRadius := by
  apply EnergyTerminalResidualCensusRefine385.b13_remaining_of_residual385
  intro n hn y hy0 hy1 hc C Z r hf
  by_cases h3116 : n = 3116
  · subst n
    exact (EnergyRefineN3116.new_radius 3116 (by simp [EnergyRefineN3116.newIDs])
      y hy0 hy1 hc C Z r hf).le
  · by_cases h3431 : n = 3431
    · subst n
      exact (EnergyRefineN3431.new_radius 3431 (by simp [EnergyRefineN3431.newIDs])
        y hy0 hy1 hc C Z r hf).le
    · by_cases h3573 : n = 3573
      · subst n
        exact (EnergyRefineN3573.new_radius 3573 (by simp [EnergyRefineN3573.newIDs])
          y hy0 hy1 hc C Z r hf).le
      · by_cases h3777 : n = 3777
        · subst n
          exact (EnergyRefineN3777.new_radius 3777 (by simp [EnergyRefineN3777.newIDs])
            y hy0 hy1 hc C Z r hf).le
        · by_cases h2337 : n = 2337
          · subst n
            exact (EnergyRefineN2337.new_radius 2337 (by simp [EnergyRefineN2337.newIDs])
              y hy0 hy1 hc C Z r hf).le
          · by_cases h2341 : n = 2341
            · subst n
              exact (EnergyRefineN2341.new_radius 2341 (by simp [EnergyRefineN2341.newIDs])
                y hy0 hy1 hc C Z r hf).le
            · by_cases h3633 : n = 3633
              · subst n
                exact (EnergyRefineN3633.new_radius 3633 (by simp [EnergyRefineN3633.newIDs])
                  y hy0 hy1 hc C Z r hf).le
              · exact h n ((mem_refinedResidualIDs_iff n).mpr
                  ⟨hn, h3116, h3431, h3573, h3777, h2337, h2341, h3633⟩)
                  y hy0 hy1 hc C Z r hf

end
end N11Formalization.EnergyTerminalResidualCensusRefine378
#check @N11Formalization.EnergyTerminalResidualCensusRefine378.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefine378.b13_remaining_of_residual378
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine378.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefine378.b13_remaining_of_residual378
