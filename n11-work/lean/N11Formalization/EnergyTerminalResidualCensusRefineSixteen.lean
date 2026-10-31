import N11Formalization.EnergyTerminalResidualCensus
import N11Formalization.EnergyTerminalBatchB13RefineSixteen
import N11Formalization.EnergyTerminalBatchB13RefineSixteenMain

/-! The sixteen individually certified B13 refinements remove a literal
sixteen-element subset of the kernel-counted 389-element residual census.
Consequently the refined residual set has cardinality 373.  This module records
the set/cardinality fact only; it does not prove the remaining radii. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalResidualCensusRefineSixteen
open Finset
noncomputable section

def newRefineIDs : Finset (Fin 5011) :=
  {37, 2337, 2341, 2965, 3040, 3112, 3116, 3431, 3440, 3573, 3589, 3623,
    3633, 3777, 3792, 3853}

def refinedResidualIDs : Finset (Fin 5011) :=
  EnergyTerminalResidualCensus.residualIDs \ newRefineIDs

private theorem census_37 : (37 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_2337 : (2337 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_2341 : (2341 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_2965 : (2965 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3040 : (3040 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3112 : (3112 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3116 : (3116 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3431 : (3431 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3440 : (3440 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3573 : (3573 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3589 : (3589 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3623 : (3623 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3633 : (3633 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3777 : (3777 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3792 : (3792 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel
private theorem census_3853 : (3853 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel

theorem newRefineIDs_subset_census : newRefineIDs ⊆ EnergyTerminalResidualCensus.residualIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact census_37
  · exact census_2337
  · exact census_2341
  · exact census_2965
  · exact census_3040
  · exact census_3112
  · exact census_3116
  · exact census_3431
  · exact census_3440
  · exact census_3573
  · exact census_3589
  · exact census_3623
  · exact census_3633
  · exact census_3777
  · exact census_3792
  · exact census_3853

theorem newRefineIDs_subset_paid : newRefineIDs ⊆
    EnergyTerminalBatchB13RefineSixteen.paidIDs := by
  intro n hn
  simp only [newRefineIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [EnergyTerminalBatchB13RefineSixteen.paidIDs,
      EnergyTerminalBatchB13RefineFourteen.paidIDs,
      EnergyTerminalBatchB13RefineThirteen.paidIDs,
      EnergyTerminalBatchB13RefineTwelve.paidIDs,
      EnergyTerminalBatchB13RefineEleven.paidIDs,
      EnergyTerminalBatchB13RefineEight.paidIDs,
      EnergyTerminalBatchB13RefineSeven.paidIDs,
      EnergyTerminalBatchB13RefineSixteen.newIDs,
      EnergyTerminalBatchB13RefineFourteen.newIDs,
      EnergyTerminalBatchB13RefineThirteen.newIDs,
      EnergyTerminalBatchB13RefineTwelve.newIDs,
      EnergyTerminalBatchB13RefineEleven.newIDs,
      EnergyTerminalBatchB13RefineEight.newIDs,
      EnergyTerminalBatchB13RefineSeven.newIDs,
      EnergyRefineN0037.newIDs, EnergyRefineN2337.newIDs,
      EnergyRefineN2341.newIDs, EnergyRefineN2965.newIDs,
      EnergyRefineN3040.newIDs, EnergyRefineN3112.newIDs,
      EnergyRefineN3116.newIDs, EnergyRefineN3431.newIDs,
      EnergyRefineN3440.newIDs, EnergyRefineN3573.newIDs,
      EnergyRefineN3589.newIDs, EnergyRefineN3623.newIDs,
      EnergyRefineN3633.newIDs, EnergyRefineN3777.newIDs,
      EnergyRefineN3792.newIDs, EnergyRefineN3853.newIDs,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]

theorem newRefineIDs_card : newRefineIDs.card = 16 := by
  decide +kernel

theorem refinedResidualIDs_card : refinedResidualIDs.card = 373 := by
  rw [refinedResidualIDs,
    Finset.card_sdiff_of_subset newRefineIDs_subset_census,
    EnergyTerminalResidualCensus.residualIDs_card, newRefineIDs_card]

/-- The sixteen ids are exactly the late B13 extensions: the eleven ids from
`RefineEleven` together with the five subsequent singletons. -/
theorem newRefineIDs_eq_late :
    newRefineIDs = EnergyTerminalBatchB13RefineEleven.newIDs ∪ {37} ∪
      {3112} ∪ {3116} ∪ {3431} ∪ {3573} := by
  decide +kernel

theorem b13_subset_paid :
    EnergyTerminalBatchB13.paidIDs ⊆
      EnergyTerminalBatchB13RefineSixteen.paidIDs := by
  intro n hn
  have h11 : n ∈ EnergyTerminalBatchB13RefineEleven.paidIDs :=
    Finset.mem_union_left _ hn
  have h12 : n ∈ EnergyTerminalBatchB13RefineTwelve.paidIDs :=
    Finset.mem_union_left _ h11
  have h13 : n ∈ EnergyTerminalBatchB13RefineThirteen.paidIDs :=
    Finset.mem_union_left _ h12
  have h14 : n ∈ EnergyTerminalBatchB13RefineFourteen.paidIDs :=
    Finset.mem_union_left _ h13
  exact Finset.mem_union_left _ h14

theorem paid_subset_b13_union_new :
    EnergyTerminalBatchB13RefineSixteen.paidIDs ⊆
      EnergyTerminalBatchB13.paidIDs ∪ newRefineIDs := by
  rw [newRefineIDs_eq_late]
  intro n hn
  simp only [EnergyTerminalBatchB13RefineSixteen.paidIDs,
    EnergyTerminalBatchB13RefineFourteen.paidIDs,
    EnergyTerminalBatchB13RefineThirteen.paidIDs,
    EnergyTerminalBatchB13RefineTwelve.paidIDs,
    EnergyTerminalBatchB13RefineEleven.paidIDs,
    Finset.mem_union] at hn ⊢
  tauto

theorem mem_refinedResidualIDs_iff (n : Fin 5011) :
    n ∈ refinedResidualIDs ↔ (DBMSourceTree.data n).terminal = true ∧
      n ∉ Patch120SharpDispatch.sharpIDs ∧
      n ∉ EnergyTerminalBatchB13RefineSixteen.paidIDs := by
  rw [refinedResidualIDs, Finset.mem_sdiff,
    EnergyTerminalResidualCensus.residualIDs_eq,
    EnergyTerminalBatchB13.mem_residualIDs_iff]
  constructor
  · rintro ⟨⟨ht, hs, hb⟩, hnnew⟩
    refine ⟨ht, hs, ?_⟩
    intro hp
    rcases Finset.mem_union.mp (paid_subset_b13_union_new hp) with hb' | hn'
    · exact hb hb'
    · exact hnnew hn'
  · rintro ⟨ht, hs, hp⟩
    exact ⟨⟨ht, hs, fun hb => hp (b13_subset_paid hb)⟩,
      fun hnnew => hp (newRefineIDs_subset_paid hnnew)⟩

/-- The refined remaining-radius obligation, posed directly on the literal
373-element census set. -/
def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011, n ∈ refinedResidualIDs →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r →
          SourceExactRoot.sourceRadius ≤ r

theorem remaining_iff_refineSixteen :
    RemainingTerminalRadius ↔
      EnergyTerminalBatchB13RefineSixteen.RemainingTerminalRadius := by
  constructor
  · intro h n ht hs hp y hy0 hy1 hc C Z r hf
    exact h n ((mem_refinedResidualIDs_iff n).mpr ⟨ht, hs, hp⟩)
      y hy0 hy1 hc C Z r hf
  · intro h n hn y hy0 hy1 hc C Z r hf
    obtain ⟨ht, hs, hp⟩ := (mem_refinedResidualIDs_iff n).mp hn
    exact h n ht hs hp y hy0 hy1 hc C Z r hf

theorem main_of_energy_refined_census_and_seven_classes
    (henergy : RemainingTerminalRadius)
    (hclasses : ActualMetricClassReduction.SevenClassExclusions) :
    N11MainStatement SourceExactRoot.sourceRadius :=
  EnergyTerminalBatchB13RefineSixteenMain.main_of_energy_refineSixteen_and_seven_classes
    (remaining_iff_refineSixteen.mp henergy) hclasses

end
end N11Formalization.EnergyTerminalResidualCensusRefineSixteen
#check @N11Formalization.EnergyTerminalResidualCensusRefineSixteen.newRefineIDs_subset_census
#check @N11Formalization.EnergyTerminalResidualCensusRefineSixteen.newRefineIDs_subset_paid
#check @N11Formalization.EnergyTerminalResidualCensusRefineSixteen.refinedResidualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensusRefineSixteen.mem_refinedResidualIDs_iff
#check @N11Formalization.EnergyTerminalResidualCensusRefineSixteen.remaining_iff_refineSixteen
#check @N11Formalization.EnergyTerminalResidualCensusRefineSixteen.main_of_energy_refined_census_and_seven_classes
#print axioms N11Formalization.EnergyTerminalResidualCensusRefineSixteen.refinedResidualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensusRefineSixteen.remaining_iff_refineSixteen
#print axioms N11Formalization.EnergyTerminalResidualCensusRefineSixteen.main_of_energy_refined_census_and_seven_classes
