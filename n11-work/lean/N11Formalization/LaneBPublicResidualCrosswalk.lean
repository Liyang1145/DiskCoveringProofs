import N11Formalization.EnergyTerminalResidualCensusRefineSixteen

/-! Crosswalk from the seven public row-cap ids to the B13 residual census.

Two ids (`2337`, `2341`) are already removed by the sixteen-id refinement.
The remaining five public row-cap ids are still in the 373-element refined
residual set.  This is set bookkeeping only; it pays no radius. -/
set_option autoImplicit false
namespace N11Formalization.LaneBPublicResidualCrosswalk
open Finset
noncomputable section

def publicRowCapIDs : Finset (Fin 5011) :=
  {1409, 2337, 2341, 2356, 2360, 2368, 2370}

def unpaidPublicRowCapIDs : Finset (Fin 5011) :=
  publicRowCapIDs \ EnergyTerminalResidualCensusRefineSixteen.newRefineIDs

private theorem census_1409 :
    (1409 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel

private theorem census_2337 :
    (2337 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel

private theorem census_2341 :
    (2341 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel

private theorem census_2356 :
    (2356 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel

private theorem census_2360 :
    (2360 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel

private theorem census_2368 :
    (2368 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel

private theorem census_2370 :
    (2370 : Fin 5011) ∈ EnergyTerminalResidualCensus.residualIDs := by
  decide +kernel

theorem publicRowCapIDs_subset_census :
    publicRowCapIDs ⊆ EnergyTerminalResidualCensus.residualIDs := by
  intro n hn
  simp only [publicRowCapIDs, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact census_1409
  · exact census_2337
  · exact census_2341
  · exact census_2356
  · exact census_2360
  · exact census_2368
  · exact census_2370

theorem publicRowCapIDs_card : publicRowCapIDs.card = 7 := by
  decide +kernel

theorem newRefineIDs_inter_publicRowCapIDs :
    EnergyTerminalResidualCensusRefineSixteen.newRefineIDs ∩ publicRowCapIDs =
      {2337, 2341} := by
  decide +kernel

theorem unpaidPublicRowCapIDs_eq :
    unpaidPublicRowCapIDs = {1409, 2356, 2360, 2368, 2370} := by
  decide +kernel

theorem unpaidPublicRowCapIDs_card : unpaidPublicRowCapIDs.card = 5 := by
  decide +kernel

theorem unpaidPublicRowCapIDs_subset_refinedResidualIDs :
    unpaidPublicRowCapIDs ⊆
      EnergyTerminalResidualCensusRefineSixteen.refinedResidualIDs := by
  intro n hn
  rw [unpaidPublicRowCapIDs, Finset.mem_sdiff] at hn
  rw [EnergyTerminalResidualCensusRefineSixteen.refinedResidualIDs,
    Finset.mem_sdiff]
  exact ⟨publicRowCapIDs_subset_census hn.1, hn.2⟩

end
end N11Formalization.LaneBPublicResidualCrosswalk
#check @N11Formalization.LaneBPublicResidualCrosswalk.publicRowCapIDs_subset_census
#check @N11Formalization.LaneBPublicResidualCrosswalk.unpaidPublicRowCapIDs_subset_refinedResidualIDs
#check @N11Formalization.LaneBPublicResidualCrosswalk.unpaidPublicRowCapIDs_card
#print axioms N11Formalization.LaneBPublicResidualCrosswalk.unpaidPublicRowCapIDs_subset_refinedResidualIDs
