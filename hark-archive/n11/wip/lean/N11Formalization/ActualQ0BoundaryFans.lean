import N11Formalization.ActualHubDegreeClasses

/-! Actual q0 boundary fan data: every true ring boundary edge has
one real nearest triangle and one of the two actual hubs. The binary
owner is produced, not constrained to a canonical interval. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ0BoundaryFans
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementEarCount ActualHubTriangleCensus
open ActualRefinementBoundaryCount ActualShortChordHubData
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder

def hubSite (b : Bool) : Fin 11 := if b then 9 else 10

theorem hubSite_injective : Function.Injective hubSite := by decide +kernel
theorem hubSite_hub : ∀ b : Bool, 9 ≤ (hubSite b).val := by decide +kernel
theorem hubSite_not_other : ∀ b : Bool, hubSite (!b) ≠ hubSite b := by decide +kernel

structure FanData {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) where
  faces : Fin 9 → R.Index
  colors : Fin 9 → Bool
  labels : ∀ i : Fin 9,
    labelSet R (faces i) = {ringSite i,nextSite i,hubSite (colors i)}

theorem actual_q0_fan_data {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card = 0) : Nonempty (FanData R) := by
  classical
  have hnone : ringOnlyTriangles R = ∅ := Finset.card_eq_zero.mp hq
  have hchoice (i : Fin 9) : ∃ A : R.Index, ∃ b : Bool,
      labelSet R A = {ringSite i,nextSite i,hubSite b} := by
    have hc := actual_boundary_triangle_count h hr R i
    obtain ⟨A,hA⟩ := Finset.card_pos.mp (by rw [hc]; decide)
    have hm := (Finset.mem_filter.mp hA).2
    have hnot : ¬ RingOnly R A := by
      intro ha
      have hmem : A ∈ ringOnlyTriangles R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
      rw [hnone] at hmem
      exact Finset.notMem_empty A hmem
    have hh := triangle_two_ring_labels_hub R i.isLt (nextRing i).isLt
      (boundary_sites_distinct i).2.1.symm hm.1 hm.2 hnot
    rcases hh with hh | hh
    · exact ⟨A,true,hh⟩
    · exact ⟨A,false,hh⟩
  let F := fun i => Classical.choose (hchoice i)
  let B := fun i => Classical.choose (Classical.choose_spec (hchoice i))
  exact ⟨⟨F,B,fun i => Classical.choose_spec (Classical.choose_spec (hchoice i))⟩⟩

theorem FanData.previous_labels {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (F : FanData R) (i : Fin 9) :
    labelSet R (F.faces (i-1)) = {prevSite i,ringSite i,hubSite (F.colors (i-1))} := by
  have hn : nextSite (i-1) = ringSite i := by unfold nextSite nextRing; rw [sub_add_cancel]
  simpa only [hn,prevSite] using F.labels (i-1)

theorem FanData.real_rows {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (F : FanData R) (i : Fin 9) :
    ∀ j ∈ ({ringSite i,nextSite i,hubSite (F.colors i)} : Finset (Fin 11)),
      R.witness (F.faces i) ∈ ActualVoronoiCells.Cell c j ∧
        dist (R.witness (F.faces i)) (c j) ≤ r := by
  intro j hj
  rw [← F.labels i] at hj
  obtain ⟨v,hv⟩ := mem_labelSet.mp hj
  rw [← hv]
  exact (Refinement.real_triangle R (F.faces i)).2.1 v

end N11Formalization.ActualQ0BoundaryFans
#check @N11Formalization.ActualQ0BoundaryFans.actual_q0_fan_data
#check @N11Formalization.ActualQ0BoundaryFans.FanData.real_rows
#print axioms N11Formalization.ActualQ0BoundaryFans.actual_q0_fan_data
