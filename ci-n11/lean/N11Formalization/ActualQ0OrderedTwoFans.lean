import N11Formalization.ActualQ0FanTransitions
import N11Formalization.ActualBinaryCycleRuns

/-! Productive ACTUAL q0 cyclic two-fan order with a legitimate cyclic
cut. The run length remains an actual1..8 parameter; no4/5 assertion or
metric class is assumed. All true primal witnesses/originalr are kept. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ0OrderedTwoFans
open ActualCoverStructuralReduction ActualFiniteNearestRefinement ActualRefinementEarCount
open ActualHubRingPaths ActualCentralRingEndpoints ActualRingDirectionOrder
open ActualRingLinkBoundaryData ActualQ0BoundaryFans ActualQ0FanTransitions
open ActualBinaryCycleRuns ActualRefinementTriangleUniqueness

structure OrderedData {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) where
  fans : FanData R
  cut : Fin 9
  second : Fin 9
  endpoints_ne : cut ≠ second
  run_length : Fin 9
  positive : 0 < run_length.val
  length_exact : run_length = second-cut
  changes : ∀ i : Fin 9, fans.colors (i-1) ≠ fans.colors i ↔ i=cut ∨ i=second
  order : ∀ i : Fin 9, fans.colors (i+cut) =
    if i.val < run_length.val then fans.colors cut else !fans.colors cut
  central_labels : ∀ a ∈ ActualRefinementHubCount.hubTriangles R,
    labelSet R a = {9,10,ringSite cut} ∨ labelSet R a = {9,10,ringSite second}
  central_first : ∃ a : R.Index, labelSet R a = {9,10,ringSite cut}
  central_second : ∃ a : R.Index, labelSet R a = {9,10,ringSite second}

theorem actual_q0_ordered_two_fans {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=0) : Nonempty (OrderedData R) := by
  obtain ⟨F⟩ := actual_q0_fan_data h hr R hq
  obtain ⟨P⟩ := (actual_two_ring_paths h hr R).1
  obtain ⟨a,b,hab,ha,hb,hchange⟩ :=
    ActualQ0FanTransitions.FanData.exactly_two_actual_transitions h hr F P
  obtain ⟨hm,_,horder⟩ := two_changes_runs hab hchange
  obtain ⟨A,hA9,hA10,hAf⟩ := P.first_central
  obtain ⟨B,hB9,hB10,hBl⟩ := P.last_central
  have hAfset := three_labels_full R (P.ring_vertices _ P.walk.start_mem_support) hA9 hA10 hAf
  have hBlset := three_labels_full R (P.ring_vertices _ P.walk.end_mem_support) hB9 hB10 hBl
  refine ⟨⟨F,a,b,hab,b-a,Nat.pos_of_ne_zero hm,rfl,hchange,horder,?_,?_,?_⟩⟩
  · intro T hT
    simpa only [← ha,← hb] using actual_central_labels h hr R P T hT
  · exact ⟨A,by rwa [← ha] at hAfset⟩
  · exact ⟨B,by rwa [← hb] at hBlset⟩

theorem OrderedData.true_shifted_fan {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (O : OrderedData R) (i : Fin 9) :
    labelSet R (O.fans.faces (i+O.cut)) =
      {ringSite (i+O.cut),nextSite (i+O.cut),
        if i.val < O.run_length.val then hubSite (O.fans.colors O.cut)
          else hubSite (!O.fans.colors O.cut)} := by
  rw [O.fans.labels,O.order]
  split_ifs <;> rfl

theorem OrderedData.true_original_rows {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (O : OrderedData R) :
    ∀ i : Fin 9, ‖R.witness (O.fans.faces (i+O.cut))‖ < 1 ∧
      ∀ j ∈ ({ringSite (i+O.cut),nextSite (i+O.cut),
        if i.val < O.run_length.val then hubSite (O.fans.colors O.cut)
          else hubSite (!O.fans.colors O.cut)} : Finset (Fin 11)),
        R.witness (O.fans.faces (i+O.cut)) ∈ ActualVoronoiCells.Cell c j ∧
          dist (R.witness (O.fans.faces (i+O.cut))) (c j) ≤ r := by
  intro i
  refine ⟨(Refinement.real_triangle R _).1,?_⟩
  intro j hj
  rw [← OrderedData.true_shifted_fan O i] at hj
  obtain ⟨v,hv⟩ := mem_labelSet.mp hj
  rw [← hv]
  exact (Refinement.real_triangle R _).2.1 v

end N11Formalization.ActualQ0OrderedTwoFans
#check @N11Formalization.ActualQ0OrderedTwoFans.actual_q0_ordered_two_fans
#check @N11Formalization.ActualQ0OrderedTwoFans.OrderedData.true_original_rows
#print axioms N11Formalization.ActualQ0OrderedTwoFans.actual_q0_ordered_two_fans
#print axioms N11Formalization.ActualQ0OrderedTwoFans.OrderedData.true_original_rows
