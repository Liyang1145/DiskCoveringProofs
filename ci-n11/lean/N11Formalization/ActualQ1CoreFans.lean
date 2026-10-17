import N11Formalization.ActualQ1CoreCycle
import N11Formalization.ActualHubDegreeClasses

/-! Productive actual q1 ear and eight core hub faces, retaining all
original nearest witnesses. Seven real boundary edges and the real short
ear chord are used; no q1 metric exclusion or orderedtwofan is asserted. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ1CoreFans
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementEarCount
open ActualSelectedEarRemoval ActualQ1CoreCycle ActualQ0BoundaryFans
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualRefinementBoundaryCount ActualRefinementInteriorFacetCount
open ActualSelectedEdgeIncidence ActualShortChordHubData ActualSelectedRingEdges

structure EarData {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) where
  index : R.Index
  center : Fin 9
  labels : labelSet R index = {prevSite center,ringSite center,nextSite center}

theorem actual_q1_ear_data {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=1) : Nonempty (EarData R) := by
  classical
  obtain ⟨A,hA⟩ := Finset.card_pos.mp (by rw [hq]; decide)
  obtain ⟨e,he⟩ := selected_ring_triangle_ear h hr R (Finset.mem_filter.mp hA).2
  exact ⟨⟨A,e,he⟩⟩

theorem actual_ear_chord_other_hub {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r} (E : EarData R) :
    ∃ A : R.Index, ∃ b : Bool,
      A ≠ E.index ∧ labelSet R A = {prevSite E.center,nextSite E.center,hubSite b} := by
  classical
  have hp : prevSite E.center ∈ labelSet R E.index := by rw [E.labels]; simp
  have hn : nextSite E.center ∈ labelSet R E.index := by rw [E.labels]; simp
  have hc := actual_selected_edge_incidence h hr R (boundary_sites_distinct E.center).2.2 hp hn
  rw [if_neg (skip_pair_not_boundary E.center)] at hc
  have he : E.index ∈ pairTriangles R (prevSite E.center) (nextSite E.center) :=
    mem_pairTriangles.mpr ⟨hp,hn⟩
  have hrest : (pairTriangles R (prevSite E.center) (nextSite E.center)).erase E.index |>.Nonempty := by
    apply Finset.card_pos.mp
    have hh := Finset.card_erase_add_one he
    omega
  obtain ⟨A,hA⟩ := hrest
  have hne := (Finset.mem_erase.mp hA).1
  have hmem := mem_pairTriangles.mp (Finset.mem_erase.mp hA).2
  have hnot : ¬ RingOnly R A := by
    intro ha
    have hear := ear_only_rings R E.labels
    exact hne (ring_only_indices_unique h hr R ha hear)
  have hh := triangle_two_ring_labels_hub R (E.center-1).isLt (nextRing E.center).isLt
    (boundary_sites_distinct E.center).2.2 hmem.1 hmem.2 hnot
  rcases hh with hh | hh
  · exact ⟨A,true,hne,hh⟩
  · exact ⟨A,false,hne,hh⟩

structure CoreFans {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) where
  ear : EarData R
  faces : Fin 8 → R.Index
  colors : Fin 8 → Bool
  labels : ∀ i : Fin 8, labelSet R (faces i) =
    {ringSite (coreSite ear.center i),ringSite (coreSite ear.center (coreNext i)),hubSite (colors i)}
  no_ear_face : ∀ i : Fin 8, faces i ≠ ear.index

theorem actual_q1_core_fans {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (hq : (ringOnlyTriangles R).card=1) : Nonempty (CoreFans R) := by
  classical
  obtain ⟨E⟩ := actual_q1_ear_data h hr R hq
  have hchoice (i : Fin 8) : ∃ A : R.Index, ∃ b : Bool,
      labelSet R A = {ringSite (coreSite E.center i),
        ringSite (coreSite E.center (coreNext i)),hubSite b} ∧ A ≠ E.index := by
    by_cases hi : i.val < 7
    · let j := coreSite E.center i
      have hc := actual_boundary_triangle_count h hr R j
      obtain ⟨A,hA⟩ := Finset.card_pos.mp (by rw [hc]; decide)
      have hm := (Finset.mem_filter.mp hA).2
      have hnext := core_seven_original_sides E.center i hi
      have hpair : ringSite (coreSite E.center (coreNext i)) ∈ labelSet R A := by
        rw [hnext]
        exact hm.2
      have hne : A ≠ E.index := by
        intro he
        have hi' := hm.1
        have hn' := hpair
        rw [he,E.labels] at hi' hn'
        exact core_original_side_not_ear E.center i hi ⟨hi',hn'⟩
      have hnot : ¬ RingOnly R A := by
        intro ha
        exact hne (ring_only_indices_unique h hr R ha (ear_only_rings R E.labels))
      have hpairne : ringSite (coreSite E.center i) ≠
          ringSite (coreSite E.center (coreNext i)) := by
        intro he
        have hh : coreSite E.center i = coreSite E.center (coreNext i) :=
          Fin.ext (congrArg (fun k : Fin 11 => k.val) he)
        exact (core_next_ne i) ((coreSite_injective E.center hh).symm)
      have hh := triangle_two_ring_labels_hub R (coreSite E.center i).isLt
        (coreSite E.center (coreNext i)).isLt hpairne hm.1 hpair hnot
      rcases hh with hh | hh
      · exact ⟨A,true,hh,hne⟩
      · exact ⟨A,false,hh,hne⟩
    · have hi7 : i=7 := by apply Fin.ext; have hb := i.isLt; omega
      subst i
      obtain ⟨A,b,hne,hA⟩ := actual_ear_chord_other_hub h hr E
      refine ⟨A,b,?_,hne⟩
      rw [(core_chord_endpoints E.center).1,(core_chord_endpoints E.center).2]
      exact hA
  let A := fun i => Classical.choose (hchoice i)
  let B := fun i => Classical.choose (Classical.choose_spec (hchoice i))
  have hspec (i : Fin 8) := Classical.choose_spec (Classical.choose_spec (hchoice i))
  exact ⟨⟨E,A,B,fun i => (hspec i).1,fun i => (hspec i).2⟩⟩

theorem CoreFans.true_original_rows {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (F : CoreFans R) :
    ∀ i : Fin 8, ‖R.witness (F.faces i)‖ < 1 ∧
      ∀ j ∈ ({ringSite (coreSite F.ear.center i),
        ringSite (coreSite F.ear.center (coreNext i)),hubSite (F.colors i)} : Finset (Fin 11)),
        R.witness (F.faces i) ∈ ActualVoronoiCells.Cell c j ∧
          dist (R.witness (F.faces i)) (c j) ≤ r := by
  intro i
  refine ⟨(Refinement.real_triangle R _).1,?_⟩
  intro j hj
  rw [← F.labels i] at hj
  obtain ⟨v,hv⟩ := mem_labelSet.mp hj
  rw [← hv]
  exact (Refinement.real_triangle R _).2.1 v

end N11Formalization.ActualQ1CoreFans
#check @N11Formalization.ActualQ1CoreFans.actual_q1_core_fans
#check @N11Formalization.ActualQ1CoreFans.CoreFans.true_original_rows
#print axioms N11Formalization.ActualQ1CoreFans.actual_q1_core_fans
