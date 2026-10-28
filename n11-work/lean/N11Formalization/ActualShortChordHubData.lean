import N11Formalization.ActualHubLinkNoRingCycle

/-! Real data for a selected skip-one ring chord with no selected ear.
It has exactly one selected triangle with each hub, and its two short
boundary sides have hub triangles. Their real witnesses are retained.
Orientation and the resulting exclusion are separate. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualShortChordHubData
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementVertexLinks
open ActualRefinementEarCount ActualSelectedEarRemoval ActualHubTriangleCensus
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualRefinementInteriorFacetCount ActualSelectedEdgeIncidence
open ActualRefinementBoundaryCount ActualHubNeighborCoverage

def SelectedEarAt {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i : Fin 9) : Prop :=
  ∃ a : R.Index, labelSet R a = {prevSite i,ringSite i,nextSite i}

theorem skip_pair_not_boundary : ∀ i : Fin 9, ¬ BoundaryLabels (prevSite i) (nextSite i) := by
  decide +kernel

theorem ear_contains_skip_pair : ∀ i e : Fin 9,
    prevSite i ∈ ({prevSite e,ringSite e,nextSite e} : Finset (Fin 11)) →
      nextSite i ∈ ({prevSite e,ringSite e,nextSite e} : Finset (Fin 11)) → i = e := by
  decide +kernel

theorem ear_contains_left_side : ∀ i e : Fin 9,
    prevSite i ∈ ({prevSite e,ringSite e,nextSite e} : Finset (Fin 11)) →
      ringSite i ∈ ({prevSite e,ringSite e,nextSite e} : Finset (Fin 11)) →
        e = i-1 ∨ e = i := by decide +kernel

theorem ear_contains_right_side : ∀ i e : Fin 9,
    ringSite i ∈ ({prevSite e,ringSite e,nextSite e} : Finset (Fin 11)) →
      nextSite i ∈ ({prevSite e,ringSite e,nextSite e} : Finset (Fin 11)) →
        e = i ∨ e = nextRing i := by decide +kernel

theorem triangle_two_ring_labels_hub {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {a : R.Index} {i j : Fin 11}
    (hi : i.val < 9) (hj : j.val < 9) (hij : i ≠ j)
    (hai : i ∈ labelSet R a) (haj : j ∈ labelSet R a)
    (ha : ¬ RingOnly R a) :
    labelSet R a = {i,j,9} ∨ labelSet R a = {i,j,10} := by
  classical
  obtain ⟨k,hki,hkj,hset⟩ := ActualRefinementLinkDegrees.three_set_third
    (labelSet_card R a) hij hai haj
  have hhub : 9 ∈ labelSet R a ∨ 10 ∈ labelSet R a := by
    simpa only [ringOnly_iff_no_hubs,not_and_or,not_not] using ha
  have hi9 : (9 : Fin 11) ≠ i := by intro he; subst i; norm_num at hi
  have hi10 : (10 : Fin 11) ≠ i := by intro he; subst i; norm_num at hi
  have hj9 : (9 : Fin 11) ≠ j := by intro he; subst j; norm_num at hj
  have hj10 : (10 : Fin 11) ≠ j := by intro he; subst j; norm_num at hj
  rw [hset] at hhub
  simp only [Finset.mem_insert,Finset.mem_singleton,hi9,hj9,hi10,hj10,false_or] at hhub
  rcases hhub with he | he
  · exact Or.inl (by rw [hset,← he])
  · exact Or.inr (by rw [hset,← he])

theorem actual_skip_no_ear_two_hubs {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    (hp : Neighbor R (prevSite i) (nextSite i)) (he : ¬ SelectedEarAt R i) :
    ∃ A B : R.Index, A ≠ B ∧
      labelSet R A = {prevSite i,nextSite i,9} ∧
      labelSet R B = {prevSite i,nextSite i,10} := by
  classical
  have hchoice (a : R.Index) (hap : prevSite i ∈ labelSet R a)
      (han : nextSite i ∈ labelSet R a) :
      labelSet R a = {prevSite i,nextSite i,9} ∨
        labelSet R a = {prevSite i,nextSite i,10} := by
    apply triangle_two_ring_labels_hub R (i-1).isLt (nextRing i).isLt hp.1.symm hap han
    intro ha
    obtain ⟨e,hE⟩ := selected_ring_triangle_ear h hr R ha
    have hie : i = e := ear_contains_skip_pair i e (hE ▸ hap) (hE ▸ han)
    exact he ⟨a,by rwa [← hie] at hE⟩
  obtain ⟨a,hai,haj⟩ := hp.2
  have hc := actual_selected_edge_incidence h hr R hp.1.symm hai haj
  rw [if_neg (skip_pair_not_boundary i)] at hc
  obtain ⟨A,B,hAB,hset⟩ := Finset.card_eq_two.mp hc
  have hAm : A ∈ pairTriangles R (prevSite i) (nextSite i) := by rw [hset]; simp
  have hBm : B ∈ pairTriangles R (prevSite i) (nextSite i) := by rw [hset]; simp
  have hA := hchoice A (mem_pairTriangles.mp hAm).1 (mem_pairTriangles.mp hAm).2
  have hB := hchoice B (mem_pairTriangles.mp hBm).1 (mem_pairTriangles.mp hBm).2
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact (hAB (labelSet_injective h.injective R (hA.trans hB.symm))).elim
  · exact ⟨A,B,hAB,hA,hB⟩
  · exact ⟨B,A,hAB.symm,hB,hA⟩
  · exact (hAB (labelSet_injective h.injective R (hA.trans hB.symm))).elim

theorem actual_skip_short_boundary_hubs {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    (hp : Neighbor R (prevSite i) (nextSite i)) (he : ¬ SelectedEarAt R i) :
    (∃ A : R.Index, labelSet R A = {prevSite i,ringSite i,9} ∨
      labelSet R A = {prevSite i,ringSite i,10}) ∧
    (∃ B : R.Index, labelSet R B = {ringSite i,nextSite i,9} ∨
      labelSet R B = {ringSite i,nextSite i,10}) := by
  obtain ⟨T,U,_,hT,hU⟩ := actual_skip_no_ear_two_hubs h hr R i hp he
  have hprev9 : Neighbor R (prevSite i) 9 := by
    refine ⟨?_,T,?_,?_⟩
    · intro he
      have hh := congrArg Fin.val he
      change 9 = (i-1).val at hh
      omega
    · rw [hT]; simp
    · rw [hT]; simp
  have hnext9 : Neighbor R (nextSite i) 9 := by
    refine ⟨?_,T,?_,?_⟩
    · intro he
      have hh := congrArg Fin.val he
      change 9 = (nextRing i).val at hh
      omega
    · rw [hT]; simp
    · rw [hT]; simp
  obtain ⟨hnprev,hnnext⟩ := actual_boundary_neighbors h hr R i
  obtain ⟨A,hAi,hAp⟩ := hnprev.2
  obtain ⟨B,hBi,hBn⟩ := hnnext.2
  constructor
  · refine ⟨A,triangle_two_ring_labels_hub R (i-1).isLt i.isLt
      (boundary_sites_distinct i).1 hAp hAi ?_⟩
    intro hA
    obtain ⟨e,hE⟩ := selected_ring_triangle_ear h hr R hA
    rcases ear_contains_left_side i e (hE ▸ hAp) (hE ▸ hAi) with hcase | hcase
    · subst e
      have hno := actual_ear_center_no_hub h hr R hE
      exact hno.1 hprev9
    · subst e
      exact he ⟨A,hE⟩
  · refine ⟨B,triangle_two_ring_labels_hub R i.isLt (nextRing i).isLt
      (boundary_sites_distinct i).2.1.symm hBi hBn ?_⟩
    intro hB
    obtain ⟨e,hE⟩ := selected_ring_triangle_ear h hr R hB
    rcases ear_contains_right_side i e (hE ▸ hBi) (hE ▸ hBn) with hcase | hcase
    · subst e
      exact he ⟨B,hE⟩
    · subst e
      have hno := actual_ear_center_no_hub h hr R hE
      exact hno.1 hnext9

end N11Formalization.ActualShortChordHubData
#check @N11Formalization.ActualShortChordHubData.actual_skip_no_ear_two_hubs
#check @N11Formalization.ActualShortChordHubData.actual_skip_short_boundary_hubs
#print axioms N11Formalization.ActualShortChordHubData.actual_skip_short_boundary_hubs
