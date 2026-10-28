import N11Formalization.ActualHubRingPaths
import N11Formalization.ActualRefinementHubCount

/-! The two ACTUAL hub ring paths have the same unordered pair of distinct
ring endpoints. Every central triangle has exactly one of these two ring
labels. The labels are produced, not assigned canonical0/4; path ordering
and complete two-fan classification remain separate. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCentralRingEndpoints
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementHubCount ActualHubRingPaths

theorem three_labels_full {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {a : R.Index} {k : Fin 11} (hk : k.val < 9)
    (h9 : 9 ∈ labelSet R a) (h10 : 10 ∈ labelSet R a) (hK : k ∈ labelSet R a) :
    labelSet R a = {9,10,k} := by
  have hk9 : k ≠ (9 : Fin 11) := by intro he; subst k; norm_num at hk
  have hk10 : k ≠ (10 : Fin 11) := by intro he; subst k; norm_num at hk
  have ht : ({9,10,k} : Finset (Fin 11)).card = 3 := by
    simp [hk9,hk10,hk9.symm,hk10.symm]
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h9
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h10
    have he := Finset.mem_singleton.mp hj
    subst j
    exact hK
  · rw [labelSet_card,ht]

theorem triple_ring_label_unique {a b : Fin 11} (ha : a.val < 9) (hb : b.val < 9)
    (he : ({9,10,a} : Finset (Fin 11)) = {9,10,b}) : a = b := by
  have hmem : a ∈ ({9,10,b} : Finset (Fin 11)) := by rw [← he]; simp
  rcases Finset.mem_insert.mp hmem with he9 | hmem
  · subst a
    norm_num at ha
  rcases Finset.mem_insert.mp hmem with he10 | hmem
  · subst a
    norm_num at ha
  exact Finset.mem_singleton.mp hmem

theorem actual_central_labels {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (P : RingPath R 9 10) :
    ∀ a ∈ hubTriangles R, labelSet R a = {9,10,P.first} ∨ labelSet R a = {9,10,P.last} := by
  classical
  have hfirst : P.first.val < 9 := P.ring_vertices _ P.walk.start_mem_support
  have hlast : P.last.val < 9 := P.ring_vertices _ P.walk.end_mem_support
  obtain ⟨A,hA9,hA10,hAf⟩ := P.first_central
  obtain ⟨B,hB9,hB10,hBl⟩ := P.last_central
  have hAfset := three_labels_full R hfirst hA9 hA10 hAf
  have hBlset := three_labels_full R hlast hB9 hB10 hBl
  have hA : A ∈ hubTriangles R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA9,hA10⟩
  have hB : B ∈ hubTriangles R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hB9,hB10⟩
  have hAB : A ≠ B := by
    intro he
    have hsets : ({9,10,P.first} : Finset (Fin 11)) = {9,10,P.last} := by
      rw [← hAfset,← hBlset,he]
    exact P.endpoints_ne (triple_ring_label_unique hfirst hlast hsets)
  have hsub : ({A,B} : Finset R.Index) ⊆ hubTriangles R := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hA
    · have he := Finset.mem_singleton.mp ha
      subst a
      exact hB
  have heq : hubTriangles R = {A,B} := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [actual_hub_triangle_count h hr R]
    simp [hAB]
  intro a ha
  rw [heq] at ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact Or.inl hAfset
  · have he := Finset.mem_singleton.mp ha
    subst a
    exact Or.inr hBlset

theorem actual_paths_common_endpoints {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (P : RingPath R 9 10) (Q : RingPath R 10 9) :
    ({P.first,P.last} : Finset (Fin 11)) = {Q.first,Q.last} := by
  classical
  have hfP : P.first.val < 9 := P.ring_vertices _ P.walk.start_mem_support
  have hlP : P.last.val < 9 := P.ring_vertices _ P.walk.end_mem_support
  have hfQ : Q.first.val < 9 := Q.ring_vertices _ Q.walk.start_mem_support
  have hlQ : Q.last.val < 9 := Q.ring_vertices _ Q.walk.end_mem_support
  have hthird (k : Fin 11) (hk : k.val < 9) (a : R.Index)
      (ha9 : 9 ∈ labelSet R a) (ha10 : 10 ∈ labelSet R a) (hak : k ∈ labelSet R a) :
      k ∈ ({P.first,P.last} : Finset (Fin 11)) := by
    have he := three_labels_full R hk ha9 ha10 hak
    have ha : a ∈ hubTriangles R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha9,ha10⟩
    rcases actual_central_labels h hr R P a ha with hF | hL
    · have hkf : k = P.first := triple_ring_label_unique hk hfP (he.symm.trans hF)
      simp [hkf]
    · have hkl : k = P.last := triple_ring_label_unique hk hlP (he.symm.trans hL)
      simp [hkl]
  obtain ⟨A,hA10,hA9,hAf⟩ := Q.first_central
  obtain ⟨B,hB10,hB9,hBl⟩ := Q.last_central
  have hQf := hthird Q.first hfQ A hA9 hA10 hAf
  have hQl := hthird Q.last hlQ B hB9 hB10 hBl
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hQf
    · have he := Finset.mem_singleton.mp hk
      subst k
      exact hQl
  · simp [P.endpoints_ne,Q.endpoints_ne]

theorem actual_two_paths_common_endpoints {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    ∃ (P : RingPath R 9 10) (Q : RingPath R 10 9),
      ({P.first,P.last} : Finset (Fin 11)) = {Q.first,Q.last} := by
  obtain ⟨hP,hQ⟩ := actual_two_ring_paths h hr R
  obtain ⟨P⟩ := hP
  obtain ⟨Q⟩ := hQ
  exact ⟨P,Q,actual_paths_common_endpoints h hr R P Q⟩

end N11Formalization.ActualCentralRingEndpoints
#check @N11Formalization.ActualCentralRingEndpoints.actual_two_paths_common_endpoints
#print axioms N11Formalization.ActualCentralRingEndpoints.actual_central_labels
#print axioms N11Formalization.ActualCentralRingEndpoints.actual_two_paths_common_endpoints
