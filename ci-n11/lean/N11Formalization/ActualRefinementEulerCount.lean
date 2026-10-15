import N11Formalization.ActualSelectedRingEdges

/-! Productive exact ACTUAL F=11 and E=21.
Derived from real ring-edge classification and finite incidence counts,
not from an assumed cellular disk or Euler characteristic. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementEulerCount
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementDoubleCounting
open ActualHubTriangleCensus ActualSelectedRingEdges ActualRefinementVertexLinks

def incidentEdges {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (i : Fin 11) : Finset (Finset (Fin 11)) := by
  classical
  exact (edges R).filter (fun e => i ∈ e)

def pairWith (i j : Fin 11) : Finset (Fin 11) := {i,j}

theorem pairWith_injective (i : Fin 11) : Function.Injective (pairWith i) := by
  intro j k he
  by_cases hji : j = i
  · subst j
    have hk : k ∈ pairWith i k := by simp [pairWith]
    rw [← he] at hk
    have hki : k = i := by simpa [pairWith] using hk
    exact hki.symm
  · have hj : j ∈ pairWith i k := by rw [← he]; simp [pairWith]
    simpa [pairWith,hji] using hj

theorem pair_of_two_set_mem {e : Finset (Fin 11)} (he : e.card = 2)
    {i : Fin 11} (hi : i ∈ e) : ∃ j : Fin 11, i ≠ j ∧ e = {i,j} := by
  have hc : (e.erase i).card = 1 := by
    have hh := Finset.card_erase_add_one hi
    omega
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hc
  have hjm : j ∈ e.erase i := by rw [hj]; simp
  refine ⟨j,(Finset.mem_erase.mp hjm).1.symm,?_⟩
  rw [← Finset.insert_erase hi,hj]

theorem incident_edges_image {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) :
    incidentEdges R i = (neighbors R i).image (pairWith i) := by
  classical
  ext e
  constructor
  · intro he
    have hE := Finset.mem_filter.mp he
    obtain ⟨j,hij,hset⟩ := pair_of_two_set_mem (selected_edge_card_two R hE.1) hE.2
    obtain ⟨a,_,hA⟩ := Finset.mem_biUnion.mp hE.1
    have hs := (Finset.mem_powersetCard.mp hA).1
    have hai : i ∈ labelSet R a := hs hE.2
    have haj : j ∈ labelSet R a := hs (by rw [hset]; simp)
    refine Finset.mem_image.mpr ⟨j,(mem_neighbors R).mpr ⟨hij.symm,a,hai,haj⟩,?_⟩
    exact hset.symm
  · rintro he
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
    have hN := (mem_neighbors R).mp hj
    obtain ⟨a,hai,haj⟩ := hN.2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_biUnion.mpr
      refine ⟨a,Finset.mem_univ _,Finset.mem_powersetCard.mpr ⟨?_,?_⟩⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with he | hk
        · exact he ▸ hai
        · exact Finset.mem_singleton.mp hk ▸ haj
      · simp [pairWith,hN.1.symm]
    · simp [pairWith]

theorem incident_edges_card {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) :
    (incidentEdges R i).card = (neighbors R i).card := by
  classical
  rw [incident_edges_image,Finset.card_image_of_injective _ (pairWith_injective i)]

theorem hub_incident_complement {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    edges R \ (incidentEdges R 9 ∪ incidentEdges R 10) = ringEdges R := by
  classical
  ext e
  simp only [Finset.mem_sdiff,Finset.mem_union,incidentEdges,ringEdges,Finset.mem_filter]
  constructor
  · rintro ⟨he,hn⟩
    refine ⟨he,?_⟩
    intro j hj
    by_contra hnot
    have hb := j.isLt
    have hcases : j = 9 ∨ j = 10 := by
      have hh : j.val = 9 ∨ j.val = 10 := by omega
      exact hh.imp (fun hv => Fin.ext hv) (fun hv => Fin.ext hv)
    rcases hcases with rfl | rfl
    · exact hn (Or.inl ⟨he,hj⟩)
    · exact hn (Or.inr ⟨he,hj⟩)
  · rintro ⟨he,hall⟩
    refine ⟨he,?_⟩
    rintro (⟨_,h9⟩ | ⟨_,h10⟩)
    · have hh := hall 9 h9
      norm_num at hh
    · have hh := hall 10 h10
      norm_num at hh

theorem actual_hub_edge_mem {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    ({9,10} : Finset (Fin 11)) ∈ edges R := by
  classical
  obtain ⟨a,_,_,_,ha9,ha10,_,_⟩ :=
    ActualRefinementFacetRetention.Refinement.hub_edge_two_retained R h hr
  apply Finset.mem_biUnion.mpr
  refine ⟨a,Finset.mem_univ _,Finset.mem_powersetCard.mpr ⟨?_,by decide⟩⟩
  intro j hj
  rcases Finset.mem_insert.mp hj with he | hj
  · subst j
    exact mem_labelSet.mpr ha9
  · have he := Finset.mem_singleton.mp hj
    subst j
    exact mem_labelSet.mpr ha10

theorem actual_hub_incident_inter {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    incidentEdges R 9 ∩ incidentEdges R 10 = {({9,10} : Finset (Fin 11))} := by
  classical
  ext e
  simp only [Finset.mem_inter,incidentEdges,Finset.mem_filter,Finset.mem_singleton]
  constructor
  · rintro ⟨⟨he,h9⟩,⟨_,h10⟩⟩
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      rcases Finset.mem_insert.mp hj with he | hj
      · exact he ▸ h9
      · exact Finset.mem_singleton.mp hj ▸ h10
    · rw [selected_edge_card_two R he]
      decide
  · rintro rfl
    exact ⟨⟨actual_hub_edge_mem h hr R,by simp⟩,⟨actual_hub_edge_mem h hr R,by simp⟩⟩

theorem actual_edge_decomposition_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (edges R).card + 1 =
      (ringEdges R).card + (neighbors R 9).card + (neighbors R 10).card := by
  classical
  have hu : incidentEdges R 9 ∪ incidentEdges R 10 ⊆ edges R := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact (Finset.mem_filter.mp he).1
    · exact (Finset.mem_filter.mp he).1
  have hp := Finset.card_sdiff_add_card_eq_card hu
  rw [hub_incident_complement] at hp
  have hi := Finset.card_union_add_card_inter (incidentEdges R 9) (incidentEdges R 10)
  rw [actual_hub_incident_inter h hr R,Finset.card_singleton,incident_edges_card,
    incident_edges_card] at hi
  omega

theorem actual_edges_eq_faces_add_ten {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (edges R).card = Fintype.card R.Index + 10 := by
  have he := actual_edge_decomposition_count h hr R
  have hf := actual_total_face_census h hr R
  rw [actual_ring_edges_card h hr R] at he
  omega

theorem actual_faces_eleven {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    Fintype.card R.Index = 11 := by
  have he := actual_edges_eq_faces_add_ten h hr R
  have hd := actual_triangle_edge_double_count h hr R
  omega

theorem actual_edges_twenty_one {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (edges R).card = 21 := by
  rw [actual_edges_eq_faces_add_ten h hr R,actual_faces_eleven h hr R]

end N11Formalization.ActualRefinementEulerCount
#check @N11Formalization.ActualRefinementEulerCount.actual_faces_eleven
#check @N11Formalization.ActualRefinementEulerCount.actual_edges_twenty_one
#print axioms N11Formalization.ActualRefinementEulerCount.actual_faces_eleven
#print axioms N11Formalization.ActualRefinementEulerCount.actual_edges_twenty_one
