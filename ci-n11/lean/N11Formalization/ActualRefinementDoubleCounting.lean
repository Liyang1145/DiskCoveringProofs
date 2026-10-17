import N11Formalization.ActualSelectedEdgeIncidence

/-! Exact face/edge incidence double counting for the ACTUAL selected
finite triangle family:3F+9=2E. This is NOT Euler, and does not by itself
claim F=11 or that the global union is a cellular disk. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementDoubleCounting
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementInteriorFacetCount
open ActualRefinementBoundaryCount ActualSelectedEdgeIncidence
open ActualRingDirectionOrder ActualBoundaryCyclicOrder

def boundaryEdges : Finset (Finset (Fin 11)) :=
  Finset.univ.image (fun i : Fin 9 => ({ringSite i,ringSite (nextRing i)} : Finset (Fin 11)))

theorem boundary_edges_card : boundaryEdges.card = 9 := by decide +kernel

theorem boundary_pair_iff : ∀ i j : Fin 11, i ≠ j →
    (({i,j} : Finset (Fin 11)) ∈ boundaryEdges ↔ BoundaryLabels i j) := by
  decide +kernel

def edges {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    Finset (Finset (Fin 11)) := by
  classical
  exact Finset.univ.biUnion (fun a : R.Index => (labelSet R a).powersetCard 2)

def edgeTriangles {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (e : Finset (Fin 11)) : Finset R.Index := by
  classical
  exact Finset.univ.filter (fun a => e ⊆ labelSet R a)

theorem boundary_edges_subset {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    boundaryEdges ⊆ edges R := by
  classical
  intro e he
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  have hcard := actual_boundary_triangle_count h hr R i
  have hne : (boundaryTriangles R i).Nonempty := Finset.card_pos.mp (by rw [hcard]; decide)
  obtain ⟨a,ha⟩ := hne
  have hA := (Finset.mem_filter.mp ha).2
  apply Finset.mem_biUnion.mpr
  refine ⟨a,Finset.mem_univ _,Finset.mem_powersetCard.mpr ⟨?_,?_⟩⟩
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hA.1
    · have he := Finset.mem_singleton.mp hk
      subst k
      exact hA.2
  · have hne : ringSite i ≠ ringSite (nextRing i) := by
      intro he
      exact next_ne i (Fin.ext (congrArg (fun q : Fin 11 => q.val) he))
    simp [hne]

theorem actual_edge_triangle_card {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {e : Finset (Fin 11)} (he : e ∈ edges R) :
    (edgeTriangles R e).card = if e ∈ boundaryEdges then 1 else 2 := by
  classical
  obtain ⟨a,_,hea⟩ := Finset.mem_biUnion.mp he
  have hA := Finset.mem_powersetCard.mp hea
  obtain ⟨i,j,hij,heq⟩ := Finset.card_eq_two.mp hA.2
  subst e
  have hI := hA.1 (by simp : i ∈ ({i,j} : Finset (Fin 11)))
  have hJ := hA.1 (by simp : j ∈ ({i,j} : Finset (Fin 11)))
  have hsame : edgeTriangles R {i,j} = pairTriangles R i j := by
    ext k
    simp [edgeTriangles,pairTriangles,Finset.insert_subset_iff,Finset.singleton_subset_iff]
  rw [hsame]
  have hcount := actual_selected_edge_incidence h hr R hij hI hJ
  simpa only [boundary_pair_iff i j hij] using hcount

theorem triangle_above_edges {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (a : R.Index) :
    (edges R).bipartiteAbove (fun t e => e ⊆ labelSet R t) a =
      (labelSet R a).powersetCard 2 := by
  classical
  ext e
  constructor
  · intro he
    have hE : e ∈ edges R ∧ e ⊆ labelSet R a := by
      simpa only [Finset.bipartiteAbove,Finset.mem_filter] using he
    obtain ⟨b,_,heb⟩ := Finset.mem_biUnion.mp hE.1
    exact Finset.mem_powersetCard.mpr ⟨hE.2,(Finset.mem_powersetCard.mp heb).2⟩
  · intro he
    change e ∈ (edges R).filter (fun e => e ⊆ labelSet R a)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,he⟩,(Finset.mem_powersetCard.mp he).1⟩

theorem actual_triangle_edge_double_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    3*Fintype.card R.Index+9 = 2*(edges R).card := by
  classical
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun a e => e ⊆ labelSet R a) (s := Finset.univ) (t := edges R)
  have hthree (a : R.Index) :
      ((edges R).bipartiteAbove (fun t e => e ⊆ labelSet R t) a).card = 3 := by
    rw [triangle_above_edges,Finset.card_powersetCard,labelSet_card]
    decide
  simp only [hthree,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hdouble
  have hleft : (∑ e ∈ edges R, (edgeTriangles R e).card)+boundaryEdges.card =
      2*(edges R).card := by
    have hB := boundary_edges_subset h hr R
    have hfilter : (edges R).filter (fun e => e ∈ boundaryEdges) = boundaryEdges := by
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun he => ⟨hB he,he⟩⟩
    have hboole : (∑ e ∈ edges R, if e ∈ boundaryEdges then 1 else 0) = boundaryEdges.card := by
      rw [Finset.sum_boole,hfilter]
      simp
    rw [← hboole,← Finset.sum_add_distrib]
    have hsum : ∀ e ∈ edges R, (edgeTriangles R e).card+
        (if e ∈ boundaryEdges then 1 else 0) = 2 := by
      intro e he
      rw [actual_edge_triangle_card h hr R he]
      split_ifs <;> decide
    rw [Finset.sum_congr rfl hsum,Finset.sum_const]
    simp only [smul_eq_mul]
    omega
  change Fintype.card R.Index*3 = ∑ e ∈ edges R, (edgeTriangles R e).card at hdouble
  rw [boundary_edges_card,← hdouble] at hleft
  nlinarith

end N11Formalization.ActualRefinementDoubleCounting
#check @N11Formalization.ActualRefinementDoubleCounting.actual_triangle_edge_double_count
#print axioms N11Formalization.ActualRefinementDoubleCounting.actual_edge_triangle_card
#print axioms N11Formalization.ActualRefinementDoubleCounting.actual_triangle_edge_double_count
