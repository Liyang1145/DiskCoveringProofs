import N11Formalization.ActualTriangleBoundaryChain

/-! All actual boundary-edge triangle coefficients agree cyclically.
Every interior edge cancels, each positive triangle has zero row divergence,
and the only surviving edges are the nine true ring boundary edges.
No global disk/Euler hypothesis is inserted. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryChainConservation
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementInteriorFacetCount
open ActualSelectedEdgeIncidence ActualRefinementVertexLinks
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualTriangleBoundaryChain

theorem total_antisymm {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i j : Fin 11) : total R i j = -total R j i := by
  unfold total
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact coefficient_antisymm R a i j

theorem total_self_zero {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) : total R i i = 0 := by
  have hh := total_antisymm R i i
  omega

theorem total_eq_pair_sum {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i j : Fin 11) :
    total R i j = ∑ a ∈ pairTriangles R i j, coefficient R a i j := by
  classical
  apply Eq.symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  exact coefficient_zero_of_not_pair R (by simpa only [mem_pairTriangles] using ha)

theorem total_nonboundary_zero {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i j : Fin 11} (hb : ¬ BoundaryLabels i j) : total R i j = 0 := by
  classical
  by_cases hij : i = j
  · subst j
    exact total_self_zero R i
  rw [total_eq_pair_sum]
  by_cases he : (pairTriangles R i j).Nonempty
  · obtain ⟨a,ha⟩ := he
    have hA := mem_pairTriangles.mp ha
    have hc := actual_selected_edge_incidence h hr R hij hA.1 hA.2
    rw [if_neg hb] at hc
    obtain ⟨A,B,hAB,hset⟩ := Finset.card_eq_two.mp hc
    have hAm : A ∈ pairTriangles R i j := by rw [hset]; simp
    have hBm : B ∈ pairTriangles R i j := by rw [hset]; simp
    have hA' := mem_pairTriangles.mp hAm
    have hB' := mem_pairTriangles.mp hBm
    rw [hset,Finset.sum_pair hAB]
    exact coefficient_shared_cancel h.injective R hAB hij hA'.1 hA'.2 hB'.1 hB'.2
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]

theorem boundary_labels_at_ring : ∀ i : Fin 9, ∀ j : Fin 11,
    BoundaryLabels (ringSite i) j ↔ j = prevSite i ∨ j = nextSite i := by
  decide +kernel

def mass {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i : Fin 9) : ℤ :=
  total R (ringSite i) (nextSite i)

theorem actual_boundary_mass_previous {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9) :
    mass R i = mass R (i-1) := by
  classical
  have hrow := total_row_zero R (ringSite i)
  have hs : ∑ j ∈ ({prevSite i,nextSite i} : Finset (Fin 11)),
      total R (ringSite i) j = ∑ j : Fin 11, total R (ringSite i) j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    apply total_nonboundary_zero h hr R
    simpa only [boundary_labels_at_ring,Finset.mem_insert,Finset.mem_singleton] using hj
  rw [← hs,Finset.sum_pair (boundary_sites_distinct i).2.2] at hrow
  have hn : nextSite (i-1) = ringSite i := by
    unfold nextSite nextRing
    rw [sub_add_cancel]
  change total R (ringSite i) (nextSite i) =
    total R (ringSite (i-1)) (nextSite (i-1))
  rw [hn]
  change total R (ringSite i) (nextSite i) = total R (prevSite i) (ringSite i)
  rw [total_antisymm R (prevSite i) (ringSite i)]
  change total R (ringSite i) (nextSite i) = -total R (ringSite i) (prevSite i)
  omega

theorem fin_nine_previous_constant {f : Fin 9 → ℤ}
    (h : ∀ i : Fin 9, f i = f (i-1)) : ∀ i j : Fin 9, f i = f j := by
  have h1 : f 1 = f 0 := h 1
  have h2 : f 2 = f 1 := h 2
  have h3 : f 3 = f 2 := h 3
  have h4 : f 4 = f 3 := h 4
  have h5 : f 5 = f 4 := h 5
  have h6 : f 6 = f 5 := h 6
  have h7 : f 7 = f 6 := h 7
  have h8 : f 8 = f 7 := h 8
  have hc : ∀ i : Fin 9, f i = f 0 := by
    intro i
    fin_cases i
    · rfl
    · exact h1
    · exact h2.trans h1
    · exact h3.trans (h2.trans h1)
    · exact h4.trans (h3.trans (h2.trans h1))
    · exact h5.trans (h4.trans (h3.trans (h2.trans h1)))
    · exact h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1))))
    · exact h7.trans (h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1)))))
    · exact h8.trans (h7.trans (h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1))))))
  intro i j
  exact (hc i).trans (hc j).symm

theorem actual_boundary_mass_constant {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    ∀ i j : Fin 9, mass R i = mass R j :=
  fin_nine_previous_constant (actual_boundary_mass_previous h hr R)

theorem boundary_total_eq_coefficient {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i j : Fin 11} (hij : i ≠ j) (hb : BoundaryLabels i j)
    {a : R.Index} (hai : i ∈ labelSet R a) (haj : j ∈ labelSet R a) :
    total R i j = coefficient R a i j := by
  classical
  have hc := actual_selected_edge_incidence h hr R hij hai haj
  rw [if_pos hb] at hc
  have ha : a ∈ pairTriangles R i j := mem_pairTriangles.mpr ⟨hai,haj⟩
  obtain ⟨b,hset⟩ := Finset.card_eq_one.mp hc
  have hab : a = b := by rw [hset] at ha; exact Finset.mem_singleton.mp ha
  have hs : pairTriangles R i j = {a} := by rw [hab,hset]
  rw [total_eq_pair_sum,hs,Finset.sum_singleton]

end N11Formalization.ActualBoundaryChainConservation
#check @N11Formalization.ActualBoundaryChainConservation.actual_boundary_mass_constant
#print axioms N11Formalization.ActualBoundaryChainConservation.actual_boundary_mass_constant
