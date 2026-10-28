import N11Formalization.ActualBoundaryChainConservation

/-! Three-label row identities and short-boundary coefficient agreement.
Real selected coefficients, not a guessed abstract orientation. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualTriangleChainRows
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualTriangleBoundaryChain
open ActualBoundaryChainConservation ActualRingDirectionOrder
open ActualRingLinkBoundaryData ActualBoundaryCyclicOrder

theorem coefficient_self_zero {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (a : R.Index) (i : Fin 11) : coefficient R a i i = 0 := by
  have hh := coefficient_antisymm R a i i
  omega

theorem coefficient_three_label_row {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {a : R.Index} {i j k : Fin 11}
    (hjk : j ≠ k) (hset : labelSet R a = {i,j,k}) :
    coefficient R a i j + coefficient R a i k = 0 := by
  classical
  have hr := coefficient_row_zero R a i
  have hs : (∑ v ∈ ({j,k} : Finset (Fin 11)), coefficient R a i v) =
      ∑ v : Fin 11, coefficient R a i v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    by_cases hvi : v = i
    · subst v
      exact coefficient_self_zero R a i
    · apply coefficient_zero_of_not_pair R
      intro hh
      rw [hset] at hh
      have hv' : v ≠ j ∧ v ≠ k := by simpa using hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh.2 with he | he | he
      · exact hvi he
      · exact hv'.1 he
      · exact hv'.2 he
  rw [← hs,Finset.sum_pair hjk] at hr
  exact hr

theorem coefficient_nonzero_of_third {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {a : R.Index} {i j k : Fin 11}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hi : i ∈ labelSet R a) (hj : j ∈ labelSet R a) (hk : k ∈ labelSet R a) :
    coefficient R a i j ≠ 0 := by
  rw [coefficient_of_third R hij hki hkj hi hj hk]
  split_ifs <;> norm_num

theorem actual_short_boundary_coefficients_equal {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    {a b : R.Index}
    (hap : prevSite i ∈ labelSet R a) (hai : ringSite i ∈ labelSet R a)
    (hbi : ringSite i ∈ labelSet R b) (hbn : nextSite i ∈ labelSet R b) :
    coefficient R a (prevSite i) (ringSite i) =
      coefficient R b (ringSite i) (nextSite i) := by
  have hleft : ActualRefinementInteriorFacetCount.BoundaryLabels (prevSite i) (ringSite i) := by
    have hn : nextSite (i-1) = ringSite i := by unfold nextSite nextRing; rw [sub_add_cancel]
    rw [← hn]
    exact (boundary_labels_at_ring (i-1) (nextSite (i-1))).mpr (Or.inr rfl)
  have hright : ActualRefinementInteriorFacetCount.BoundaryLabels (ringSite i) (nextSite i) :=
    (boundary_labels_at_ring i (nextSite i)).mpr (Or.inr rfl)
  have hprev := boundary_total_eq_coefficient h hr R (boundary_sites_distinct i).1
    hleft hap hai
  have hnext := boundary_total_eq_coefficient h hr R (boundary_sites_distinct i).2.1.symm
    hright hbi hbn
  have hm := actual_boundary_mass_previous h hr R i
  have hn : nextSite (i-1) = ringSite i := by unfold nextSite nextRing; rw [sub_add_cancel]
  dsimp only [mass] at hm
  rw [hn] at hm
  exact hprev.symm.trans (hm.symm.trans hnext)

end N11Formalization.ActualTriangleChainRows
#check @N11Formalization.ActualTriangleChainRows.actual_short_boundary_coefficients_equal
#print axioms N11Formalization.ActualTriangleChainRows.actual_short_boundary_coefficients_equal
