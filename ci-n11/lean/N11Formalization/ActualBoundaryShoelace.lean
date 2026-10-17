import N11Formalization.ActualTriangleShoelace
import N11Formalization.ActualRefinementEulerCount

/-! Actual weighted boundary chain reduces to one common signed ring
shoelace coefficient. This is exact algebra; positivity of the radial
ring shoelace, and then the genuine circle-piece identities, are separate. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryShoelace
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualTriangleBoundaryChain ActualBoundaryChainConservation ActualTriangleShoelace
open ActualRefinementBoundaryCount ActualRefinementTriangleUniqueness
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualRefinementInteriorFacetCount FlashTiling

def forward (i : Fin 9) : Fin 11 × Fin 11 := (ringSite i,nextSite i)
def backward (i : Fin 9) : Fin 11 × Fin 11 := (nextSite i,ringSite i)
def forwardPairs : Finset (Fin 11 × Fin 11) := Finset.univ.image forward
def backwardPairs : Finset (Fin 11 × Fin 11) := Finset.univ.image backward

theorem forward_injective : Function.Injective forward := by decide +kernel
theorem backward_injective : Function.Injective backward := by decide +kernel
theorem forward_backward_disjoint : Disjoint forwardPairs backwardPairs := by decide +kernel
theorem boundary_labels_iff_pairs : ∀ i j : Fin 11,
    BoundaryLabels i j ↔ (i,j) ∈ forwardPairs ∪ backwardPairs := by decide +kernel

theorem actual_boundary_mass_one_or_neg_one {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9) :
    mass R i=1 ∨ mass R i= -1 := by
  classical
  have hc := actual_boundary_triangle_count h hr R i
  obtain ⟨A,hA⟩ := Finset.card_pos.mp (by rw [hc]; decide)
  have hmem := (Finset.mem_filter.mp hA).2
  have hij := (boundary_sites_distinct i).2.1.symm
  obtain ⟨k,hki,hkn,hset⟩ := ActualRefinementLinkDegrees.three_set_third
    (labelSet_card R A) hij hmem.1 hmem.2
  have hk : k ∈ labelSet R A := by rw [hset]; simp
  have hb : BoundaryLabels (ringSite i) (nextSite i) :=
    (boundary_labels_at_ring i (nextSite i)).mpr (Or.inr rfl)
  have ht := boundary_total_eq_coefficient h hr R hij hb hmem.1 hmem.2
  change mass R i=coefficient R A (ringSite i) (nextSite i) at ht
  rw [ht,coefficient_of_third R hij hki hkn hmem.1 hmem.2 hk]
  split_ifs <;> simp

theorem actual_weighted_boundary_support {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (∑ i : Fin 11, ∑ j : Fin 11, (total R i j : ℝ)*det2 (c i) (c j)) =
      ∑ p ∈ forwardPairs ∪ backwardPairs, (total R p.1 p.2 : ℝ)*det2 (c p.1) (c p.2) := by
  classical
  have hs : (∑ p ∈ forwardPairs ∪ backwardPairs,
      (total R p.1 p.2 : ℝ)*det2 (c p.1) (c p.2)) =
      ∑ p : Fin 11 × Fin 11, (total R p.1 p.2 : ℝ)*det2 (c p.1) (c p.2) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    have hb : ¬BoundaryLabels p.1 p.2 := fun hh =>
      hp ((boundary_labels_iff_pairs p.1 p.2).mp hh)
    rw [total_nonboundary_zero h hr R hb,Int.cast_zero,zero_mul]
  rw [hs,Fintype.sum_prod_type]

theorem actual_weighted_ring_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (∑ i : Fin 11, ∑ j : Fin 11, (total R i j : ℝ)*det2 (c i) (c j)) =
      2*(mass R 0 : ℝ)*∑ i : Fin 9, det2 (c (ringSite i)) (c (nextSite i)) := by
  classical
  rw [actual_weighted_boundary_support h hr R,Finset.sum_union forward_backward_disjoint,
    forwardPairs,backwardPairs]
  rw [Finset.sum_image (fun i _ j _ he => forward_injective he),
    Finset.sum_image (fun i _ j _ he => backward_injective he)]
  have hf (i : Fin 9) : total R (ringSite i) (nextSite i)=mass R 0 :=
    actual_boundary_mass_constant h hr R i 0
  have hb (i : Fin 9) : (total R (nextSite i) (ringSite i) : ℝ)*
      det2 (c (nextSite i)) (c (ringSite i)) =
      (mass R 0 : ℝ)*det2 (c (ringSite i)) (c (nextSite i)) := by
    rw [total_antisymm R (nextSite i) (ringSite i),hf,Int.cast_neg,
      ActualTriangleShoelace.det2_antisymm (c (nextSite i)) (c (ringSite i))]
    ring
  change (∑ i : Fin 9, (total R (ringSite i) (nextSite i) : ℝ)*
      det2 (c (ringSite i)) (c (nextSite i))) +
      (∑ i : Fin 9, (total R (nextSite i) (ringSite i) : ℝ)*
        det2 (c (nextSite i)) (c (ringSite i))) = _
  simp only [hf,hb]
  simp only [← Finset.mul_sum]
  ring

theorem actual_signed_shoelace_identity {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (∑ A : R.Index, orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2))) =
      (mass R 0 : ℝ)*∑ i : Fin 9, det2 (c (ringSite i)) (c (nextSite i)) := by
  have ht := actual_total_weighted_boundary R
  rw [actual_weighted_ring_sum h hr R] at ht
  linarith

end N11Formalization.ActualBoundaryShoelace
#check @N11Formalization.ActualBoundaryShoelace.actual_signed_shoelace_identity
#print axioms N11Formalization.ActualBoundaryShoelace.actual_boundary_mass_one_or_neg_one
#print axioms N11Formalization.ActualBoundaryShoelace.actual_signed_shoelace_identity
