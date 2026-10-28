import N11Formalization.ActualBoundaryShoelace
import N11Formalization.ActualRingShoelacePositive

/-! Productive ACTUAL center-ring shoelace identity.
All real positive selected triangle determinants sum to the positive
nine-ring shoelace. Boundary orientation+1 is derived by positivity,
not from an assumed convex hull/cellular disk/Jordan theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCenterRingShoelace
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryChainConservation ActualBoundaryShoelace ActualRingShoelacePositive
open ActualRefinementEulerCount ActualRingDirectionOrder ActualRingLinkBoundaryData FlashTiling

theorem actual_face_determinant_sum_positive {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    0 < ∑ A : R.Index, orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2)) := by
  classical
  letI : Nonempty R.Index := Fintype.card_pos_iff.mp (by rw [actual_faces_eleven h hr R]; decide)
  exact Finset.sum_pos (fun A _ => (Refinement.real_triangle R A).2.2) Finset.univ_nonempty

theorem actual_boundary_mass_positive_one {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    mass R 0=1 := by
  have ht := actual_signed_shoelace_identity h hr R
  have hf := actual_face_determinant_sum_positive h hr R
  have hp := actual_ring_shoelace_positive h hr
  have hp' : 0 < ∑ i : Fin 9, det2 (c (ringSite i)) (c (nextSite i)) := by
    simpa only [nextSite] using hp
  rcases actual_boundary_mass_one_or_neg_one h hr R 0 with he | he
  · exact he
  · rw [he] at ht
    norm_num at ht
    change (∑ A : R.Index, orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2))) =
      -∑ i : Fin 9, det2 (c (ringSite i)) (c (nextSite i)) at ht
    linarith

theorem actual_center_ring_shoelace {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (∑ A : R.Index, orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2))) =
      ∑ i : Fin 9, det2 (c (ringSite i)) (c (nextSite i)) := by
  have ht := actual_signed_shoelace_identity h hr R
  rwa [actual_boundary_mass_positive_one h hr R,Int.cast_one,one_mul] at ht

theorem actual_all_boundary_mass_positive_one {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    ∀ i : Fin 9, mass R i=1 := by
  intro i
  rw [actual_boundary_mass_constant h hr R i 0,actual_boundary_mass_positive_one h hr R]

end N11Formalization.ActualCenterRingShoelace
#check @N11Formalization.ActualCenterRingShoelace.actual_center_ring_shoelace
#print axioms N11Formalization.ActualCenterRingShoelace.actual_center_ring_shoelace
#print axioms N11Formalization.ActualCenterRingShoelace.actual_all_boundary_mass_positive_one
