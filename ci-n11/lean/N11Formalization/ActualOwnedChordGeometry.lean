import N11Formalization.ActualOwnershipSwitchWidths
import N11Formalization.ActualTriangleShoelace

/-! Closed inward-side geometry of each actual nearest ownership chord.

The original allowance r is used in the width and norm bounds. Tangent
chords are retained: the owner triangle determinant is nonnegative, not
silently required to be strictly positive.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualOwnedChordGeometry
open ActualCoverStructuralReduction ActualOwnershipSwitchWidths ActualBoundaryNineTies
open ActualRingDirectionOrder ActualBoundaryCyclicOrder ActualBoundaryArcFrame FlashTiling

theorem center_chord_orientation (C : Point) (m d : ℝ) :
    orient C (circleMap (m-d)) (circleMap (m+d)) =
      2*Real.sin d*(Real.cos d-inner ℝ C (circleMap m)) := by
  rw [PinTangentGeometry.inner_coords]
  change
    (Real.cos (m-d)-C 0)*(Real.sin (m+d)-C 1) -
        (Real.sin (m-d)-C 1)*(Real.cos (m+d)-C 0) =
      2*Real.sin d*(Real.cos d-(C 0*Real.cos m+C 1*Real.sin m))
  calc
    _ = 2*Real.sin d*
        (Real.cos d*(Real.sin m^2+Real.cos m^2)-
          (C 0*Real.cos m+C 1*Real.sin m)) := by
      rw [Real.cos_sub,Real.cos_add,Real.sin_sub,Real.sin_add]
      ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

theorem actual_owner_norm_le_chord_distance {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) (i : Fin 9) :
    ‖c (ringSite (nextRing i))‖ ≤ Real.cos (switchGap v i/2) := by
  have hg := actual_switch_gap_positive h hr v i
  have hu := actual_switch_gap_le_two_arcsin h hr v i
  have ha : Real.arcsin r ≤ Real.pi := by
    linarith [Real.arcsin_le_pi_div_two r,Real.pi_pos]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith : 0 ≤ switchGap v i/2) ha (by linarith : switchGap v i/2 ≤ Real.arcsin r)
  rw [Real.cos_arcsin] at hc
  exact (h.inward (ringSite (nextRing i)) (nextRing i).isLt).trans hc

theorem actual_owned_chord_triangle_nonneg {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) (i : Fin 9) :
    0 ≤ orient (c (ringSite (nextRing i))) (circleMap (v.tie i).angle)
      (circleMap (v.tie (nextRing i)).angle) := by
  let a := (v.tie i).angle
  let b := nextLift v i
  let m := (a+b)/2
  let d := (b-a)/2
  have hd : d = switchGap v i/2 := rfl
  have hleft : a = m-d := by dsimp [m,d]; ring
  have hright : b = m+d := by dsimp [m,d]; ring
  have hcos := actual_owner_norm_le_chord_distance h hr v i
  have hinner : inner ℝ (c (ringSite (nextRing i))) (circleMap m) ≤
      ‖c (ringSite (nextRing i))‖ := by
    have hh := (abs_le.mp (abs_real_inner_le_norm
      (c (ringSite (nextRing i))) (circleMap m))).2
    rwa [circleMap_norm,mul_one] at hh
  have hg := actual_switch_gap_positive h hr v i
  have hu := actual_switch_gap_le_two_arcsin h hr v i
  have hd0 : 0 < d := by rw [hd]; linarith
  have hdpi : d < Real.pi := by
    rw [hd]
    linarith [Real.arcsin_le_pi_div_two r,Real.pi_pos]
  have hs := (Real.sin_pos_of_pos_of_lt_pi hd0 hdpi).le
  rw [← nextLift_circle v i]
  change 0 ≤ orient (c (ringSite (nextRing i))) (circleMap a) (circleMap b)
  rw [hleft,hright,center_chord_orientation]
  apply mul_nonneg
  · exact mul_nonneg (by norm_num) hs
  · rw [hd]
    exact sub_nonneg.mpr (hinner.trans hcos)

end N11Formalization.ActualOwnedChordGeometry
#check @N11Formalization.ActualOwnedChordGeometry.actual_owned_chord_triangle_nonneg
#print axioms N11Formalization.ActualOwnedChordGeometry.actual_owned_chord_triangle_nonneg
