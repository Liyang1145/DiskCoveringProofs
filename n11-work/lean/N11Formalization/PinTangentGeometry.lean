import N11Formalization.PinBranchBind
import N11Formalization.PinHeightPay
set_option autoImplicit false
namespace N11Formalization.PinTangentGeometry
open N11Formalization PinBranchBind
noncomputable section

def det (a b : Point) : ℝ := a 0 * b 1 - a 1 * b 0

theorem inner_coords (a b : Point) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct, Fin.sum_univ_two]
  ring

theorem norm_sq_coords (a : Point) : ‖a‖^2 = (a 0)^2 + (a 1)^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coords]
  ring

/-- Coordinate determinant and coordinate-free Gram determinant are the same quantity. -/
theorem det_sq_gram (a b : Point) :
    (det a b)^2 = ‖a‖^2 * ‖b‖^2 - (inner ℝ a b)^2 := by
  rw [norm_sq_coords, norm_sq_coords, inner_coords]
  unfold det
  ring

/-- Nonzero chord and nonzero pin height pay normal independence, with no branch sign assumption. -/
theorem pin_normals_independent {P Q U : Point}
    (hPQ : P ≠ Q) (heq : ‖U-P‖ = ‖U-Q‖)
    (hh : 0 < pinHeight P Q U) : det (U-P) (U-Q) ≠ 0 := by
  let W := U - chordMid P Q
  let D := Q-P
  have ho : inner ℝ W D = 0 :=
    PinHeightPayV6.sub_midpoint_orthogonal heq
  have hd : 0 < ‖D‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hPQ))
  have hw : 0 < ‖W‖ := hh
  have hg := det_sq_gram W D
  rw [ho, zero_pow (by decide : (2:ℕ) ≠ 0), sub_zero] at hg
  have hdet : det (U-P) (U-Q) = -(det W D) := by
    unfold det W D chordMid
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    ring
  intro hz
  have hz' : det W D = 0 := by linarith [hdet]
  rw [hz', zero_pow (by decide : (2:ℕ) ≠ 0)] at hg
  have hp := mul_pos (sq_pos_of_pos hw) (sq_pos_of_pos hd)
  linarith

/-- Two circle-normal equations uniquely determine a tangent velocity in the plane. -/
theorem tangent_unique {P Q U v w : Point}
    (hn : det (U-P) (U-Q) ≠ 0)
    (hP : inner ℝ (U-P) v = inner ℝ (U-P) w)
    (hQ : inner ℝ (U-Q) v = inner ℝ (U-Q) w) : v = w := by
  have h0 := hP
  have h1 := hQ
  rw [inner_coords, inner_coords] at h0 h1
  have hx : det (U-P) (U-Q) * (v 0 - w 0) = 0 := by
    unfold det
    linear_combination (U-Q) 1 * h0 - (U-P) 1 * h1
  have hy : det (U-P) (U-Q) * (v 1 - w 1) = 0 := by
    unfold det
    linear_combination (U-P) 0 * h1 - (U-Q) 0 * h0
  have hx' := (mul_eq_zero.mp hx).resolve_left hn
  have hy' := (mul_eq_zero.mp hy).resolve_left hn
  ext i
  fin_cases i
  · exact sub_eq_zero.mp hx'
  · exact sub_eq_zero.mp hy'

/-- Consumer of equidistance/positive-height geometry, not a numerical rank test. -/
theorem tangent_unique_of_height {P Q U v w : Point}
    (hPQ : P ≠ Q) (heq : ‖U-P‖ = ‖U-Q‖) (hh : 0 < pinHeight P Q U)
    (hP : inner ℝ (U-P) v = inner ℝ (U-P) w)
    (hQ : inner ℝ (U-Q) v = inner ℝ (U-Q) w) : v = w :=
  tangent_unique (pin_normals_independent hPQ heq hh) hP hQ

end
end N11Formalization.PinTangentGeometry
#check @N11Formalization.PinTangentGeometry.pin_normals_independent
#check @N11Formalization.PinTangentGeometry.tangent_unique_of_height
#print axioms N11Formalization.PinTangentGeometry.tangent_unique_of_height
