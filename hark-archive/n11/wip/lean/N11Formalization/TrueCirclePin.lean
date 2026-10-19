import N11Formalization.PinTangentGeometry
set_option autoImplicit false
namespace N11Formalization.TrueCirclePin
open N11Formalization PinBranchBind PinTangentGeometry
noncomputable section

/-- Project a fixed seed normal onto the perpendicular of the varying chord. -/
def normal (W P Q : Point) : Point :=
  W - (inner ℝ W (Q-P) / ‖Q-P‖^2) • (Q-P)
def rad (P Q : Point) (R : ℝ) : ℝ := R^2 - ‖Q-P‖^2/4
def pin (W P Q : Point) (R : ℝ) : Point :=
  chordMid P Q + (Real.sqrt (rad P Q R) / ‖normal W P Q‖) • normal W P Q

theorem normal_orthogonal (W P Q : Point) (hPQ : P ≠ Q) :
    inner ℝ (normal W P Q) (Q-P) = 0 := by
  have hn : ‖Q-P‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hPQ.symm))
  rw [normal, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hPQ.symm)]
  ring

theorem normal_source {P Q U : Point} (heq : ‖U-P‖=‖U-Q‖) :
    normal (U-chordMid P Q) P Q = U-chordMid P Q := by
  have ho : inner ℝ (U-chordMid P Q) (Q-P) = 0 :=
    PinHeightPayV6.sub_midpoint_orthogonal heq
  simp [normal, ho]

/-- Height normalization proves the two actual squared-circle equations. -/
theorem pin_circle_equations (W P Q : Point) (R : ℝ)
    (hPQ : P ≠ Q) (hN : normal W P Q ≠ 0) (hr : 0 ≤ rad P Q R) :
    ‖pin W P Q R-P‖^2 = R^2 ∧ ‖pin W P Q R-Q‖^2 = R^2 := by
  let N := normal W P Q
  let M := chordMid P Q
  let V := (Real.sqrt (rad P Q R) / ‖N‖) • N
  have hn : ‖N‖ ≠ 0 := norm_ne_zero_iff.mpr hN
  have hv : ‖V‖^2 = rad P Q R := by
    dsimp [V]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, Real.sq_sqrt hr]
    field_simp
  have hM := two_smul_chordMid P Q
  have hPM : P-M = -(1/2 : ℝ) • (Q-P) := by
    dsimp [M, chordMid]
    module
  have hQM : Q-M = (1/2 : ℝ) • (Q-P) := by
    dsimp [M, chordMid]
    module
  have hp : ‖P-M‖^2 = ‖Q-P‖^2/4 := by
    rw [hPM, norm_smul, Real.norm_eq_abs, mul_pow]
    norm_num
    ring
  have hq : ‖Q-M‖^2 = ‖Q-P‖^2/4 := by
    rw [hQM, norm_smul, Real.norm_eq_abs, mul_pow]
    norm_num
    ring
  have ho := normal_orthogonal W P Q hPQ
  have hop : inner ℝ V (P-M) = 0 := by
    rw [hPM]
    dsimp [V, N]
    rw [real_inner_smul_left, real_inner_smul_right, ho]
    ring
  have hoq : inner ℝ V (Q-M) = 0 := by
    rw [hQM]
    dsimp [V, N]
    rw [real_inner_smul_left, real_inner_smul_right, ho]
    ring
  have hleft : pin W P Q R-P = V-(P-M) := by dsimp [pin, V, N, M]; abel
  have hright : pin W P Q R-Q = V-(Q-M) := by dsimp [pin, V, N, M]; abel
  constructor
  · rw [hleft, norm_sub_sq_real, hv, hp, hop]
    unfold rad
    ring
  · rw [hright, norm_sub_sq_real, hv, hq, hoq]
    unfold rad
    ring

/-- The fixed-seed construction selects the exact source branch, not its reflected partner. -/
theorem pin_source {P Q U : Point} {R : ℝ}
    (hP : ‖U-P‖=R) (hQ : ‖U-Q‖=R) (hh : 0 < pinHeight P Q U) :
    pin (U-chordMid P Q) P Q R = U := by
  have heq := hP.trans hQ.symm
  have hheight := PinHeightPayV6.pinHeight_sq_of_equidistant hP hQ
  have hr : rad P Q R = ‖U-chordMid P Q‖^2 := by
    change R^2-‖Q-P‖^2/4 = _
    change ‖U-chordMid P Q‖^2 = R^2-(‖Q-P‖/2)^2 at hheight
    nlinarith [hheight]
  unfold pin
  rw [normal_source heq, hr, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hn : ‖U-chordMid P Q‖ ≠ 0 := ne_of_gt hh
  rw [div_self hn, one_smul]
  abel

end
end N11Formalization.TrueCirclePin
#check @N11Formalization.TrueCirclePin.pin_circle_equations
#check @N11Formalization.TrueCirclePin.pin_source
#print axioms N11Formalization.TrueCirclePin.pin_circle_equations
#print axioms N11Formalization.TrueCirclePin.pin_source
