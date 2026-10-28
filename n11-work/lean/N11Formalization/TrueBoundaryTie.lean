import N11Formalization.TrueCirclePinSmooth

/-!
Genuine unit-circle tie for independently moving two Cartesian centres.
The perpendicular bisector is intersected with the unit circle, using a fixed
seed to select the source branch. This is NOT a reflected off-boundary endpoint
extension. The radius function is distance to the actual tie.
-/
set_option autoImplicit false
namespace N11Formalization.TrueBoundaryTie
open N11Formalization TrueCirclePin PinTangentGeometry
noncomputable section

def offset (P Q : Point) : ℝ := (‖Q‖^2-‖P‖^2)/(2*‖Q-P‖^2)
def foot (P Q : Point) : Point := offset P Q • (Q-P)
def rad (P Q : Point) : ℝ := 1-‖foot P Q‖^2
def tie (W P Q : Point) : Point :=
  foot P Q + (Real.sqrt (rad P Q)/‖normal W P Q‖) • normal W P Q
def radius (W P Q : Point) : ℝ := ‖tie W P Q-P‖

theorem foot_row (P Q : Point) (hPQ : P≠Q) :
    inner ℝ (foot P Q) (Q-P)=(‖Q‖^2-‖P‖^2)/2 := by
  have hN : ‖Q-P‖^2≠0 := pow_ne_zero 2
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hPQ.symm))
  rw [foot,real_inner_smul_left,real_inner_self_eq_norm_sq,offset]
  field_simp [hN,norm_ne_zero_iff.mpr (sub_ne_zero.mpr hPQ.symm)]

theorem tie_equations (W P Q : Point) (hPQ : P≠Q)
    (hN : normal W P Q≠0) (hr : 0≤rad P Q) :
    ‖tie W P Q‖=1 ∧ ‖tie W P Q-P‖=‖tie W P Q-Q‖ := by
  let N := normal W P Q
  let V := (Real.sqrt (rad P Q)/‖N‖) • N
  have hn : ‖N‖≠0 := norm_ne_zero_iff.mpr hN
  have ho := normal_orthogonal W P Q hPQ
  have ho' : inner ℝ (Q-P) (normal W P Q)=0 := (real_inner_comm _ _).trans ho
  have hv : ‖V‖^2=rad P Q := by
    dsimp [V]
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow,Real.sq_sqrt hr]
    field_simp [hn]
  have horth : inner ℝ (foot P Q) V=0 := by
    rw [foot]
    dsimp [V,N]
    rw [real_inner_smul_left,real_inner_smul_right,ho']
    ring
  have hu : ‖tie W P Q‖^2=1 := by
    change ‖foot P Q+V‖^2=1
    rw [norm_add_sq_real,horth,hv]
    unfold rad
    ring
  have hrow : inner ℝ (tie W P Q) (Q-P)=(‖Q‖^2-‖P‖^2)/2 := by
    rw [tie,inner_add_left,real_inner_smul_left,ho,mul_zero,add_zero,foot_row P Q hPQ]
  have heq : ‖tie W P Q-P‖^2=‖tie W P Q-Q‖^2 := by
    rw [inner_sub_right] at hrow
    rw [norm_sub_sq_real,norm_sub_sq_real]
    linarith
  constructor
  · nlinarith [norm_nonneg (tie W P Q)]
  · nlinarith [norm_nonneg (tie W P Q-P),norm_nonneg (tie W P Q-Q)]

theorem equidistant_row {P Q T : Point} (he : ‖T-P‖=‖T-Q‖) :
    inner ℝ T (Q-P)=(‖Q‖^2-‖P‖^2)/2 := by
  have h := congrArg (fun r : ℝ => r^2) he
  rw [norm_sub_sq_real,norm_sub_sq_real] at h
  rw [inner_sub_right]
  linarith

theorem seed_orthogonal {P Q T : Point} (hPQ : P≠Q) (he : ‖T-P‖=‖T-Q‖) :
    inner ℝ (T-foot P Q) (Q-P)=0 := by
  rw [inner_sub_left,equidistant_row he,foot_row P Q hPQ,sub_self]

theorem normal_seed {P Q T : Point} (hPQ : P≠Q) (he : ‖T-P‖=‖T-Q‖) :
    normal (T-foot P Q) P Q=T-foot P Q := by
  simp only [normal,seed_orthogonal hPQ he,zero_div,zero_smul,sub_zero]

theorem source_rad {P Q T : Point} (hPQ : P≠Q) (hunit : ‖T‖=1)
    (he : ‖T-P‖=‖T-Q‖) :
    rad P Q=‖T-foot P Q‖^2 := by
  have ho : inner ℝ (T-foot P Q) (foot P Q)=0 := by
    have hfoot : inner ℝ (T-foot P Q) (foot P Q) =
        offset P Q * inner ℝ (T-foot P Q) (Q-P) :=
      real_inner_smul_right _ _ _
    rw [hfoot,seed_orthogonal hPQ he,mul_zero]
  have hu : T=(T-foot P Q)+foot P Q := by abel
  have hs := norm_add_sq_real (T-foot P Q) (foot P Q)
  rw [← hu,ho,hunit] at hs
  unfold rad
  nlinarith

/-- Exact branch binding, not merely equidistance on the unit circle. -/
theorem tie_source {P Q T : Point} (hPQ : P≠Q) (hunit : ‖T‖=1)
    (he : ‖T-P‖=‖T-Q‖) (hN : T-foot P Q≠0) :
    tie (T-foot P Q) P Q=T := by
  rw [tie,normal_seed hPQ he,source_rad hPQ hunit he,
    Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hN),one_smul]
  abel

/-- Tangency cannot occur at an equidistant unit-circle point when both centres
are strictly inside the unit disk. This pays branch nondegeneracy geometrically,
without a sampled determinant or interval-containing-zero argument. -/
theorem seed_ne_of_inside {P Q T : Point} (hPQ : P≠Q) (hunit : ‖T‖=1)
    (he : ‖T-P‖=‖T-Q‖) (hP : ‖P‖<1) (hQ : ‖Q‖<1) :
    T-foot P Q≠0 := by
  intro hzero
  have hT : T=foot P Q := sub_eq_zero.mp hzero
  have hsum : inner ℝ (Q-P) (P+Q)=‖Q‖^2-‖P‖^2 := by
    rw [inner_sub_left,inner_add_right,inner_add_right,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_comm Q P]
    ring
  have htotal : inner ℝ T (P+Q)=offset P Q*(‖Q‖^2-‖P‖^2) := by
    rw [hT,foot,real_inner_smul_left,hsum]
  have hn : inner ℝ T T=1 := by rw [real_inner_self_eq_norm_sq,hunit]; norm_num
  have hn' : offset P Q * inner ℝ T (Q-P)=1 := by
    calc
      _ = inner ℝ T (foot P Q) := (real_inner_smul_right _ _ _).symm
      _ = inner ℝ T T := by rw [← hT]
      _ = 1 := hn
  rw [equidistant_row he] at hn'
  have hab : inner ℝ T P+inner ℝ T Q=2 := by
    rw [inner_add_right] at htotal
    nlinarith [hn']
  have hpI : inner ℝ T P<1 := lt_of_le_of_lt
    (real_inner_le_norm T P) (by simpa only [hunit,one_mul] using hP)
  have hqI : inner ℝ T Q<1 := lt_of_le_of_lt
    (real_inner_le_norm T Q) (by simpa only [hunit,one_mul] using hQ)
  linarith

abbrev Data := TrueCirclePinSmooth.Data
def tieData (W : Point) (z : Data) : Point :=
  tie W (TrueCirclePinSmooth.left z) (TrueCirclePinSmooth.right z)

theorem foot_smooth (z : Data)
    (hPQ : TrueCirclePinSmooth.left z≠TrueCirclePinSmooth.right z) :
    ContDiffAt ℝ 1 (fun y : Data =>
      foot (TrueCirclePinSmooth.left y) (TrueCirclePinSmooth.right y)) z := by
  have hP := TrueCirclePinSmooth.left_smooth z
  have hQ := TrueCirclePinSmooth.right_smooth z
  have hD := hQ.sub hP
  have hn : 2*‖TrueCirclePinSmooth.right z-TrueCirclePinSmooth.left z‖^2≠0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hPQ.symm)))
  exact (((hQ.norm_sq ℝ).sub (hP.norm_sq ℝ)).div
    ((hD.norm_sq ℝ).const_smul (2 : ℝ)) hn).smul hD

theorem tieData_smooth (W : Point) (z : Data)
    (hPQ : TrueCirclePinSmooth.left z≠TrueCirclePinSmooth.right z)
    (hN : normal W (TrueCirclePinSmooth.left z) (TrueCirclePinSmooth.right z)≠0)
    (hr : rad (TrueCirclePinSmooth.left z) (TrueCirclePinSmooth.right z)≠0) :
    ContDiffAt ℝ 1 (tieData W) z := by
  have hF := foot_smooth z hPQ
  have hNormal := TrueCirclePinSmooth.normal_smooth W z hPQ
  have hRad := (contDiffAt_const.sub (hF.norm_sq ℝ)).sqrt hr
  exact hF.add ((hRad.div (hNormal.norm ℝ hN) (norm_ne_zero_iff.mpr hN)).smul hNormal)

end
end N11Formalization.TrueBoundaryTie
#check @N11Formalization.TrueBoundaryTie.tie_equations
#check @N11Formalization.TrueBoundaryTie.tie_source
#check @N11Formalization.TrueBoundaryTie.tieData_smooth
#print axioms N11Formalization.TrueBoundaryTie.tie_source
