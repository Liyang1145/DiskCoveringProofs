import N11Formalization.ActualSharedMomentRationalCertificate

/-! A rational sine check supplies an arbitrary certified upper bracket
for the actual selected-ear arcsine constant. This refines the weak-dual
constant without changing the covering radius or any geometric premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSharedMomentSharpConstant
open ActualSharedMomentRationalCertificate ActualFiniteNearestRefinement
open MetricAreaRationalCertificate

structure EarAsinBracket (alpha : ℚ) : Prop where
  endpoint : alpha ∈ Set.Icc (0 : ℚ) 1
  sine : (19/25 : ℚ) ≤ sinLoNLag alpha

theorem arcsin_upper_of_bracket {alpha : ℚ} (h : EarAsinBracket alpha) :
    Real.arcsin (19/25 : ℝ) ≤ (alpha : ℝ) := by
  have ha0 : (0 : ℝ) ≤ (alpha : ℝ) := by exact_mod_cast h.endpoint.1
  have ha1 : (alpha : ℝ) ≤ 1 := by exact_mod_cast h.endpoint.2
  have ha : (alpha : ℝ) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith only [ha0,ha1,Real.pi_gt_three]
  have hs : (19/25 : ℝ) ≤ (sinLoNLag alpha : ℝ) := by
    have hh : ((19/25 : ℚ) : ℝ) ≤ (sinLoNLag alpha : ℝ) := Rat.cast_le.mpr h.sine
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
    exact hh
  exact (Real.arcsin_le_iff_le_sin (by constructor <;> norm_num) ha).mpr
    (hs.trans (sinLoNLag_le_sin alpha))

theorem ear_asin_863314 : EarAsinBracket (863314/1000000 : ℚ) := by
  constructor
  · norm_num
  · norm_num [sinLoNLag,sinTQ,Finset.sum_range_succ]

def sharpConstantUpperQ {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) (eta alpha : ℚ) : ℚ :=
  piProductUpper (constantCoeffQ D kap eta)+2*alpha*eta

theorem dualConstant_upper_of_bracket {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ)
    (eta alpha : ℚ) (heta : 0 ≤ eta) (ha : EarAsinBracket alpha) :
    ActualSharedMomentMaskedDual.dualConstant D.toReal (fun e => (kap e : ℝ)) eta ≤
      (sharpConstantUpperQ D kap eta alpha : ℝ) := by
  have hp := pi_product_upper (constantCoeffQ D kap eta)
  have hb := mul_le_mul_of_nonneg_right (arcsin_upper_of_bracket ha)
    (show (0 : ℝ) ≤ eta by exact_mod_cast heta)
  have he : ActualSharedMomentMaskedDual.dualConstant D.toReal (fun e => (kap e : ℝ)) eta=
      (constantCoeffQ D kap eta : ℝ)*Real.pi+2*Real.arcsin (19/25)*(eta : ℝ) := by
    unfold ActualSharedMomentMaskedDual.dualConstant
    rw [stationConstant_cast]
    unfold constantCoeffQ CoeffQ.toReal
    push_cast
    ring
  rw [he]
  unfold sharpConstantUpperQ
  push_cast
  linarith only [hp,hb]

end N11Formalization.ActualSharedMomentSharpConstant
#check @N11Formalization.ActualSharedMomentSharpConstant.dualConstant_upper_of_bracket
#print axioms N11Formalization.ActualSharedMomentSharpConstant.arcsin_upper_of_bracket
#print axioms N11Formalization.ActualSharedMomentSharpConstant.ear_asin_863314
#print axioms N11Formalization.ActualSharedMomentSharpConstant.dualConstant_upper_of_bracket
