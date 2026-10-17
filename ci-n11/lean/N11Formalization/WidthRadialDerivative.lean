import Mathlib
set_option autoImplicit false
namespace N11Formalization.WidthRadialDerivative
noncomputable section

def rhoMinus (R a : ℝ) : ℝ := Real.cos a - Real.sqrt (R^2 - Real.sin a^2)
def widthSlope (R a : ℝ) : ℝ := Real.sin a * rhoMinus R a / Real.sqrt (R^2-Real.sin a^2)

/-- Exact derivative in the half-width coordinate on the strict inner-root branch. -/
theorem hasDerivAt_rhoMinus_width (R a : ℝ) (hrad : 0 < R^2 - Real.sin a^2) :
    HasDerivAt (rhoMinus R) (widthSlope R a) a := by
  have hs := (Real.hasDerivAt_sin a).pow 2
  have hradD := hs.const_sub (R^2)
  have hsq := hradD.sqrt (ne_of_gt hrad)
  have h := (Real.hasDerivAt_cos a).sub hsq
  have hd : -Real.sin a - (-(2 * Real.sin a ^ (2-1) * Real.cos a)) /
      (2 * Real.sqrt (R^2 - Real.sin a^2)) = widthSlope R a := by
    unfold widthSlope rhoMinus
    have hn := ne_of_gt (Real.sqrt_pos.mpr hrad)
    simp only [show (2-1 : ℕ) = 1 from rfl, pow_one]
    field_simp
    <;> ring
  change HasDerivAt (rhoMinus R)
    (-Real.sin a - (-(2 * Real.sin a ^ (2-1) * Real.cos a)) /
      (2 * Real.sqrt (R^2 - Real.sin a^2))) a at h
  rw [hd] at h
  exact h

/-- Positivity of the inner radial root from cos positivity and R^2<1. -/
theorem rhoMinus_pos (R a : ℝ) (hcos : 0 < Real.cos a)
    (hrad : 0 ≤ R^2 - Real.sin a^2) (hR : R^2 < 1) :
    0 < rhoMinus R a := by
  have hs := Real.sq_sqrt hrad
  have hc := Real.sin_sq_add_cos_sq a
  have hsn := Real.sqrt_nonneg (R^2 - Real.sin a^2)
  unfold rhoMinus
  nlinarith

/-- The half-width/radius coordinate change is nondegenerate on the legal strict branch.
No assertion is made at width=0 or radicand=0. -/
theorem widthSlope_pos (R a : ℝ) (hsin : 0 < Real.sin a)
    (hcos : 0 < Real.cos a) (hrad : 0 < R^2-Real.sin a^2) (hR : R^2 < 1) :
    0 < widthSlope R a := by
  exact div_pos (mul_pos hsin (rhoMinus_pos R a hcos hrad.le hR))
    (Real.sqrt_pos.mpr hrad)

/-- Calibration on the degenerate width=0 branch: derivative vanishes, hence the
nondegeneracy theorem must not be applied there. -/
theorem widthSlope_zero_width (R : ℝ) : widthSlope R 0 = 0 := by
  simp [widthSlope]

theorem source_rho_eq (R a : ℝ) : rhoMinus R a = Real.cos a - Real.sqrt (R^2-Real.sin a^2) := rfl
end
end N11Formalization.WidthRadialDerivative
#print N11Formalization.WidthRadialDerivative.hasDerivAt_rhoMinus_width
#print axioms N11Formalization.WidthRadialDerivative.hasDerivAt_rhoMinus_width
#print axioms N11Formalization.WidthRadialDerivative.widthSlope_pos
#print axioms N11Formalization.WidthRadialDerivative.widthSlope_zero_width
