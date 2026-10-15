import N11Formalization.PinCircleDifferential

/-! Coordinate-free circle-radius differential: differentiating all THREE
equal-distance equations, then using an affine centre identity, eliminates
the moving circumcentre. No acuteness or beta positivity is required for this
differential identity; positivity is a separate stress obligation. -/
set_option autoImplicit false
namespace N11Formalization.CircumradiusDifferential
open N11Formalization PinCircleDifferential
noncomputable section

theorem weighted_radius_velocity
    {Z A B C : ℝ → Point} {R : ℝ → ℝ}
    {z' a' b' c' : Point} {r' t : ℝ} (wA wB wC : ℝ)
    (hz : HasDerivAt Z z' t) (ha : HasDerivAt A a' t)
    (hb : HasDerivAt B b' t) (hc : HasDerivAt C c' t) (hr : HasDerivAt R r' t)
    (hs : wA+wB+wC=1) (hcenter : Z t=wA • A t+wB • B t+wC • C t)
    (hA : ∀ᶠ s in nhds t, ‖Z s-A s‖^2=(R s)^2)
    (hB : ∀ᶠ s in nhds t, ‖Z s-B s‖^2=(R s)^2)
    (hC : ∀ᶠ s in nhds t, ‖Z s-C s‖^2=(R s)^2) :
    R t * r' = -(wA*inner ℝ (Z t-A t) a' +
      wB*inner ℝ (Z t-B t) b'+wC*inner ℝ (Z t-C t) c') := by
  have hP := circle_velocity_row hz ha hr hA
  have hQ := circle_velocity_row hz hb hr hB
  have hH := circle_velocity_row hz hc hr hC
  have hn : wA • (Z t-A t)+wB • (Z t-B t)+wC • (Z t-C t)=0 := by
    calc
      _ = (wA+wB+wC) • Z t - (wA • A t+wB • B t+wC • C t) := by module
      _ = 0 := by rw [hs, one_smul, ← hcenter, sub_self]
  have hi := congrArg (fun n : Point => inner ℝ n z') hn
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at hi
  rw [inner_sub_right] at hP hQ hH
  linear_combination -wA * hP - wB * hQ - wC * hH + hi - (R t * r') * hs

end
end N11Formalization.CircumradiusDifferential
#check @N11Formalization.CircumradiusDifferential.weighted_radius_velocity
#print axioms N11Formalization.CircumradiusDifferential.weighted_radius_velocity
