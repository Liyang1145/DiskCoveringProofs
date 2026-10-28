import N11Formalization.PinTangentGeometry
set_option autoImplicit false
namespace N11Formalization.PinCircleDifferential
open N11Formalization PinTangentGeometry
noncomputable section

/-- Differentiating the actual squared distance equation yields its normal velocity row.
The radius curve is allowed to vary; no off-locus reflected construction is used. -/
theorem circle_velocity_row {U P : ℝ → Point} {R : ℝ → ℝ}
    {u' p' : Point} {r' t : ℝ}
    (hu : HasDerivAt U u' t) (hp : HasDerivAt P p' t) (hr : HasDerivAt R r' t)
    (he : ∀ᶠ s in nhds t, ‖U s - P s‖^2 = (R s)^2) :
    inner ℝ (U t - P t) (u'-p') = R t * r' := by
  have hd := hu.sub hp
  have hi := hd.inner ℝ hd
  have hi' : HasDerivAt (fun s => ‖U s - P s‖^2)
      (2 * inner ℝ (U t - P t) (u'-p')) t := by
    have hv : inner ℝ (U t - P t) (u'-p') + inner ℝ (u'-p') (U t - P t) =
        2 * inner ℝ (U t - P t) (u'-p') := by
      rw [real_inner_comm (u'-p') (U t-P t)]
      ring
    simpa only [Pi.sub_apply, real_inner_self_eq_norm_sq, hv] using hi
  have he' : (fun s => (R s)^2) =ᶠ[nhds t] (fun s => ‖U s-P s‖^2) := by
    filter_upwards [he] with s hs
    exact hs.symm
  have hh := hi'.congr_of_eventuallyEq he'
  have hhR := hr.pow 2
  have heq := hh.unique hhR
  norm_num only [show (2-1:ℕ)=1 from rfl, pow_one, Nat.cast_ofNat] at heq
  linarith

/-- Two differentiable true equal-circle pin curves that start on the same nondegenerate
branch and follow the same centers/radius have the same derivative. -/
theorem two_pin_curves_derivative_eq {U V P Q : ℝ → Point} {R : ℝ → ℝ}
    {u' v' p' q' : Point} {r' t : ℝ}
    (hu : HasDerivAt U u' t) (hv : HasDerivAt V v' t)
    (hp : HasDerivAt P p' t) (hq : HasDerivAt Q q' t) (hr : HasDerivAt R r' t)
    (hUV : U t = V t) (hn : det (U t-P t) (U t-Q t) ≠ 0)
    (huP : ∀ᶠ s in nhds t, ‖U s-P s‖^2 = (R s)^2)
    (huQ : ∀ᶠ s in nhds t, ‖U s-Q s‖^2 = (R s)^2)
    (hvP : ∀ᶠ s in nhds t, ‖V s-P s‖^2 = (R s)^2)
    (hvQ : ∀ᶠ s in nhds t, ‖V s-Q s‖^2 = (R s)^2) : u'=v' := by
  have h1 := circle_velocity_row hu hp hr huP
  have h2 := circle_velocity_row hv hp hr hvP
  have h3 := circle_velocity_row hu hq hr huQ
  have h4 := circle_velocity_row hv hq hr hvQ
  rw [← hUV] at h2 h4
  apply tangent_unique hn
  · simp only [inner_sub_right] at h1 h2
    linarith
  · simp only [inner_sub_right] at h3 h4
    linarith

end
end N11Formalization.PinCircleDifferential
#check @N11Formalization.PinCircleDifferential.circle_velocity_row
#check @N11Formalization.PinCircleDifferential.two_pin_curves_derivative_eq
#print axioms N11Formalization.PinCircleDifferential.two_pin_curves_derivative_eq
