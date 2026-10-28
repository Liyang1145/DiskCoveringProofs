import N11Formalization
set_option autoImplicit false

#check @N11Formalization.ReflectionCovectorLift.invariant_zero_of_fixed_zero
#check @N11Formalization.ReflectionCovectorLift.invariant_zero_of_fixed_zero_apply
#print axioms N11Formalization.ReflectionCovectorLift.invariant_zero_of_fixed_zero

example
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (σ : E →ₗ[ℝ] E)
    (hσ : ∀ x : E, σ (σ x) = x)
    (ℓ : E →ₗ[ℝ] ℝ)
    (hinv : ∀ x : E, ℓ (σ x) = ℓ x)
    (hfixed : ∀ x : E, σ x = x → ℓ x = 0) (x : E) :
    ℓ x = 0 :=
  N11Formalization.ReflectionCovectorLift.invariant_zero_of_fixed_zero_apply
    σ hσ ℓ hinv hfixed x
