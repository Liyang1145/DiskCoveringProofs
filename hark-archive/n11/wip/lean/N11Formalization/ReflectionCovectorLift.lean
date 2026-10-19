import Mathlib

/-!
Pure linear reflection lift. If a covector is invariant under an involution and
vanishes on the fixed subspace, it vanishes everywhere. The theorem is
coordinate-free and intentionally leaves the geometric proof of invariance and
fixed-subspace stationarity to its consumers.
-/
set_option autoImplicit false
namespace N11Formalization.ReflectionCovectorLift
noncomputable section

theorem invariant_zero_of_fixed_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (σ : E →ₗ[ℝ] E)
    (hσ : ∀ x : E, σ (σ x) = x)
    (ℓ : E →ₗ[ℝ] ℝ)
    (hinv : ∀ x : E, ℓ (σ x) = ℓ x)
    (hfixed : ∀ x : E, σ x = x → ℓ x = 0) :
    ℓ = 0 := by
  apply LinearMap.ext
  intro x
  have hplus : σ (x + σ x) = x + σ x := by
    simp only [map_add, hσ]
    ac_rfl
  have hminus : ℓ (x - σ x) = 0 := by
    rw [map_sub, hinv]
    simp
  have hfixedplus : ℓ (x + σ x) = 0 := hfixed _ hplus
  have hdecomp : (2 : ℝ) • x = (x + σ x) + (x - σ x) := by
    module
  calc
    ℓ x = (2 : ℝ)⁻¹ * ℓ ((2 : ℝ) • x) := by
      rw [map_smul]
      simp [smul_eq_mul, mul_comm]
    _ = (2 : ℝ)⁻¹ * ℓ ((x + σ x) + (x - σ x)) := by rw [hdecomp]
    _ = 0 := by rw [map_add, hfixedplus, hminus, add_zero, mul_zero]

theorem invariant_zero_of_fixed_zero_apply
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (σ : E →ₗ[ℝ] E)
    (hσ : ∀ x : E, σ (σ x) = x)
    (ℓ : E →ₗ[ℝ] ℝ)
    (hinv : ∀ x : E, ℓ (σ x) = ℓ x)
    (hfixed : ∀ x : E, σ x = x → ℓ x = 0) (x : E) :
    ℓ x = 0 :=
  congrArg (fun m : E →ₗ[ℝ] ℝ => m x)
    (invariant_zero_of_fixed_zero σ hσ ℓ hinv hfixed)

end
end N11Formalization.ReflectionCovectorLift
#check @N11Formalization.ReflectionCovectorLift.invariant_zero_of_fixed_zero
#print axioms N11Formalization.ReflectionCovectorLift.invariant_zero_of_fixed_zero
