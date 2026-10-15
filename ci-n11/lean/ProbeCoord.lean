import Mathlib

namespace ProbeCoord

def coord (i : Fin 7) : (Fin 7 → ℝ) →L[ℝ] ℝ where
  toFun := fun v => v i
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

example (i : Fin 7) (v : Fin 7 → ℝ) : coord i v = v i := rfl

example (i : Fin 7) (x : Fin 7 → ℝ) : HasFDerivAt (fun z : Fin 7 → ℝ => z i) (coord i) x :=
  ContinuousLinearMap.hasFDerivAt (f := coord i) (x := x)

example (i : Fin 7) (v : Fin 7 → ℝ) : fderiv ℝ (fun z : Fin 7 → ℝ => z i) 0 v = v i := by
  rw [ContinuousLinearMap.hasFDerivAt.fderiv (f := coord i) (x := 0)]
  rfl

example (a : Fin 7 → ℝ) (i₀ : Fin 7) :
    ∑ i : Fin 7, a i * (Pi.single i₀ 1 : Fin 7 → ℝ) i = a i₀ := by
  classical
  refine Finset.sum_eq_single (s := Finset.univ) i₀ ?_ ?_
  · intro b _ hb
    rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

example (a : Fin 7 → ℝ) (i₀ : Fin 7) :
    ∑ i : Fin 7, a i * (Pi.single i₀ 1 : Fin 7 → ℝ) i = a i₀ := by
  classical
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

end ProbeCoord
