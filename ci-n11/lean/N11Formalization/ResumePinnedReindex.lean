import N11Formalization.ResumeLocalIncidence

namespace N11Formalization.ResumeLocalIncidence

/-- Raw index k is canonical k-2. This is a relabelling together with the
fixed graph incidence map, NOT a cyclic symmetry of the canonical graph. -/
def canonRawEquiv : Fin 9 ≃ Fin 9 where
  toFun := fun i => i + 2
  invFun := siteMap
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

def canonReindex {α : Type*} (v : Fin 9 → α) : Fin 9 → α :=
  fun i => v (canonRawEquiv i)

theorem canonReindex_source {α : Type*} (v : Fin 9 → α) (k : Fin 9) :
    canonReindex v (siteMap k) = v k := by
  exact congrArg v (canonRawEquiv.apply_symm_apply k)

/-- The actual local source pins raw8, hence canonical6 (not canonical8). -/
theorem canonReindex_pin (x : Fin 9 → ℝ) (h : x 8 = 0) :
    canonReindex x 6 = 0 := h

theorem sum_canonReindex_sq (x : Fin 9 → ℝ) :
    ∑ i, (canonReindex x i) ^ 2 = ∑ k, (x k) ^ 2 := by
  exact Equiv.sum_comp canonRawEquiv (fun k => (x k)^2)

/-- Rotation-normalized displacement transport from raw8 to canonical6. -/
theorem canonReindex_displacement (θ β : Fin 9 → ℝ) (i : Fin 9) :
    canonReindex (fun k => (θ k - θ 8) - (β k - β 8)) i =
      (canonReindex θ i - canonReindex θ 6) -
        (canonReindex β i - canonReindex β 6) := rfl

#print axioms canonReindex_source
#print axioms canonReindex_pin
#print axioms sum_canonReindex_sq
#print axioms canonReindex_displacement
end N11Formalization.ResumeLocalIncidence
