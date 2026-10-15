import N11Formalization.Interval.Range

/-!
# fm-eval 探针 3：`![...] i` 的归约方式 + `Decidable (inWindow A (phaseOf A))` 的实例
-/

namespace N11Formalization

namespace RatInterval

/-- 探针本地副本（正式定义在 `ResidualInterval.lean`）。 -/
def phaseOf (A : RatInterval) : ℤ := ⌊(A.lo + A.hi) / 2 / halfPiLo + 1 / 2⌋

-- (a) 具体下标 4 的向量归约
example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨4, by omega⟩ = 5 := rfl

example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨4, by omega⟩ = 5 := by simp

example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨4, by omega⟩ = 5 := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]

example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨4, by omega⟩ = 5 := by
  simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]

-- (b) Decidable 实例
example (A : RatInterval) : Decidable (inWindow A 0) := inferInstance

example (A : RatInterval) : Decidable (inWindow A (3 : ℤ)) := inferInstance

example (A : RatInterval) : Decidable (inWindow A (phaseOf A)) := inferInstance

example (A : RatInterval) : Decidable (inWindow A (⌊(A.lo + A.hi) / 2 / halfPiLo + 1 / 2⌋)) :=
  inferInstance

end RatInterval

end N11Formalization
