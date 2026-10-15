import N11Formalization.Interval.Range
namespace N11Formalization
namespace RatInterval
example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨0, by omega⟩ = 1 := by
  simp only [Matrix.cons_val_zero]
example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨0, by omega⟩ = 1 := by
  simp only [Matrix.cons_val_zero']
example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨4, by omega⟩ = 5 := by
  simp only [Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_fin_one]
example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨4, by omega⟩ = 5 := by
  norm_num
example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨8, by omega⟩ = 9 := by
  simp only [Matrix.cons_val_succ', Matrix.cons_val_zero', Matrix.cons_val_fin_one]
example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨8, by omega⟩ = 9 := by
  decide
end RatInterval
end N11Formalization
