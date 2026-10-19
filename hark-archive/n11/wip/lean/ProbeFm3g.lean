import N11Formalization.Interval.Range
namespace N11Formalization
namespace RatInterval
example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨4, by omega⟩ = 5 := by
  simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
example : (![1, 2, 3, 4, 5, 6, 7, 8, 9] : Fin 9 → ℕ) ⟨4, by omega⟩ = 5 := by
  fin_cases (show Fin 9 from ⟨4, by omega⟩) <;> simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
-- 展开一个具体坐标的区间向量（复现 ResidualInterval 的用法）
example (q : Fin 12 → ℚ) : True := by
  have h : (fun k : Fin 9 => (![ofRat (q 0), ofRat (q 1), ofRat (q 2), ofRat (q 3), ofRat (q 4), ofRat (q 5), ofRat (q 6), ofRat (q 7), ofRat (q 8)] : Fin 9 → RatInterval) k) 4 = ofRat (q 4) := by
    simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  trivial
end RatInterval
end N11Formalization
