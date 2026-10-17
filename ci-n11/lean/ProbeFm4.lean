import N11Formalization.Interval.Range

/-! 探针 4：`![...]` 在 `Fin 5`/`Fin 9` 上、对 `fin_cases` 产生的字面下标的归约 —— 精确复现 `ResidualInterval.lean` 的失败模式 -/

namespace N11Formalization

namespace RatInterval

example : (0 : Fin 5) = ⟨0, by omega⟩ := rfl

example : (4 : Fin 9) = ⟨4, by omega⟩ := rfl

example : 0 % 9 = 0 := rfl

example : (![ofRat (1 / 2), ofRat (1 / 3), ofRat 1, ofRat 2, ofRat 3] : Fin 5 → RatInterval)
    ⟨0, by omega⟩ = ofRat (1 / 2) := by
  simp only [Matrix.cons_val_zero]

example (k : Fin 5) : (![ofRat (1 / 2), ofRat (1 / 3), ofRat 1, ofRat 2, ofRat 3] : Fin 5 → RatInterval)
    k = (![ofRat (1 / 2), ofRat (1 / 3), ofRat 1, ofRat 2, ofRat 3] : Fin 5 → RatInterval) k := by
  fin_cases k <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ', Matrix.cons_val_fin_one]

-- 完整复现：定义 + mem 引理（与 ResidualInterval 同构，只是 3 槽）
def aVec (q : Fin 12 → ℚ) : Fin 3 → RatInterval :=
  ![ofRat (q 0), ofRat (q 1), sub piI (mul (ofRat 2) (ofRat (q 0)))]

def aVecR (u : Fin 12 → ℝ) : Fin 3 → ℝ := ![u 0, u 1, Real.pi - 2 * u 0]

theorem aVec_mem (q : Fin 12 → ℚ) (k : Fin 3) :
    ((aVec q k)).Mem (aVecR (fun i => ((q i : ℚ) : ℝ)) k) := by
  fin_cases k <;>
    simp only [aVec, aVecR, Matrix.cons_val_zero, Matrix.cons_val_succ', Matrix.cons_val_fin_one] <;>
    repeat first
      | exact ofRat_mem _
      | exact piI_mem
      | apply sub_mem
      | apply mul_mem

end RatInterval

end N11Formalization
