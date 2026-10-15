import N11Formalization.Interval.Range

/-! 探针 3b：找出 `Decidable (inWindow A k)` 卡在哪一步 -/

namespace N11Formalization

namespace RatInterval

example (k : ℤ) : Decidable (0 ≤ k) := inferInstance

example (A : RatInterval) : Decidable (-1 ≤ A.lo) := inferInstance

example (A : RatInterval) (k : ℤ) : Decidable (-1 ≤ A.lo - (if 0 ≤ k then k * halfPiHi else k * halfPiLo)) :=
  inferInstance

example (A : RatInterval) (k : ℤ) :
    Decidable (-1 ≤ A.lo - (if 0 ≤ k then (k : ℚ) * halfPiHi else (k : ℚ) * halfPiLo)) :=
  inferInstance

example (A : RatInterval) (k : ℤ) : Decidable (A.lo - (if 0 ≤ k then k * halfPiLo else k * halfPiHi) ≤ 1) :=
  inferInstance

example (A : RatInterval) (k : ℤ) : Decidable (¬ (0 ≤ k)) := inferInstance

end RatInterval

end N11Formalization
