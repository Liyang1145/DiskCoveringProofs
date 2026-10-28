import N11Formalization.Interval.Range
namespace N11Formalization
namespace RatInterval
example (A : RatInterval) : inWindow A 0 = (-1 ≤ A.lo - (if (0:ℤ) ≤ 0 then (0:ℤ) * halfPiHi else (0:ℤ) * halfPiLo) ∧ A.hi - (if (0:ℤ) ≤ 0 then (0:ℤ) * halfPiLo else (0:ℤ) * halfPiHi) ≤ 1) := rfl
example (A : RatInterval) : Decidable A.Valid := inferInstance
example (A : RatInterval) : Decidable (-1 ≤ A.lo ∧ A.hi ≤ 1) := inferInstance
example (A : RatInterval) : Decidable (∃ k : ℤ, inWindow A k) := by classical exact inferInstance
example (A : RatInterval) (k : ℤ) : Decidable (-1 ≤ A.lo - (if 0 ≤ k then k * halfPiHi else k * halfPiLo)) := inferInstance
#check (inferInstance : Decidable (True))
end RatInterval
end N11Formalization
