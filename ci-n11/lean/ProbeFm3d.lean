import N11Formalization.Interval.Range
namespace N11Formalization
namespace RatInterval
example (A : RatInterval) : Decidable (inWindow A 0) := inferInstance
example (A : RatInterval) (k : ℤ) : Decidable (inWindow A k) := inferInstance
example (A : RatInterval) (k : ℤ) : Decidable (inWindow A (k+1)) := inferInstance
example (A : RatInterval) : Decidable (sq A = A) := inferInstance
end RatInterval
end N11Formalization
