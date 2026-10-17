import N11Formalization.OpNorm
import N11Formalization.Assembly.G1
import N11Formalization.Interval.Vector

open Metric

namespace N11Formalization

example {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {Q : ℝ}
    (hQ : 0 ≤ Q) (J : Fin n → Fin n → RatInterval)
    (henc : ∀ i j : Fin n, (J i j).Mem (A (Pi.single j 1) i)) : True := trivial

example (J : Fin 12 → Fin 12 → RatInterval) : (J 0 0).lo = (J 0 0).lo := rfl

end N11Formalization
