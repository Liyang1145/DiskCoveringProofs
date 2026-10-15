import Mathlib
import N11Formalization.Leaf4348Dispatch

/-!
  **Leaf 4348 radius consumer -- DRAFT.**

  No `sorry`/custom `axiom`/`native_decide`.  Inputs are explicit and local: the leaf's DBM cell
  and a `Feasible (circleMap o theta y) C Z r`; the conclusion is `T < r`.  This is NOT an
  unrestricted cover statement and NOT an accepted result: every interface it consumes is still
  going through the serial gate queue.
-/

namespace N11Formalization.Leaf4348Radius

open Finset ResumeNetwork ResumeDirichlet ResumeHarmonic ResumeSchurEnergy
open N11Formalization.FlashCosine (Lq LQ Dq DQ Lc Dc tval zval zval_eq theta)

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 400000000

/-- Feasible network radii at this leaf's chart points exceed the frozen threshold. -/
theorem leaf4348_radius_gt (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : N11Formalization.FlashLeafSplit.Cell
      (fun i j => (N11Formalization.Leaf4348LP.dbm i j : ℝ))
      (N11Formalization.FlashLeafSplit.tlift y))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : Feasible (fun j => circleMap (theta y j)) C Z r) :
    (N11Formalization.Leaf4348LP.T : ℝ) < r := by
  have hlo := N11Formalization.Leaf4348Dispatch.leaf4348_oracle_gt y hy0 hy1 hcell
  have hhi := oracle_le_feasible hf
  have ht : (0 : ℝ) ≤ (N11Formalization.Leaf4348LP.T : ℝ) := by
    norm_num [N11Formalization.Leaf4348LP.T]
  have hr := hf.1
  nlinarith

#print axioms N11Formalization.Leaf4348Radius.leaf4348_radius_gt

end N11Formalization.Leaf4348Radius
