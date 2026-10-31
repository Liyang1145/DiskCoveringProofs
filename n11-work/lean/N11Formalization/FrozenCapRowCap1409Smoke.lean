import N11Formalization.FrozenCapRationalCore
import Mathlib.Tactic.NormNum

/-! Two-leaf proof-pattern smoke test for generated node-1409 row caps.
Diagnostic only; this does not claim a packet or residual payment. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapRowCap1409Smoke
open N11Formalization.FrozenCapRationalCore
noncomputable section

def rowA (i j : Fin 10) (q : Fin 9) : ℚ :=
  (if q.val < j.val then 1 else 0) - (if q.val < i.val then 1 else 0)

theorem leaf_0_1 :
    y_1409 (0 : Fin 9) * rowA (0 : Fin 10) (1 : Fin 10) (0 : Fin 9) +
    y_1409 (1 : Fin 9) * rowA (0 : Fin 10) (1 : Fin 10) (1 : Fin 9) +
    y_1409 (2 : Fin 9) * rowA (0 : Fin 10) (1 : Fin 10) (2 : Fin 9) +
    y_1409 (3 : Fin 9) * rowA (0 : Fin 10) (1 : Fin 10) (3 : Fin 9) +
    y_1409 (4 : Fin 9) * rowA (0 : Fin 10) (1 : Fin 10) (4 : Fin 9) +
    y_1409 (5 : Fin 9) * rowA (0 : Fin 10) (1 : Fin 10) (5 : Fin 9) +
    y_1409 (6 : Fin 9) * rowA (0 : Fin 10) (1 : Fin 10) (6 : Fin 9) +
    y_1409 (7 : Fin 9) * rowA (0 : Fin 10) (1 : Fin 10) (7 : Fin 9) +
    y_1409 (8 : Fin 9) * rowA (0 : Fin 10) (1 : Fin 10) (8 : Fin 9) ≤
      (1 : ℚ) / 4 := by
  change (0 : ℚ) ≤ (1 : ℚ) / 4
  norm_num

theorem leaf_5_4 :
    y_1409 (0 : Fin 9) * rowA (5 : Fin 10) (4 : Fin 10) (0 : Fin 9) +
    y_1409 (1 : Fin 9) * rowA (5 : Fin 10) (4 : Fin 10) (1 : Fin 9) +
    y_1409 (2 : Fin 9) * rowA (5 : Fin 10) (4 : Fin 10) (2 : Fin 9) +
    y_1409 (3 : Fin 9) * rowA (5 : Fin 10) (4 : Fin 10) (3 : Fin 9) +
    y_1409 (4 : Fin 9) * rowA (5 : Fin 10) (4 : Fin 10) (4 : Fin 9) +
    y_1409 (5 : Fin 9) * rowA (5 : Fin 10) (4 : Fin 10) (5 : Fin 9) +
    y_1409 (6 : Fin 9) * rowA (5 : Fin 10) (4 : Fin 10) (6 : Fin 9) +
    y_1409 (7 : Fin 9) * rowA (5 : Fin 10) (4 : Fin 10) (7 : Fin 9) +
    y_1409 (8 : Fin 9) * rowA (5 : Fin 10) (4 : Fin 10) (8 : Fin 9) ≤
      (1 : ℚ) / 2 := by
  change (1 : ℚ) / 2 ≤ (1 : ℚ) / 2
  norm_num

end
end N11Formalization.FrozenCapRowCap1409Smoke
