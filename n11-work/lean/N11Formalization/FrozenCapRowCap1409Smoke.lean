import N11Formalization.FrozenCapRationalCore
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Two-leaf proof-pattern smoke test for generated node-1409 row caps.
Diagnostic only; this does not claim a packet or residual payment. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapRowCap1409Smoke
open Finset
open N11Formalization.FrozenCapRationalCore
noncomputable section

def rowA (i j : Fin 10) (q : Fin 9) : ℚ :=
  (if q.val < j.val then 1 else 0) - (if q.val < i.val then 1 else 0)

def db (i j : Fin 10) : ℚ :=
  if i.val = 0 ∧ j.val = 2 then 1 / 4
  else if i.val = 5 ∧ j.val = 4 then -1 / 8
  else 0

theorem leaf_0_2 :
    (∑ q : Fin 9, y_1409 q * rowA 0 2 q) ≤ db 0 2 := by
  norm_num [y_1409, rowA, db, Fin.sum_univ_succ]

theorem leaf_5_4 :
    (∑ q : Fin 9, y_1409 q * rowA 5 4 q) ≤ db 5 4 := by
  norm_num [y_1409, rowA, db, Fin.sum_univ_succ]

end
end N11Formalization.FrozenCapRowCap1409Smoke
