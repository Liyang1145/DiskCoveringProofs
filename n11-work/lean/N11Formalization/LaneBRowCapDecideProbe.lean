import N11Formalization.FrozenCapRationalCore
import Mathlib.Tactic.FinCases

/-! Probe whether kernel decision proves representative frozen row caps that
the generated `norm_num` modules leave unsolved.  This is an engineering probe,
not a replacement certificate and not proof credit for the 100-row modules. -/
set_option autoImplicit false
namespace N11Formalization.LaneBRowCapDecideProbe
open Finset
open N11Formalization.FrozenCapRationalCore
noncomputable section

def rowA (i j : Fin 10) (q : Fin 9) : ℚ :=
  (if q.val < j.val then 1 else 0) - (if q.val < i.val then 1 else 0)

theorem row_0_1 :
    y_1409 0 * rowA 0 1 0 + y_1409 1 * rowA 0 1 1 +
      y_1409 2 * rowA 0 1 2 + y_1409 3 * rowA 0 1 3 +
      y_1409 4 * rowA 0 1 4 + y_1409 5 * rowA 0 1 5 +
      y_1409 6 * rowA 0 1 6 + y_1409 7 * rowA 0 1 7 +
      y_1409 8 * rowA 0 1 8 ≤ (1 : ℚ) / 4 := by
  decide +kernel

theorem row_4_5 :
    y_1409 0 * rowA 4 5 0 + y_1409 1 * rowA 4 5 1 +
      y_1409 2 * rowA 4 5 2 + y_1409 3 * rowA 4 5 3 +
      y_1409 4 * rowA 4 5 4 + y_1409 5 * rowA 4 5 5 +
      y_1409 6 * rowA 4 5 6 + y_1409 7 * rowA 4 5 7 +
      y_1409 8 * rowA 4 5 8 ≤ (1 : ℚ) / 4 := by
  decide +kernel

theorem row_9_9 :
    y_1409 0 * rowA 9 9 0 + y_1409 1 * rowA 9 9 1 +
      y_1409 2 * rowA 9 9 2 + y_1409 3 * rowA 9 9 3 +
      y_1409 4 * rowA 9 9 4 + y_1409 5 * rowA 9 9 5 +
      y_1409 6 * rowA 9 9 6 + y_1409 7 * rowA 9 9 7 +
      y_1409 8 * rowA 9 9 8 ≤ 0 := by
  decide +kernel

end
end N11Formalization.LaneBRowCapDecideProbe
#print axioms N11Formalization.LaneBRowCapDecideProbe.row_4_5
