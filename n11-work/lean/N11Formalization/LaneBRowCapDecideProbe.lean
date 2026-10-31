import N11Formalization.FrozenCapRationalCore
import Mathlib.Tactic.FinCases

/-! Probe whether explicit rational reduction proves representative frozen row
caps that the generated `norm_num` modules leave unsolved.  This is an
engineering probe, not a replacement certificate and not proof credit for the
100-row modules. -/
set_option autoImplicit false
namespace N11Formalization.LaneBRowCapDecideProbe
open Finset
open N11Formalization.FrozenCapRationalCore
noncomputable section

def rowA (i j : Fin 10) (q : Fin 9) : ℚ :=
  (if q.val < j.val then 1 else 0) - (if q.val < i.val then 1 else 0)

def dbmVal : Fin 10 → Fin 10 → ℤ
  | i, j => ![
    ![0, 1024, 1024, 1024, 2048, 3072, 3072, 3072, 3584, 4096],
    ![0, 0, 1024, 1024, 2048, 3072, 3072, 3072, 3584, 4096],
    ![0, 0, 0, 1024, 2048, 3072, 3072, 3072, 3584, 4096],
    ![0, 0, 0, 0, 1536, 2048, 2048, 2048, 2560, 4096],
    ![-1536, -512, -512, -512, 0, 1024, 1024, 1024, 1536, 2560],
    ![-2048, -1536, -1536, -1536, -512, 0, 512, 512, 512, 2048],
    ![-2048, -1536, -1536, -1536, -512, 0, 0, 512, 512, 2048],
    ![-2048, -1536, -1536, -1536, -512, 0, 0, 0, 512, 2048],
    ![-2560, -2048, -2048, -2048, -1024, 0, 0, 0, 0, 1536],
    ![-4096, -3072, -3072, -3072, -2048, -1024, -1024, -1024, -512, 0]
  ] i j

def db (i j : Fin 10) : ℚ := (dbmVal i j : ℚ) / 4096

theorem row_0_1 :
    y_1409 0 * rowA 0 1 0 + y_1409 1 * rowA 0 1 1 +
      y_1409 2 * rowA 0 1 2 + y_1409 3 * rowA 0 1 3 +
      y_1409 4 * rowA 0 1 4 + y_1409 5 * rowA 0 1 5 +
      y_1409 6 * rowA 0 1 6 + y_1409 7 * rowA 0 1 7 +
      y_1409 8 * rowA 0 1 8 ≤ db 0 1 := by
  norm_num [y_1409, rowA, db, dbmVal]
  simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  norm_num

theorem row_4_5 :
    y_1409 0 * rowA 4 5 0 + y_1409 1 * rowA 4 5 1 +
      y_1409 2 * rowA 4 5 2 + y_1409 3 * rowA 4 5 3 +
      y_1409 4 * rowA 4 5 4 + y_1409 5 * rowA 4 5 5 +
      y_1409 6 * rowA 4 5 6 + y_1409 7 * rowA 4 5 7 +
      y_1409 8 * rowA 4 5 8 ≤ db 4 5 := by
  norm_num [y_1409, rowA, db, dbmVal]
  simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  norm_num

theorem row_9_9 :
    y_1409 0 * rowA 9 9 0 + y_1409 1 * rowA 9 9 1 +
      y_1409 2 * rowA 9 9 2 + y_1409 3 * rowA 9 9 3 +
      y_1409 4 * rowA 9 9 4 + y_1409 5 * rowA 9 9 5 +
      y_1409 6 * rowA 9 9 6 + y_1409 7 * rowA 9 9 7 +
      y_1409 8 * rowA 9 9 8 ≤ db 9 9 := by
  norm_num [y_1409, rowA, db, dbmVal]
  simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  norm_num

end
end N11Formalization.LaneBRowCapDecideProbe
#print axioms N11Formalization.LaneBRowCapDecideProbe.row_4_5
