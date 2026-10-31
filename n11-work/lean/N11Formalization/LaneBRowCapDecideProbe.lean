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
    (∑ q : Fin 9, y_1409 q * rowA 0 1 q) ≤ db 0 1 := by
  norm_num [y_1409, rowA, db, dbmVal, Fin.sum_univ_succ]

theorem row_4_5 :
    (∑ q : Fin 9, y_1409 q * rowA 4 5 q) ≤ db 4 5 := by
  norm_num [y_1409, rowA, db, dbmVal, Fin.sum_univ_succ]

theorem row_9_9 :
    (∑ q : Fin 9, y_1409 q * rowA 9 9 q) ≤ db 9 9 := by
  norm_num [y_1409, rowA, db, dbmVal, Fin.sum_univ_succ]

end
end N11Formalization.LaneBRowCapDecideProbe
#print axioms N11Formalization.LaneBRowCapDecideProbe.row_4_5
