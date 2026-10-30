import N11Formalization.FrozenCapWideFieldWitnesses
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact 100-pair row caps for the seven wide-support witnesses. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapWideFieldRowCaps
open Finset
open N11Formalization.FrozenCapWideFieldWitnesses
noncomputable section

def rowA (i j : Fin 10) (q : Fin 9) : ℚ :=
  (if q.val < j.val then 1 else 0) - (if q.val < i.val then 1 else 0)

def dbmVal_1409 : Fin 10 → Fin 10 → ℤ
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

def db_1409 (i j : Fin 10) : ℚ := (dbmVal_1409 i j : ℚ) / 4096

theorem row_cap_1409_0_0 :
    yW_1409 0 * rowA 0 0 0 + yW_1409 1 * rowA 0 0 1 + yW_1409 2 * rowA 0 0 2 + yW_1409 3 * rowA 0 0 3 + yW_1409 4 * rowA 0 0 4 + yW_1409 5 * rowA 0 0 5 + yW_1409 6 * rowA 0 0 6 + yW_1409 7 * rowA 0 0 7 + yW_1409 8 * rowA 0 0 8 ≤ db_1409 0 0 := by
  have hleft : yW_1409 0 * rowA 0 0 0 + yW_1409 1 * rowA 0 0 1 + yW_1409 2 * rowA 0 0 2 + yW_1409 3 * rowA 0 0 3 + yW_1409 4 * rowA 0 0 4 + yW_1409 5 * rowA 0 0 5 + yW_1409 6 * rowA 0 0 6 + yW_1409 7 * rowA 0 0 7 + yW_1409 8 * rowA 0 0 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 0 0 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_0_1 :
    yW_1409 0 * rowA 0 1 0 + yW_1409 1 * rowA 0 1 1 + yW_1409 2 * rowA 0 1 2 + yW_1409 3 * rowA 0 1 3 + yW_1409 4 * rowA 0 1 4 + yW_1409 5 * rowA 0 1 5 + yW_1409 6 * rowA 0 1 6 + yW_1409 7 * rowA 0 1 7 + yW_1409 8 * rowA 0 1 8 ≤ db_1409 0 1 := by
  have hleft : yW_1409 0 * rowA 0 1 0 + yW_1409 1 * rowA 0 1 1 + yW_1409 2 * rowA 0 1 2 + yW_1409 3 * rowA 0 1 3 + yW_1409 4 * rowA 0 1 4 + yW_1409 5 * rowA 0 1 5 + yW_1409 6 * rowA 0 1 6 + yW_1409 7 * rowA 0 1 7 + yW_1409 8 * rowA 0 1 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 0 1 = (1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_0_2 :
    yW_1409 0 * rowA 0 2 0 + yW_1409 1 * rowA 0 2 1 + yW_1409 2 * rowA 0 2 2 + yW_1409 3 * rowA 0 2 3 + yW_1409 4 * rowA 0 2 4 + yW_1409 5 * rowA 0 2 5 + yW_1409 6 * rowA 0 2 6 + yW_1409 7 * rowA 0 2 7 + yW_1409 8 * rowA 0 2 8 ≤ db_1409 0 2 := by
  have hleft : yW_1409 0 * rowA 0 2 0 + yW_1409 1 * rowA 0 2 1 + yW_1409 2 * rowA 0 2 2 + yW_1409 3 * rowA 0 2 3 + yW_1409 4 * rowA 0 2 4 + yW_1409 5 * rowA 0 2 5 + yW_1409 6 * rowA 0 2 6 + yW_1409 7 * rowA 0 2 7 + yW_1409 8 * rowA 0 2 8 = (1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 0 2 = (1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_0_3 :
    yW_1409 0 * rowA 0 3 0 + yW_1409 1 * rowA 0 3 1 + yW_1409 2 * rowA 0 3 2 + yW_1409 3 * rowA 0 3 3 + yW_1409 4 * rowA 0 3 4 + yW_1409 5 * rowA 0 3 5 + yW_1409 6 * rowA 0 3 6 + yW_1409 7 * rowA 0 3 7 + yW_1409 8 * rowA 0 3 8 ≤ db_1409 0 3 := by
  have hleft : yW_1409 0 * rowA 0 3 0 + yW_1409 1 * rowA 0 3 1 + yW_1409 2 * rowA 0 3 2 + yW_1409 3 * rowA 0 3 3 + yW_1409 4 * rowA 0 3 4 + yW_1409 5 * rowA 0 3 5 + yW_1409 6 * rowA 0 3 6 + yW_1409 7 * rowA 0 3 7 + yW_1409 8 * rowA 0 3 8 = (1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 0 3 = (1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_0_4 :
    yW_1409 0 * rowA 0 4 0 + yW_1409 1 * rowA 0 4 1 + yW_1409 2 * rowA 0 4 2 + yW_1409 3 * rowA 0 4 3 + yW_1409 4 * rowA 0 4 4 + yW_1409 5 * rowA 0 4 5 + yW_1409 6 * rowA 0 4 6 + yW_1409 7 * rowA 0 4 7 + yW_1409 8 * rowA 0 4 8 ≤ db_1409 0 4 := by
  have hleft : yW_1409 0 * rowA 0 4 0 + yW_1409 1 * rowA 0 4 1 + yW_1409 2 * rowA 0 4 2 + yW_1409 3 * rowA 0 4 3 + yW_1409 4 * rowA 0 4 4 + yW_1409 5 * rowA 0 4 5 + yW_1409 6 * rowA 0 4 6 + yW_1409 7 * rowA 0 4 7 + yW_1409 8 * rowA 0 4 8 = (3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 0 4 = (1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_0_5 :
    yW_1409 0 * rowA 0 5 0 + yW_1409 1 * rowA 0 5 1 + yW_1409 2 * rowA 0 5 2 + yW_1409 3 * rowA 0 5 3 + yW_1409 4 * rowA 0 5 4 + yW_1409 5 * rowA 0 5 5 + yW_1409 6 * rowA 0 5 6 + yW_1409 7 * rowA 0 5 7 + yW_1409 8 * rowA 0 5 8 ≤ db_1409 0 5 := by
  have hleft : yW_1409 0 * rowA 0 5 0 + yW_1409 1 * rowA 0 5 1 + yW_1409 2 * rowA 0 5 2 + yW_1409 3 * rowA 0 5 3 + yW_1409 4 * rowA 0 5 4 + yW_1409 5 * rowA 0 5 5 + yW_1409 6 * rowA 0 5 6 + yW_1409 7 * rowA 0 5 7 + yW_1409 8 * rowA 0 5 8 = (5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 0 5 = (3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_0_6 :
    yW_1409 0 * rowA 0 6 0 + yW_1409 1 * rowA 0 6 1 + yW_1409 2 * rowA 0 6 2 + yW_1409 3 * rowA 0 6 3 + yW_1409 4 * rowA 0 6 4 + yW_1409 5 * rowA 0 6 5 + yW_1409 6 * rowA 0 6 6 + yW_1409 7 * rowA 0 6 7 + yW_1409 8 * rowA 0 6 8 ≤ db_1409 0 6 := by
  have hleft : yW_1409 0 * rowA 0 6 0 + yW_1409 1 * rowA 0 6 1 + yW_1409 2 * rowA 0 6 2 + yW_1409 3 * rowA 0 6 3 + yW_1409 4 * rowA 0 6 4 + yW_1409 5 * rowA 0 6 5 + yW_1409 6 * rowA 0 6 6 + yW_1409 7 * rowA 0 6 7 + yW_1409 8 * rowA 0 6 8 = (5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 0 6 = (3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_0_7 :
    yW_1409 0 * rowA 0 7 0 + yW_1409 1 * rowA 0 7 1 + yW_1409 2 * rowA 0 7 2 + yW_1409 3 * rowA 0 7 3 + yW_1409 4 * rowA 0 7 4 + yW_1409 5 * rowA 0 7 5 + yW_1409 6 * rowA 0 7 6 + yW_1409 7 * rowA 0 7 7 + yW_1409 8 * rowA 0 7 8 ≤ db_1409 0 7 := by
  have hleft : yW_1409 0 * rowA 0 7 0 + yW_1409 1 * rowA 0 7 1 + yW_1409 2 * rowA 0 7 2 + yW_1409 3 * rowA 0 7 3 + yW_1409 4 * rowA 0 7 4 + yW_1409 5 * rowA 0 7 5 + yW_1409 6 * rowA 0 7 6 + yW_1409 7 * rowA 0 7 7 + yW_1409 8 * rowA 0 7 8 = (5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 0 7 = (3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_0_8 :
    yW_1409 0 * rowA 0 8 0 + yW_1409 1 * rowA 0 8 1 + yW_1409 2 * rowA 0 8 2 + yW_1409 3 * rowA 0 8 3 + yW_1409 4 * rowA 0 8 4 + yW_1409 5 * rowA 0 8 5 + yW_1409 6 * rowA 0 8 6 + yW_1409 7 * rowA 0 8 7 + yW_1409 8 * rowA 0 8 8 ≤ db_1409 0 8 := by
  have hleft : yW_1409 0 * rowA 0 8 0 + yW_1409 1 * rowA 0 8 1 + yW_1409 2 * rowA 0 8 2 + yW_1409 3 * rowA 0 8 3 + yW_1409 4 * rowA 0 8 4 + yW_1409 5 * rowA 0 8 5 + yW_1409 6 * rowA 0 8 6 + yW_1409 7 * rowA 0 8 7 + yW_1409 8 * rowA 0 8 8 = (3 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 0 8 = (7 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_0_9 :
    yW_1409 0 * rowA 0 9 0 + yW_1409 1 * rowA 0 9 1 + yW_1409 2 * rowA 0 9 2 + yW_1409 3 * rowA 0 9 3 + yW_1409 4 * rowA 0 9 4 + yW_1409 5 * rowA 0 9 5 + yW_1409 6 * rowA 0 9 6 + yW_1409 7 * rowA 0 9 7 + yW_1409 8 * rowA 0 9 8 ≤ db_1409 0 9 := by
  have hleft : yW_1409 0 * rowA 0 9 0 + yW_1409 1 * rowA 0 9 1 + yW_1409 2 * rowA 0 9 2 + yW_1409 3 * rowA 0 9 3 + yW_1409 4 * rowA 0 9 4 + yW_1409 5 * rowA 0 9 5 + yW_1409 6 * rowA 0 9 6 + yW_1409 7 * rowA 0 9 7 + yW_1409 8 * rowA 0 9 8 = (1 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 0 9 = (1 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_1_0 :
    yW_1409 0 * rowA 1 0 0 + yW_1409 1 * rowA 1 0 1 + yW_1409 2 * rowA 1 0 2 + yW_1409 3 * rowA 1 0 3 + yW_1409 4 * rowA 1 0 4 + yW_1409 5 * rowA 1 0 5 + yW_1409 6 * rowA 1 0 6 + yW_1409 7 * rowA 1 0 7 + yW_1409 8 * rowA 1 0 8 ≤ db_1409 1 0 := by
  have hleft : yW_1409 0 * rowA 1 0 0 + yW_1409 1 * rowA 1 0 1 + yW_1409 2 * rowA 1 0 2 + yW_1409 3 * rowA 1 0 3 + yW_1409 4 * rowA 1 0 4 + yW_1409 5 * rowA 1 0 5 + yW_1409 6 * rowA 1 0 6 + yW_1409 7 * rowA 1 0 7 + yW_1409 8 * rowA 1 0 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 1 0 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_1_1 :
    yW_1409 0 * rowA 1 1 0 + yW_1409 1 * rowA 1 1 1 + yW_1409 2 * rowA 1 1 2 + yW_1409 3 * rowA 1 1 3 + yW_1409 4 * rowA 1 1 4 + yW_1409 5 * rowA 1 1 5 + yW_1409 6 * rowA 1 1 6 + yW_1409 7 * rowA 1 1 7 + yW_1409 8 * rowA 1 1 8 ≤ db_1409 1 1 := by
  have hleft : yW_1409 0 * rowA 1 1 0 + yW_1409 1 * rowA 1 1 1 + yW_1409 2 * rowA 1 1 2 + yW_1409 3 * rowA 1 1 3 + yW_1409 4 * rowA 1 1 4 + yW_1409 5 * rowA 1 1 5 + yW_1409 6 * rowA 1 1 6 + yW_1409 7 * rowA 1 1 7 + yW_1409 8 * rowA 1 1 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 1 1 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_1_2 :
    yW_1409 0 * rowA 1 2 0 + yW_1409 1 * rowA 1 2 1 + yW_1409 2 * rowA 1 2 2 + yW_1409 3 * rowA 1 2 3 + yW_1409 4 * rowA 1 2 4 + yW_1409 5 * rowA 1 2 5 + yW_1409 6 * rowA 1 2 6 + yW_1409 7 * rowA 1 2 7 + yW_1409 8 * rowA 1 2 8 ≤ db_1409 1 2 := by
  have hleft : yW_1409 0 * rowA 1 2 0 + yW_1409 1 * rowA 1 2 1 + yW_1409 2 * rowA 1 2 2 + yW_1409 3 * rowA 1 2 3 + yW_1409 4 * rowA 1 2 4 + yW_1409 5 * rowA 1 2 5 + yW_1409 6 * rowA 1 2 6 + yW_1409 7 * rowA 1 2 7 + yW_1409 8 * rowA 1 2 8 = (1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 1 2 = (1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_1_3 :
    yW_1409 0 * rowA 1 3 0 + yW_1409 1 * rowA 1 3 1 + yW_1409 2 * rowA 1 3 2 + yW_1409 3 * rowA 1 3 3 + yW_1409 4 * rowA 1 3 4 + yW_1409 5 * rowA 1 3 5 + yW_1409 6 * rowA 1 3 6 + yW_1409 7 * rowA 1 3 7 + yW_1409 8 * rowA 1 3 8 ≤ db_1409 1 3 := by
  have hleft : yW_1409 0 * rowA 1 3 0 + yW_1409 1 * rowA 1 3 1 + yW_1409 2 * rowA 1 3 2 + yW_1409 3 * rowA 1 3 3 + yW_1409 4 * rowA 1 3 4 + yW_1409 5 * rowA 1 3 5 + yW_1409 6 * rowA 1 3 6 + yW_1409 7 * rowA 1 3 7 + yW_1409 8 * rowA 1 3 8 = (1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 1 3 = (1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_1_4 :
    yW_1409 0 * rowA 1 4 0 + yW_1409 1 * rowA 1 4 1 + yW_1409 2 * rowA 1 4 2 + yW_1409 3 * rowA 1 4 3 + yW_1409 4 * rowA 1 4 4 + yW_1409 5 * rowA 1 4 5 + yW_1409 6 * rowA 1 4 6 + yW_1409 7 * rowA 1 4 7 + yW_1409 8 * rowA 1 4 8 ≤ db_1409 1 4 := by
  have hleft : yW_1409 0 * rowA 1 4 0 + yW_1409 1 * rowA 1 4 1 + yW_1409 2 * rowA 1 4 2 + yW_1409 3 * rowA 1 4 3 + yW_1409 4 * rowA 1 4 4 + yW_1409 5 * rowA 1 4 5 + yW_1409 6 * rowA 1 4 6 + yW_1409 7 * rowA 1 4 7 + yW_1409 8 * rowA 1 4 8 = (3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 1 4 = (1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_1_5 :
    yW_1409 0 * rowA 1 5 0 + yW_1409 1 * rowA 1 5 1 + yW_1409 2 * rowA 1 5 2 + yW_1409 3 * rowA 1 5 3 + yW_1409 4 * rowA 1 5 4 + yW_1409 5 * rowA 1 5 5 + yW_1409 6 * rowA 1 5 6 + yW_1409 7 * rowA 1 5 7 + yW_1409 8 * rowA 1 5 8 ≤ db_1409 1 5 := by
  have hleft : yW_1409 0 * rowA 1 5 0 + yW_1409 1 * rowA 1 5 1 + yW_1409 2 * rowA 1 5 2 + yW_1409 3 * rowA 1 5 3 + yW_1409 4 * rowA 1 5 4 + yW_1409 5 * rowA 1 5 5 + yW_1409 6 * rowA 1 5 6 + yW_1409 7 * rowA 1 5 7 + yW_1409 8 * rowA 1 5 8 = (5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 1 5 = (3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_1_6 :
    yW_1409 0 * rowA 1 6 0 + yW_1409 1 * rowA 1 6 1 + yW_1409 2 * rowA 1 6 2 + yW_1409 3 * rowA 1 6 3 + yW_1409 4 * rowA 1 6 4 + yW_1409 5 * rowA 1 6 5 + yW_1409 6 * rowA 1 6 6 + yW_1409 7 * rowA 1 6 7 + yW_1409 8 * rowA 1 6 8 ≤ db_1409 1 6 := by
  have hleft : yW_1409 0 * rowA 1 6 0 + yW_1409 1 * rowA 1 6 1 + yW_1409 2 * rowA 1 6 2 + yW_1409 3 * rowA 1 6 3 + yW_1409 4 * rowA 1 6 4 + yW_1409 5 * rowA 1 6 5 + yW_1409 6 * rowA 1 6 6 + yW_1409 7 * rowA 1 6 7 + yW_1409 8 * rowA 1 6 8 = (5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 1 6 = (3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_1_7 :
    yW_1409 0 * rowA 1 7 0 + yW_1409 1 * rowA 1 7 1 + yW_1409 2 * rowA 1 7 2 + yW_1409 3 * rowA 1 7 3 + yW_1409 4 * rowA 1 7 4 + yW_1409 5 * rowA 1 7 5 + yW_1409 6 * rowA 1 7 6 + yW_1409 7 * rowA 1 7 7 + yW_1409 8 * rowA 1 7 8 ≤ db_1409 1 7 := by
  have hleft : yW_1409 0 * rowA 1 7 0 + yW_1409 1 * rowA 1 7 1 + yW_1409 2 * rowA 1 7 2 + yW_1409 3 * rowA 1 7 3 + yW_1409 4 * rowA 1 7 4 + yW_1409 5 * rowA 1 7 5 + yW_1409 6 * rowA 1 7 6 + yW_1409 7 * rowA 1 7 7 + yW_1409 8 * rowA 1 7 8 = (5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 1 7 = (3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_1_8 :
    yW_1409 0 * rowA 1 8 0 + yW_1409 1 * rowA 1 8 1 + yW_1409 2 * rowA 1 8 2 + yW_1409 3 * rowA 1 8 3 + yW_1409 4 * rowA 1 8 4 + yW_1409 5 * rowA 1 8 5 + yW_1409 6 * rowA 1 8 6 + yW_1409 7 * rowA 1 8 7 + yW_1409 8 * rowA 1 8 8 ≤ db_1409 1 8 := by
  have hleft : yW_1409 0 * rowA 1 8 0 + yW_1409 1 * rowA 1 8 1 + yW_1409 2 * rowA 1 8 2 + yW_1409 3 * rowA 1 8 3 + yW_1409 4 * rowA 1 8 4 + yW_1409 5 * rowA 1 8 5 + yW_1409 6 * rowA 1 8 6 + yW_1409 7 * rowA 1 8 7 + yW_1409 8 * rowA 1 8 8 = (3 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 1 8 = (7 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_1_9 :
    yW_1409 0 * rowA 1 9 0 + yW_1409 1 * rowA 1 9 1 + yW_1409 2 * rowA 1 9 2 + yW_1409 3 * rowA 1 9 3 + yW_1409 4 * rowA 1 9 4 + yW_1409 5 * rowA 1 9 5 + yW_1409 6 * rowA 1 9 6 + yW_1409 7 * rowA 1 9 7 + yW_1409 8 * rowA 1 9 8 ≤ db_1409 1 9 := by
  have hleft : yW_1409 0 * rowA 1 9 0 + yW_1409 1 * rowA 1 9 1 + yW_1409 2 * rowA 1 9 2 + yW_1409 3 * rowA 1 9 3 + yW_1409 4 * rowA 1 9 4 + yW_1409 5 * rowA 1 9 5 + yW_1409 6 * rowA 1 9 6 + yW_1409 7 * rowA 1 9 7 + yW_1409 8 * rowA 1 9 8 = (1 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 1 9 = (1 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_2_0 :
    yW_1409 0 * rowA 2 0 0 + yW_1409 1 * rowA 2 0 1 + yW_1409 2 * rowA 2 0 2 + yW_1409 3 * rowA 2 0 3 + yW_1409 4 * rowA 2 0 4 + yW_1409 5 * rowA 2 0 5 + yW_1409 6 * rowA 2 0 6 + yW_1409 7 * rowA 2 0 7 + yW_1409 8 * rowA 2 0 8 ≤ db_1409 2 0 := by
  have hleft : yW_1409 0 * rowA 2 0 0 + yW_1409 1 * rowA 2 0 1 + yW_1409 2 * rowA 2 0 2 + yW_1409 3 * rowA 2 0 3 + yW_1409 4 * rowA 2 0 4 + yW_1409 5 * rowA 2 0 5 + yW_1409 6 * rowA 2 0 6 + yW_1409 7 * rowA 2 0 7 + yW_1409 8 * rowA 2 0 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 2 0 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_2_1 :
    yW_1409 0 * rowA 2 1 0 + yW_1409 1 * rowA 2 1 1 + yW_1409 2 * rowA 2 1 2 + yW_1409 3 * rowA 2 1 3 + yW_1409 4 * rowA 2 1 4 + yW_1409 5 * rowA 2 1 5 + yW_1409 6 * rowA 2 1 6 + yW_1409 7 * rowA 2 1 7 + yW_1409 8 * rowA 2 1 8 ≤ db_1409 2 1 := by
  have hleft : yW_1409 0 * rowA 2 1 0 + yW_1409 1 * rowA 2 1 1 + yW_1409 2 * rowA 2 1 2 + yW_1409 3 * rowA 2 1 3 + yW_1409 4 * rowA 2 1 4 + yW_1409 5 * rowA 2 1 5 + yW_1409 6 * rowA 2 1 6 + yW_1409 7 * rowA 2 1 7 + yW_1409 8 * rowA 2 1 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 2 1 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_2_2 :
    yW_1409 0 * rowA 2 2 0 + yW_1409 1 * rowA 2 2 1 + yW_1409 2 * rowA 2 2 2 + yW_1409 3 * rowA 2 2 3 + yW_1409 4 * rowA 2 2 4 + yW_1409 5 * rowA 2 2 5 + yW_1409 6 * rowA 2 2 6 + yW_1409 7 * rowA 2 2 7 + yW_1409 8 * rowA 2 2 8 ≤ db_1409 2 2 := by
  have hleft : yW_1409 0 * rowA 2 2 0 + yW_1409 1 * rowA 2 2 1 + yW_1409 2 * rowA 2 2 2 + yW_1409 3 * rowA 2 2 3 + yW_1409 4 * rowA 2 2 4 + yW_1409 5 * rowA 2 2 5 + yW_1409 6 * rowA 2 2 6 + yW_1409 7 * rowA 2 2 7 + yW_1409 8 * rowA 2 2 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 2 2 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_2_3 :
    yW_1409 0 * rowA 2 3 0 + yW_1409 1 * rowA 2 3 1 + yW_1409 2 * rowA 2 3 2 + yW_1409 3 * rowA 2 3 3 + yW_1409 4 * rowA 2 3 4 + yW_1409 5 * rowA 2 3 5 + yW_1409 6 * rowA 2 3 6 + yW_1409 7 * rowA 2 3 7 + yW_1409 8 * rowA 2 3 8 ≤ db_1409 2 3 := by
  have hleft : yW_1409 0 * rowA 2 3 0 + yW_1409 1 * rowA 2 3 1 + yW_1409 2 * rowA 2 3 2 + yW_1409 3 * rowA 2 3 3 + yW_1409 4 * rowA 2 3 4 + yW_1409 5 * rowA 2 3 5 + yW_1409 6 * rowA 2 3 6 + yW_1409 7 * rowA 2 3 7 + yW_1409 8 * rowA 2 3 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 2 3 = (1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_2_4 :
    yW_1409 0 * rowA 2 4 0 + yW_1409 1 * rowA 2 4 1 + yW_1409 2 * rowA 2 4 2 + yW_1409 3 * rowA 2 4 3 + yW_1409 4 * rowA 2 4 4 + yW_1409 5 * rowA 2 4 5 + yW_1409 6 * rowA 2 4 6 + yW_1409 7 * rowA 2 4 7 + yW_1409 8 * rowA 2 4 8 ≤ db_1409 2 4 := by
  have hleft : yW_1409 0 * rowA 2 4 0 + yW_1409 1 * rowA 2 4 1 + yW_1409 2 * rowA 2 4 2 + yW_1409 3 * rowA 2 4 3 + yW_1409 4 * rowA 2 4 4 + yW_1409 5 * rowA 2 4 5 + yW_1409 6 * rowA 2 4 6 + yW_1409 7 * rowA 2 4 7 + yW_1409 8 * rowA 2 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 2 4 = (1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_2_5 :
    yW_1409 0 * rowA 2 5 0 + yW_1409 1 * rowA 2 5 1 + yW_1409 2 * rowA 2 5 2 + yW_1409 3 * rowA 2 5 3 + yW_1409 4 * rowA 2 5 4 + yW_1409 5 * rowA 2 5 5 + yW_1409 6 * rowA 2 5 6 + yW_1409 7 * rowA 2 5 7 + yW_1409 8 * rowA 2 5 8 ≤ db_1409 2 5 := by
  have hleft : yW_1409 0 * rowA 2 5 0 + yW_1409 1 * rowA 2 5 1 + yW_1409 2 * rowA 2 5 2 + yW_1409 3 * rowA 2 5 3 + yW_1409 4 * rowA 2 5 4 + yW_1409 5 * rowA 2 5 5 + yW_1409 6 * rowA 2 5 6 + yW_1409 7 * rowA 2 5 7 + yW_1409 8 * rowA 2 5 8 = (1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 2 5 = (3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_2_6 :
    yW_1409 0 * rowA 2 6 0 + yW_1409 1 * rowA 2 6 1 + yW_1409 2 * rowA 2 6 2 + yW_1409 3 * rowA 2 6 3 + yW_1409 4 * rowA 2 6 4 + yW_1409 5 * rowA 2 6 5 + yW_1409 6 * rowA 2 6 6 + yW_1409 7 * rowA 2 6 7 + yW_1409 8 * rowA 2 6 8 ≤ db_1409 2 6 := by
  have hleft : yW_1409 0 * rowA 2 6 0 + yW_1409 1 * rowA 2 6 1 + yW_1409 2 * rowA 2 6 2 + yW_1409 3 * rowA 2 6 3 + yW_1409 4 * rowA 2 6 4 + yW_1409 5 * rowA 2 6 5 + yW_1409 6 * rowA 2 6 6 + yW_1409 7 * rowA 2 6 7 + yW_1409 8 * rowA 2 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 2 6 = (3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_2_7 :
    yW_1409 0 * rowA 2 7 0 + yW_1409 1 * rowA 2 7 1 + yW_1409 2 * rowA 2 7 2 + yW_1409 3 * rowA 2 7 3 + yW_1409 4 * rowA 2 7 4 + yW_1409 5 * rowA 2 7 5 + yW_1409 6 * rowA 2 7 6 + yW_1409 7 * rowA 2 7 7 + yW_1409 8 * rowA 2 7 8 ≤ db_1409 2 7 := by
  have hleft : yW_1409 0 * rowA 2 7 0 + yW_1409 1 * rowA 2 7 1 + yW_1409 2 * rowA 2 7 2 + yW_1409 3 * rowA 2 7 3 + yW_1409 4 * rowA 2 7 4 + yW_1409 5 * rowA 2 7 5 + yW_1409 6 * rowA 2 7 6 + yW_1409 7 * rowA 2 7 7 + yW_1409 8 * rowA 2 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 2 7 = (3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_2_8 :
    yW_1409 0 * rowA 2 8 0 + yW_1409 1 * rowA 2 8 1 + yW_1409 2 * rowA 2 8 2 + yW_1409 3 * rowA 2 8 3 + yW_1409 4 * rowA 2 8 4 + yW_1409 5 * rowA 2 8 5 + yW_1409 6 * rowA 2 8 6 + yW_1409 7 * rowA 2 8 7 + yW_1409 8 * rowA 2 8 8 ≤ db_1409 2 8 := by
  have hleft : yW_1409 0 * rowA 2 8 0 + yW_1409 1 * rowA 2 8 1 + yW_1409 2 * rowA 2 8 2 + yW_1409 3 * rowA 2 8 3 + yW_1409 4 * rowA 2 8 4 + yW_1409 5 * rowA 2 8 5 + yW_1409 6 * rowA 2 8 6 + yW_1409 7 * rowA 2 8 7 + yW_1409 8 * rowA 2 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 2 8 = (7 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_2_9 :
    yW_1409 0 * rowA 2 9 0 + yW_1409 1 * rowA 2 9 1 + yW_1409 2 * rowA 2 9 2 + yW_1409 3 * rowA 2 9 3 + yW_1409 4 * rowA 2 9 4 + yW_1409 5 * rowA 2 9 5 + yW_1409 6 * rowA 2 9 6 + yW_1409 7 * rowA 2 9 7 + yW_1409 8 * rowA 2 9 8 ≤ db_1409 2 9 := by
  have hleft : yW_1409 0 * rowA 2 9 0 + yW_1409 1 * rowA 2 9 1 + yW_1409 2 * rowA 2 9 2 + yW_1409 3 * rowA 2 9 3 + yW_1409 4 * rowA 2 9 4 + yW_1409 5 * rowA 2 9 5 + yW_1409 6 * rowA 2 9 6 + yW_1409 7 * rowA 2 9 7 + yW_1409 8 * rowA 2 9 8 = (7 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 2 9 = (1 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_3_0 :
    yW_1409 0 * rowA 3 0 0 + yW_1409 1 * rowA 3 0 1 + yW_1409 2 * rowA 3 0 2 + yW_1409 3 * rowA 3 0 3 + yW_1409 4 * rowA 3 0 4 + yW_1409 5 * rowA 3 0 5 + yW_1409 6 * rowA 3 0 6 + yW_1409 7 * rowA 3 0 7 + yW_1409 8 * rowA 3 0 8 ≤ db_1409 3 0 := by
  have hleft : yW_1409 0 * rowA 3 0 0 + yW_1409 1 * rowA 3 0 1 + yW_1409 2 * rowA 3 0 2 + yW_1409 3 * rowA 3 0 3 + yW_1409 4 * rowA 3 0 4 + yW_1409 5 * rowA 3 0 5 + yW_1409 6 * rowA 3 0 6 + yW_1409 7 * rowA 3 0 7 + yW_1409 8 * rowA 3 0 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 3 0 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_3_1 :
    yW_1409 0 * rowA 3 1 0 + yW_1409 1 * rowA 3 1 1 + yW_1409 2 * rowA 3 1 2 + yW_1409 3 * rowA 3 1 3 + yW_1409 4 * rowA 3 1 4 + yW_1409 5 * rowA 3 1 5 + yW_1409 6 * rowA 3 1 6 + yW_1409 7 * rowA 3 1 7 + yW_1409 8 * rowA 3 1 8 ≤ db_1409 3 1 := by
  have hleft : yW_1409 0 * rowA 3 1 0 + yW_1409 1 * rowA 3 1 1 + yW_1409 2 * rowA 3 1 2 + yW_1409 3 * rowA 3 1 3 + yW_1409 4 * rowA 3 1 4 + yW_1409 5 * rowA 3 1 5 + yW_1409 6 * rowA 3 1 6 + yW_1409 7 * rowA 3 1 7 + yW_1409 8 * rowA 3 1 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 3 1 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_3_2 :
    yW_1409 0 * rowA 3 2 0 + yW_1409 1 * rowA 3 2 1 + yW_1409 2 * rowA 3 2 2 + yW_1409 3 * rowA 3 2 3 + yW_1409 4 * rowA 3 2 4 + yW_1409 5 * rowA 3 2 5 + yW_1409 6 * rowA 3 2 6 + yW_1409 7 * rowA 3 2 7 + yW_1409 8 * rowA 3 2 8 ≤ db_1409 3 2 := by
  have hleft : yW_1409 0 * rowA 3 2 0 + yW_1409 1 * rowA 3 2 1 + yW_1409 2 * rowA 3 2 2 + yW_1409 3 * rowA 3 2 3 + yW_1409 4 * rowA 3 2 4 + yW_1409 5 * rowA 3 2 5 + yW_1409 6 * rowA 3 2 6 + yW_1409 7 * rowA 3 2 7 + yW_1409 8 * rowA 3 2 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 3 2 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_3_3 :
    yW_1409 0 * rowA 3 3 0 + yW_1409 1 * rowA 3 3 1 + yW_1409 2 * rowA 3 3 2 + yW_1409 3 * rowA 3 3 3 + yW_1409 4 * rowA 3 3 4 + yW_1409 5 * rowA 3 3 5 + yW_1409 6 * rowA 3 3 6 + yW_1409 7 * rowA 3 3 7 + yW_1409 8 * rowA 3 3 8 ≤ db_1409 3 3 := by
  have hleft : yW_1409 0 * rowA 3 3 0 + yW_1409 1 * rowA 3 3 1 + yW_1409 2 * rowA 3 3 2 + yW_1409 3 * rowA 3 3 3 + yW_1409 4 * rowA 3 3 4 + yW_1409 5 * rowA 3 3 5 + yW_1409 6 * rowA 3 3 6 + yW_1409 7 * rowA 3 3 7 + yW_1409 8 * rowA 3 3 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 3 3 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_3_4 :
    yW_1409 0 * rowA 3 4 0 + yW_1409 1 * rowA 3 4 1 + yW_1409 2 * rowA 3 4 2 + yW_1409 3 * rowA 3 4 3 + yW_1409 4 * rowA 3 4 4 + yW_1409 5 * rowA 3 4 5 + yW_1409 6 * rowA 3 4 6 + yW_1409 7 * rowA 3 4 7 + yW_1409 8 * rowA 3 4 8 ≤ db_1409 3 4 := by
  have hleft : yW_1409 0 * rowA 3 4 0 + yW_1409 1 * rowA 3 4 1 + yW_1409 2 * rowA 3 4 2 + yW_1409 3 * rowA 3 4 3 + yW_1409 4 * rowA 3 4 4 + yW_1409 5 * rowA 3 4 5 + yW_1409 6 * rowA 3 4 6 + yW_1409 7 * rowA 3 4 7 + yW_1409 8 * rowA 3 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 3 4 = (3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_3_5 :
    yW_1409 0 * rowA 3 5 0 + yW_1409 1 * rowA 3 5 1 + yW_1409 2 * rowA 3 5 2 + yW_1409 3 * rowA 3 5 3 + yW_1409 4 * rowA 3 5 4 + yW_1409 5 * rowA 3 5 5 + yW_1409 6 * rowA 3 5 6 + yW_1409 7 * rowA 3 5 7 + yW_1409 8 * rowA 3 5 8 ≤ db_1409 3 5 := by
  have hleft : yW_1409 0 * rowA 3 5 0 + yW_1409 1 * rowA 3 5 1 + yW_1409 2 * rowA 3 5 2 + yW_1409 3 * rowA 3 5 3 + yW_1409 4 * rowA 3 5 4 + yW_1409 5 * rowA 3 5 5 + yW_1409 6 * rowA 3 5 6 + yW_1409 7 * rowA 3 5 7 + yW_1409 8 * rowA 3 5 8 = (1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 3 5 = (1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_3_6 :
    yW_1409 0 * rowA 3 6 0 + yW_1409 1 * rowA 3 6 1 + yW_1409 2 * rowA 3 6 2 + yW_1409 3 * rowA 3 6 3 + yW_1409 4 * rowA 3 6 4 + yW_1409 5 * rowA 3 6 5 + yW_1409 6 * rowA 3 6 6 + yW_1409 7 * rowA 3 6 7 + yW_1409 8 * rowA 3 6 8 ≤ db_1409 3 6 := by
  have hleft : yW_1409 0 * rowA 3 6 0 + yW_1409 1 * rowA 3 6 1 + yW_1409 2 * rowA 3 6 2 + yW_1409 3 * rowA 3 6 3 + yW_1409 4 * rowA 3 6 4 + yW_1409 5 * rowA 3 6 5 + yW_1409 6 * rowA 3 6 6 + yW_1409 7 * rowA 3 6 7 + yW_1409 8 * rowA 3 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 3 6 = (1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_3_7 :
    yW_1409 0 * rowA 3 7 0 + yW_1409 1 * rowA 3 7 1 + yW_1409 2 * rowA 3 7 2 + yW_1409 3 * rowA 3 7 3 + yW_1409 4 * rowA 3 7 4 + yW_1409 5 * rowA 3 7 5 + yW_1409 6 * rowA 3 7 6 + yW_1409 7 * rowA 3 7 7 + yW_1409 8 * rowA 3 7 8 ≤ db_1409 3 7 := by
  have hleft : yW_1409 0 * rowA 3 7 0 + yW_1409 1 * rowA 3 7 1 + yW_1409 2 * rowA 3 7 2 + yW_1409 3 * rowA 3 7 3 + yW_1409 4 * rowA 3 7 4 + yW_1409 5 * rowA 3 7 5 + yW_1409 6 * rowA 3 7 6 + yW_1409 7 * rowA 3 7 7 + yW_1409 8 * rowA 3 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 3 7 = (1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_3_8 :
    yW_1409 0 * rowA 3 8 0 + yW_1409 1 * rowA 3 8 1 + yW_1409 2 * rowA 3 8 2 + yW_1409 3 * rowA 3 8 3 + yW_1409 4 * rowA 3 8 4 + yW_1409 5 * rowA 3 8 5 + yW_1409 6 * rowA 3 8 6 + yW_1409 7 * rowA 3 8 7 + yW_1409 8 * rowA 3 8 8 ≤ db_1409 3 8 := by
  have hleft : yW_1409 0 * rowA 3 8 0 + yW_1409 1 * rowA 3 8 1 + yW_1409 2 * rowA 3 8 2 + yW_1409 3 * rowA 3 8 3 + yW_1409 4 * rowA 3 8 4 + yW_1409 5 * rowA 3 8 5 + yW_1409 6 * rowA 3 8 6 + yW_1409 7 * rowA 3 8 7 + yW_1409 8 * rowA 3 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 3 8 = (5 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_3_9 :
    yW_1409 0 * rowA 3 9 0 + yW_1409 1 * rowA 3 9 1 + yW_1409 2 * rowA 3 9 2 + yW_1409 3 * rowA 3 9 3 + yW_1409 4 * rowA 3 9 4 + yW_1409 5 * rowA 3 9 5 + yW_1409 6 * rowA 3 9 6 + yW_1409 7 * rowA 3 9 7 + yW_1409 8 * rowA 3 9 8 ≤ db_1409 3 9 := by
  have hleft : yW_1409 0 * rowA 3 9 0 + yW_1409 1 * rowA 3 9 1 + yW_1409 2 * rowA 3 9 2 + yW_1409 3 * rowA 3 9 3 + yW_1409 4 * rowA 3 9 4 + yW_1409 5 * rowA 3 9 5 + yW_1409 6 * rowA 3 9 6 + yW_1409 7 * rowA 3 9 7 + yW_1409 8 * rowA 3 9 8 = (7 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 3 9 = (1 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_4_0 :
    yW_1409 0 * rowA 4 0 0 + yW_1409 1 * rowA 4 0 1 + yW_1409 2 * rowA 4 0 2 + yW_1409 3 * rowA 4 0 3 + yW_1409 4 * rowA 4 0 4 + yW_1409 5 * rowA 4 0 5 + yW_1409 6 * rowA 4 0 6 + yW_1409 7 * rowA 4 0 7 + yW_1409 8 * rowA 4 0 8 ≤ db_1409 4 0 := by
  have hleft : yW_1409 0 * rowA 4 0 0 + yW_1409 1 * rowA 4 0 1 + yW_1409 2 * rowA 4 0 2 + yW_1409 3 * rowA 4 0 3 + yW_1409 4 * rowA 4 0 4 + yW_1409 5 * rowA 4 0 5 + yW_1409 6 * rowA 4 0 6 + yW_1409 7 * rowA 4 0 7 + yW_1409 8 * rowA 4 0 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 4 0 = (-3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_4_1 :
    yW_1409 0 * rowA 4 1 0 + yW_1409 1 * rowA 4 1 1 + yW_1409 2 * rowA 4 1 2 + yW_1409 3 * rowA 4 1 3 + yW_1409 4 * rowA 4 1 4 + yW_1409 5 * rowA 4 1 5 + yW_1409 6 * rowA 4 1 6 + yW_1409 7 * rowA 4 1 7 + yW_1409 8 * rowA 4 1 8 ≤ db_1409 4 1 := by
  have hleft : yW_1409 0 * rowA 4 1 0 + yW_1409 1 * rowA 4 1 1 + yW_1409 2 * rowA 4 1 2 + yW_1409 3 * rowA 4 1 3 + yW_1409 4 * rowA 4 1 4 + yW_1409 5 * rowA 4 1 5 + yW_1409 6 * rowA 4 1 6 + yW_1409 7 * rowA 4 1 7 + yW_1409 8 * rowA 4 1 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 4 1 = (-1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_4_2 :
    yW_1409 0 * rowA 4 2 0 + yW_1409 1 * rowA 4 2 1 + yW_1409 2 * rowA 4 2 2 + yW_1409 3 * rowA 4 2 3 + yW_1409 4 * rowA 4 2 4 + yW_1409 5 * rowA 4 2 5 + yW_1409 6 * rowA 4 2 6 + yW_1409 7 * rowA 4 2 7 + yW_1409 8 * rowA 4 2 8 ≤ db_1409 4 2 := by
  have hleft : yW_1409 0 * rowA 4 2 0 + yW_1409 1 * rowA 4 2 1 + yW_1409 2 * rowA 4 2 2 + yW_1409 3 * rowA 4 2 3 + yW_1409 4 * rowA 4 2 4 + yW_1409 5 * rowA 4 2 5 + yW_1409 6 * rowA 4 2 6 + yW_1409 7 * rowA 4 2 7 + yW_1409 8 * rowA 4 2 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 4 2 = (-1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_4_3 :
    yW_1409 0 * rowA 4 3 0 + yW_1409 1 * rowA 4 3 1 + yW_1409 2 * rowA 4 3 2 + yW_1409 3 * rowA 4 3 3 + yW_1409 4 * rowA 4 3 4 + yW_1409 5 * rowA 4 3 5 + yW_1409 6 * rowA 4 3 6 + yW_1409 7 * rowA 4 3 7 + yW_1409 8 * rowA 4 3 8 ≤ db_1409 4 3 := by
  have hleft : yW_1409 0 * rowA 4 3 0 + yW_1409 1 * rowA 4 3 1 + yW_1409 2 * rowA 4 3 2 + yW_1409 3 * rowA 4 3 3 + yW_1409 4 * rowA 4 3 4 + yW_1409 5 * rowA 4 3 5 + yW_1409 6 * rowA 4 3 6 + yW_1409 7 * rowA 4 3 7 + yW_1409 8 * rowA 4 3 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 4 3 = (-1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_4_4 :
    yW_1409 0 * rowA 4 4 0 + yW_1409 1 * rowA 4 4 1 + yW_1409 2 * rowA 4 4 2 + yW_1409 3 * rowA 4 4 3 + yW_1409 4 * rowA 4 4 4 + yW_1409 5 * rowA 4 4 5 + yW_1409 6 * rowA 4 4 6 + yW_1409 7 * rowA 4 4 7 + yW_1409 8 * rowA 4 4 8 ≤ db_1409 4 4 := by
  have hleft : yW_1409 0 * rowA 4 4 0 + yW_1409 1 * rowA 4 4 1 + yW_1409 2 * rowA 4 4 2 + yW_1409 3 * rowA 4 4 3 + yW_1409 4 * rowA 4 4 4 + yW_1409 5 * rowA 4 4 5 + yW_1409 6 * rowA 4 4 6 + yW_1409 7 * rowA 4 4 7 + yW_1409 8 * rowA 4 4 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 4 4 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_4_5 :
    yW_1409 0 * rowA 4 5 0 + yW_1409 1 * rowA 4 5 1 + yW_1409 2 * rowA 4 5 2 + yW_1409 3 * rowA 4 5 3 + yW_1409 4 * rowA 4 5 4 + yW_1409 5 * rowA 4 5 5 + yW_1409 6 * rowA 4 5 6 + yW_1409 7 * rowA 4 5 7 + yW_1409 8 * rowA 4 5 8 ≤ db_1409 4 5 := by
  have hleft : yW_1409 0 * rowA 4 5 0 + yW_1409 1 * rowA 4 5 1 + yW_1409 2 * rowA 4 5 2 + yW_1409 3 * rowA 4 5 3 + yW_1409 4 * rowA 4 5 4 + yW_1409 5 * rowA 4 5 5 + yW_1409 6 * rowA 4 5 6 + yW_1409 7 * rowA 4 5 7 + yW_1409 8 * rowA 4 5 8 = (1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 4 5 = (1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_4_6 :
    yW_1409 0 * rowA 4 6 0 + yW_1409 1 * rowA 4 6 1 + yW_1409 2 * rowA 4 6 2 + yW_1409 3 * rowA 4 6 3 + yW_1409 4 * rowA 4 6 4 + yW_1409 5 * rowA 4 6 5 + yW_1409 6 * rowA 4 6 6 + yW_1409 7 * rowA 4 6 7 + yW_1409 8 * rowA 4 6 8 ≤ db_1409 4 6 := by
  have hleft : yW_1409 0 * rowA 4 6 0 + yW_1409 1 * rowA 4 6 1 + yW_1409 2 * rowA 4 6 2 + yW_1409 3 * rowA 4 6 3 + yW_1409 4 * rowA 4 6 4 + yW_1409 5 * rowA 4 6 5 + yW_1409 6 * rowA 4 6 6 + yW_1409 7 * rowA 4 6 7 + yW_1409 8 * rowA 4 6 8 = (1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 4 6 = (1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_4_7 :
    yW_1409 0 * rowA 4 7 0 + yW_1409 1 * rowA 4 7 1 + yW_1409 2 * rowA 4 7 2 + yW_1409 3 * rowA 4 7 3 + yW_1409 4 * rowA 4 7 4 + yW_1409 5 * rowA 4 7 5 + yW_1409 6 * rowA 4 7 6 + yW_1409 7 * rowA 4 7 7 + yW_1409 8 * rowA 4 7 8 ≤ db_1409 4 7 := by
  have hleft : yW_1409 0 * rowA 4 7 0 + yW_1409 1 * rowA 4 7 1 + yW_1409 2 * rowA 4 7 2 + yW_1409 3 * rowA 4 7 3 + yW_1409 4 * rowA 4 7 4 + yW_1409 5 * rowA 4 7 5 + yW_1409 6 * rowA 4 7 6 + yW_1409 7 * rowA 4 7 7 + yW_1409 8 * rowA 4 7 8 = (1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 4 7 = (1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_4_8 :
    yW_1409 0 * rowA 4 8 0 + yW_1409 1 * rowA 4 8 1 + yW_1409 2 * rowA 4 8 2 + yW_1409 3 * rowA 4 8 3 + yW_1409 4 * rowA 4 8 4 + yW_1409 5 * rowA 4 8 5 + yW_1409 6 * rowA 4 8 6 + yW_1409 7 * rowA 4 8 7 + yW_1409 8 * rowA 4 8 8 ≤ db_1409 4 8 := by
  have hleft : yW_1409 0 * rowA 4 8 0 + yW_1409 1 * rowA 4 8 1 + yW_1409 2 * rowA 4 8 2 + yW_1409 3 * rowA 4 8 3 + yW_1409 4 * rowA 4 8 4 + yW_1409 5 * rowA 4 8 5 + yW_1409 6 * rowA 4 8 6 + yW_1409 7 * rowA 4 8 7 + yW_1409 8 * rowA 4 8 8 = (3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 4 8 = (3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_4_9 :
    yW_1409 0 * rowA 4 9 0 + yW_1409 1 * rowA 4 9 1 + yW_1409 2 * rowA 4 9 2 + yW_1409 3 * rowA 4 9 3 + yW_1409 4 * rowA 4 9 4 + yW_1409 5 * rowA 4 9 5 + yW_1409 6 * rowA 4 9 6 + yW_1409 7 * rowA 4 9 7 + yW_1409 8 * rowA 4 9 8 ≤ db_1409 4 9 := by
  have hleft : yW_1409 0 * rowA 4 9 0 + yW_1409 1 * rowA 4 9 1 + yW_1409 2 * rowA 4 9 2 + yW_1409 3 * rowA 4 9 3 + yW_1409 4 * rowA 4 9 4 + yW_1409 5 * rowA 4 9 5 + yW_1409 6 * rowA 4 9 6 + yW_1409 7 * rowA 4 9 7 + yW_1409 8 * rowA 4 9 8 = (5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 4 9 = (5 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_5_0 :
    yW_1409 0 * rowA 5 0 0 + yW_1409 1 * rowA 5 0 1 + yW_1409 2 * rowA 5 0 2 + yW_1409 3 * rowA 5 0 3 + yW_1409 4 * rowA 5 0 4 + yW_1409 5 * rowA 5 0 5 + yW_1409 6 * rowA 5 0 6 + yW_1409 7 * rowA 5 0 7 + yW_1409 8 * rowA 5 0 8 ≤ db_1409 5 0 := by
  have hleft : yW_1409 0 * rowA 5 0 0 + yW_1409 1 * rowA 5 0 1 + yW_1409 2 * rowA 5 0 2 + yW_1409 3 * rowA 5 0 3 + yW_1409 4 * rowA 5 0 4 + yW_1409 5 * rowA 5 0 5 + yW_1409 6 * rowA 5 0 6 + yW_1409 7 * rowA 5 0 7 + yW_1409 8 * rowA 5 0 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 5 0 = (-1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_5_1 :
    yW_1409 0 * rowA 5 1 0 + yW_1409 1 * rowA 5 1 1 + yW_1409 2 * rowA 5 1 2 + yW_1409 3 * rowA 5 1 3 + yW_1409 4 * rowA 5 1 4 + yW_1409 5 * rowA 5 1 5 + yW_1409 6 * rowA 5 1 6 + yW_1409 7 * rowA 5 1 7 + yW_1409 8 * rowA 5 1 8 ≤ db_1409 5 1 := by
  have hleft : yW_1409 0 * rowA 5 1 0 + yW_1409 1 * rowA 5 1 1 + yW_1409 2 * rowA 5 1 2 + yW_1409 3 * rowA 5 1 3 + yW_1409 4 * rowA 5 1 4 + yW_1409 5 * rowA 5 1 5 + yW_1409 6 * rowA 5 1 6 + yW_1409 7 * rowA 5 1 7 + yW_1409 8 * rowA 5 1 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 5 1 = (-3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_5_2 :
    yW_1409 0 * rowA 5 2 0 + yW_1409 1 * rowA 5 2 1 + yW_1409 2 * rowA 5 2 2 + yW_1409 3 * rowA 5 2 3 + yW_1409 4 * rowA 5 2 4 + yW_1409 5 * rowA 5 2 5 + yW_1409 6 * rowA 5 2 6 + yW_1409 7 * rowA 5 2 7 + yW_1409 8 * rowA 5 2 8 ≤ db_1409 5 2 := by
  have hleft : yW_1409 0 * rowA 5 2 0 + yW_1409 1 * rowA 5 2 1 + yW_1409 2 * rowA 5 2 2 + yW_1409 3 * rowA 5 2 3 + yW_1409 4 * rowA 5 2 4 + yW_1409 5 * rowA 5 2 5 + yW_1409 6 * rowA 5 2 6 + yW_1409 7 * rowA 5 2 7 + yW_1409 8 * rowA 5 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 5 2 = (-3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_5_3 :
    yW_1409 0 * rowA 5 3 0 + yW_1409 1 * rowA 5 3 1 + yW_1409 2 * rowA 5 3 2 + yW_1409 3 * rowA 5 3 3 + yW_1409 4 * rowA 5 3 4 + yW_1409 5 * rowA 5 3 5 + yW_1409 6 * rowA 5 3 6 + yW_1409 7 * rowA 5 3 7 + yW_1409 8 * rowA 5 3 8 ≤ db_1409 5 3 := by
  have hleft : yW_1409 0 * rowA 5 3 0 + yW_1409 1 * rowA 5 3 1 + yW_1409 2 * rowA 5 3 2 + yW_1409 3 * rowA 5 3 3 + yW_1409 4 * rowA 5 3 4 + yW_1409 5 * rowA 5 3 5 + yW_1409 6 * rowA 5 3 6 + yW_1409 7 * rowA 5 3 7 + yW_1409 8 * rowA 5 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 5 3 = (-3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_5_4 :
    yW_1409 0 * rowA 5 4 0 + yW_1409 1 * rowA 5 4 1 + yW_1409 2 * rowA 5 4 2 + yW_1409 3 * rowA 5 4 3 + yW_1409 4 * rowA 5 4 4 + yW_1409 5 * rowA 5 4 5 + yW_1409 6 * rowA 5 4 6 + yW_1409 7 * rowA 5 4 7 + yW_1409 8 * rowA 5 4 8 ≤ db_1409 5 4 := by
  have hleft : yW_1409 0 * rowA 5 4 0 + yW_1409 1 * rowA 5 4 1 + yW_1409 2 * rowA 5 4 2 + yW_1409 3 * rowA 5 4 3 + yW_1409 4 * rowA 5 4 4 + yW_1409 5 * rowA 5 4 5 + yW_1409 6 * rowA 5 4 6 + yW_1409 7 * rowA 5 4 7 + yW_1409 8 * rowA 5 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 5 4 = (-1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_5_5 :
    yW_1409 0 * rowA 5 5 0 + yW_1409 1 * rowA 5 5 1 + yW_1409 2 * rowA 5 5 2 + yW_1409 3 * rowA 5 5 3 + yW_1409 4 * rowA 5 5 4 + yW_1409 5 * rowA 5 5 5 + yW_1409 6 * rowA 5 5 6 + yW_1409 7 * rowA 5 5 7 + yW_1409 8 * rowA 5 5 8 ≤ db_1409 5 5 := by
  have hleft : yW_1409 0 * rowA 5 5 0 + yW_1409 1 * rowA 5 5 1 + yW_1409 2 * rowA 5 5 2 + yW_1409 3 * rowA 5 5 3 + yW_1409 4 * rowA 5 5 4 + yW_1409 5 * rowA 5 5 5 + yW_1409 6 * rowA 5 5 6 + yW_1409 7 * rowA 5 5 7 + yW_1409 8 * rowA 5 5 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 5 5 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_5_6 :
    yW_1409 0 * rowA 5 6 0 + yW_1409 1 * rowA 5 6 1 + yW_1409 2 * rowA 5 6 2 + yW_1409 3 * rowA 5 6 3 + yW_1409 4 * rowA 5 6 4 + yW_1409 5 * rowA 5 6 5 + yW_1409 6 * rowA 5 6 6 + yW_1409 7 * rowA 5 6 7 + yW_1409 8 * rowA 5 6 8 ≤ db_1409 5 6 := by
  have hleft : yW_1409 0 * rowA 5 6 0 + yW_1409 1 * rowA 5 6 1 + yW_1409 2 * rowA 5 6 2 + yW_1409 3 * rowA 5 6 3 + yW_1409 4 * rowA 5 6 4 + yW_1409 5 * rowA 5 6 5 + yW_1409 6 * rowA 5 6 6 + yW_1409 7 * rowA 5 6 7 + yW_1409 8 * rowA 5 6 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 5 6 = (1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_5_7 :
    yW_1409 0 * rowA 5 7 0 + yW_1409 1 * rowA 5 7 1 + yW_1409 2 * rowA 5 7 2 + yW_1409 3 * rowA 5 7 3 + yW_1409 4 * rowA 5 7 4 + yW_1409 5 * rowA 5 7 5 + yW_1409 6 * rowA 5 7 6 + yW_1409 7 * rowA 5 7 7 + yW_1409 8 * rowA 5 7 8 ≤ db_1409 5 7 := by
  have hleft : yW_1409 0 * rowA 5 7 0 + yW_1409 1 * rowA 5 7 1 + yW_1409 2 * rowA 5 7 2 + yW_1409 3 * rowA 5 7 3 + yW_1409 4 * rowA 5 7 4 + yW_1409 5 * rowA 5 7 5 + yW_1409 6 * rowA 5 7 6 + yW_1409 7 * rowA 5 7 7 + yW_1409 8 * rowA 5 7 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 5 7 = (1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_5_8 :
    yW_1409 0 * rowA 5 8 0 + yW_1409 1 * rowA 5 8 1 + yW_1409 2 * rowA 5 8 2 + yW_1409 3 * rowA 5 8 3 + yW_1409 4 * rowA 5 8 4 + yW_1409 5 * rowA 5 8 5 + yW_1409 6 * rowA 5 8 6 + yW_1409 7 * rowA 5 8 7 + yW_1409 8 * rowA 5 8 8 ≤ db_1409 5 8 := by
  have hleft : yW_1409 0 * rowA 5 8 0 + yW_1409 1 * rowA 5 8 1 + yW_1409 2 * rowA 5 8 2 + yW_1409 3 * rowA 5 8 3 + yW_1409 4 * rowA 5 8 4 + yW_1409 5 * rowA 5 8 5 + yW_1409 6 * rowA 5 8 6 + yW_1409 7 * rowA 5 8 7 + yW_1409 8 * rowA 5 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 5 8 = (1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_5_9 :
    yW_1409 0 * rowA 5 9 0 + yW_1409 1 * rowA 5 9 1 + yW_1409 2 * rowA 5 9 2 + yW_1409 3 * rowA 5 9 3 + yW_1409 4 * rowA 5 9 4 + yW_1409 5 * rowA 5 9 5 + yW_1409 6 * rowA 5 9 6 + yW_1409 7 * rowA 5 9 7 + yW_1409 8 * rowA 5 9 8 ≤ db_1409 5 9 := by
  have hleft : yW_1409 0 * rowA 5 9 0 + yW_1409 1 * rowA 5 9 1 + yW_1409 2 * rowA 5 9 2 + yW_1409 3 * rowA 5 9 3 + yW_1409 4 * rowA 5 9 4 + yW_1409 5 * rowA 5 9 5 + yW_1409 6 * rowA 5 9 6 + yW_1409 7 * rowA 5 9 7 + yW_1409 8 * rowA 5 9 8 = (3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 5 9 = (1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_6_0 :
    yW_1409 0 * rowA 6 0 0 + yW_1409 1 * rowA 6 0 1 + yW_1409 2 * rowA 6 0 2 + yW_1409 3 * rowA 6 0 3 + yW_1409 4 * rowA 6 0 4 + yW_1409 5 * rowA 6 0 5 + yW_1409 6 * rowA 6 0 6 + yW_1409 7 * rowA 6 0 7 + yW_1409 8 * rowA 6 0 8 ≤ db_1409 6 0 := by
  have hleft : yW_1409 0 * rowA 6 0 0 + yW_1409 1 * rowA 6 0 1 + yW_1409 2 * rowA 6 0 2 + yW_1409 3 * rowA 6 0 3 + yW_1409 4 * rowA 6 0 4 + yW_1409 5 * rowA 6 0 5 + yW_1409 6 * rowA 6 0 6 + yW_1409 7 * rowA 6 0 7 + yW_1409 8 * rowA 6 0 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 6 0 = (-1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_6_1 :
    yW_1409 0 * rowA 6 1 0 + yW_1409 1 * rowA 6 1 1 + yW_1409 2 * rowA 6 1 2 + yW_1409 3 * rowA 6 1 3 + yW_1409 4 * rowA 6 1 4 + yW_1409 5 * rowA 6 1 5 + yW_1409 6 * rowA 6 1 6 + yW_1409 7 * rowA 6 1 7 + yW_1409 8 * rowA 6 1 8 ≤ db_1409 6 1 := by
  have hleft : yW_1409 0 * rowA 6 1 0 + yW_1409 1 * rowA 6 1 1 + yW_1409 2 * rowA 6 1 2 + yW_1409 3 * rowA 6 1 3 + yW_1409 4 * rowA 6 1 4 + yW_1409 5 * rowA 6 1 5 + yW_1409 6 * rowA 6 1 6 + yW_1409 7 * rowA 6 1 7 + yW_1409 8 * rowA 6 1 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 6 1 = (-3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_6_2 :
    yW_1409 0 * rowA 6 2 0 + yW_1409 1 * rowA 6 2 1 + yW_1409 2 * rowA 6 2 2 + yW_1409 3 * rowA 6 2 3 + yW_1409 4 * rowA 6 2 4 + yW_1409 5 * rowA 6 2 5 + yW_1409 6 * rowA 6 2 6 + yW_1409 7 * rowA 6 2 7 + yW_1409 8 * rowA 6 2 8 ≤ db_1409 6 2 := by
  have hleft : yW_1409 0 * rowA 6 2 0 + yW_1409 1 * rowA 6 2 1 + yW_1409 2 * rowA 6 2 2 + yW_1409 3 * rowA 6 2 3 + yW_1409 4 * rowA 6 2 4 + yW_1409 5 * rowA 6 2 5 + yW_1409 6 * rowA 6 2 6 + yW_1409 7 * rowA 6 2 7 + yW_1409 8 * rowA 6 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 6 2 = (-3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_6_3 :
    yW_1409 0 * rowA 6 3 0 + yW_1409 1 * rowA 6 3 1 + yW_1409 2 * rowA 6 3 2 + yW_1409 3 * rowA 6 3 3 + yW_1409 4 * rowA 6 3 4 + yW_1409 5 * rowA 6 3 5 + yW_1409 6 * rowA 6 3 6 + yW_1409 7 * rowA 6 3 7 + yW_1409 8 * rowA 6 3 8 ≤ db_1409 6 3 := by
  have hleft : yW_1409 0 * rowA 6 3 0 + yW_1409 1 * rowA 6 3 1 + yW_1409 2 * rowA 6 3 2 + yW_1409 3 * rowA 6 3 3 + yW_1409 4 * rowA 6 3 4 + yW_1409 5 * rowA 6 3 5 + yW_1409 6 * rowA 6 3 6 + yW_1409 7 * rowA 6 3 7 + yW_1409 8 * rowA 6 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 6 3 = (-3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_6_4 :
    yW_1409 0 * rowA 6 4 0 + yW_1409 1 * rowA 6 4 1 + yW_1409 2 * rowA 6 4 2 + yW_1409 3 * rowA 6 4 3 + yW_1409 4 * rowA 6 4 4 + yW_1409 5 * rowA 6 4 5 + yW_1409 6 * rowA 6 4 6 + yW_1409 7 * rowA 6 4 7 + yW_1409 8 * rowA 6 4 8 ≤ db_1409 6 4 := by
  have hleft : yW_1409 0 * rowA 6 4 0 + yW_1409 1 * rowA 6 4 1 + yW_1409 2 * rowA 6 4 2 + yW_1409 3 * rowA 6 4 3 + yW_1409 4 * rowA 6 4 4 + yW_1409 5 * rowA 6 4 5 + yW_1409 6 * rowA 6 4 6 + yW_1409 7 * rowA 6 4 7 + yW_1409 8 * rowA 6 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 6 4 = (-1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_6_5 :
    yW_1409 0 * rowA 6 5 0 + yW_1409 1 * rowA 6 5 1 + yW_1409 2 * rowA 6 5 2 + yW_1409 3 * rowA 6 5 3 + yW_1409 4 * rowA 6 5 4 + yW_1409 5 * rowA 6 5 5 + yW_1409 6 * rowA 6 5 6 + yW_1409 7 * rowA 6 5 7 + yW_1409 8 * rowA 6 5 8 ≤ db_1409 6 5 := by
  have hleft : yW_1409 0 * rowA 6 5 0 + yW_1409 1 * rowA 6 5 1 + yW_1409 2 * rowA 6 5 2 + yW_1409 3 * rowA 6 5 3 + yW_1409 4 * rowA 6 5 4 + yW_1409 5 * rowA 6 5 5 + yW_1409 6 * rowA 6 5 6 + yW_1409 7 * rowA 6 5 7 + yW_1409 8 * rowA 6 5 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 6 5 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_6_6 :
    yW_1409 0 * rowA 6 6 0 + yW_1409 1 * rowA 6 6 1 + yW_1409 2 * rowA 6 6 2 + yW_1409 3 * rowA 6 6 3 + yW_1409 4 * rowA 6 6 4 + yW_1409 5 * rowA 6 6 5 + yW_1409 6 * rowA 6 6 6 + yW_1409 7 * rowA 6 6 7 + yW_1409 8 * rowA 6 6 8 ≤ db_1409 6 6 := by
  have hleft : yW_1409 0 * rowA 6 6 0 + yW_1409 1 * rowA 6 6 1 + yW_1409 2 * rowA 6 6 2 + yW_1409 3 * rowA 6 6 3 + yW_1409 4 * rowA 6 6 4 + yW_1409 5 * rowA 6 6 5 + yW_1409 6 * rowA 6 6 6 + yW_1409 7 * rowA 6 6 7 + yW_1409 8 * rowA 6 6 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 6 6 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_6_7 :
    yW_1409 0 * rowA 6 7 0 + yW_1409 1 * rowA 6 7 1 + yW_1409 2 * rowA 6 7 2 + yW_1409 3 * rowA 6 7 3 + yW_1409 4 * rowA 6 7 4 + yW_1409 5 * rowA 6 7 5 + yW_1409 6 * rowA 6 7 6 + yW_1409 7 * rowA 6 7 7 + yW_1409 8 * rowA 6 7 8 ≤ db_1409 6 7 := by
  have hleft : yW_1409 0 * rowA 6 7 0 + yW_1409 1 * rowA 6 7 1 + yW_1409 2 * rowA 6 7 2 + yW_1409 3 * rowA 6 7 3 + yW_1409 4 * rowA 6 7 4 + yW_1409 5 * rowA 6 7 5 + yW_1409 6 * rowA 6 7 6 + yW_1409 7 * rowA 6 7 7 + yW_1409 8 * rowA 6 7 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 6 7 = (1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_6_8 :
    yW_1409 0 * rowA 6 8 0 + yW_1409 1 * rowA 6 8 1 + yW_1409 2 * rowA 6 8 2 + yW_1409 3 * rowA 6 8 3 + yW_1409 4 * rowA 6 8 4 + yW_1409 5 * rowA 6 8 5 + yW_1409 6 * rowA 6 8 6 + yW_1409 7 * rowA 6 8 7 + yW_1409 8 * rowA 6 8 8 ≤ db_1409 6 8 := by
  have hleft : yW_1409 0 * rowA 6 8 0 + yW_1409 1 * rowA 6 8 1 + yW_1409 2 * rowA 6 8 2 + yW_1409 3 * rowA 6 8 3 + yW_1409 4 * rowA 6 8 4 + yW_1409 5 * rowA 6 8 5 + yW_1409 6 * rowA 6 8 6 + yW_1409 7 * rowA 6 8 7 + yW_1409 8 * rowA 6 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 6 8 = (1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_6_9 :
    yW_1409 0 * rowA 6 9 0 + yW_1409 1 * rowA 6 9 1 + yW_1409 2 * rowA 6 9 2 + yW_1409 3 * rowA 6 9 3 + yW_1409 4 * rowA 6 9 4 + yW_1409 5 * rowA 6 9 5 + yW_1409 6 * rowA 6 9 6 + yW_1409 7 * rowA 6 9 7 + yW_1409 8 * rowA 6 9 8 ≤ db_1409 6 9 := by
  have hleft : yW_1409 0 * rowA 6 9 0 + yW_1409 1 * rowA 6 9 1 + yW_1409 2 * rowA 6 9 2 + yW_1409 3 * rowA 6 9 3 + yW_1409 4 * rowA 6 9 4 + yW_1409 5 * rowA 6 9 5 + yW_1409 6 * rowA 6 9 6 + yW_1409 7 * rowA 6 9 7 + yW_1409 8 * rowA 6 9 8 = (3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 6 9 = (1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_7_0 :
    yW_1409 0 * rowA 7 0 0 + yW_1409 1 * rowA 7 0 1 + yW_1409 2 * rowA 7 0 2 + yW_1409 3 * rowA 7 0 3 + yW_1409 4 * rowA 7 0 4 + yW_1409 5 * rowA 7 0 5 + yW_1409 6 * rowA 7 0 6 + yW_1409 7 * rowA 7 0 7 + yW_1409 8 * rowA 7 0 8 ≤ db_1409 7 0 := by
  have hleft : yW_1409 0 * rowA 7 0 0 + yW_1409 1 * rowA 7 0 1 + yW_1409 2 * rowA 7 0 2 + yW_1409 3 * rowA 7 0 3 + yW_1409 4 * rowA 7 0 4 + yW_1409 5 * rowA 7 0 5 + yW_1409 6 * rowA 7 0 6 + yW_1409 7 * rowA 7 0 7 + yW_1409 8 * rowA 7 0 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 7 0 = (-1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_7_1 :
    yW_1409 0 * rowA 7 1 0 + yW_1409 1 * rowA 7 1 1 + yW_1409 2 * rowA 7 1 2 + yW_1409 3 * rowA 7 1 3 + yW_1409 4 * rowA 7 1 4 + yW_1409 5 * rowA 7 1 5 + yW_1409 6 * rowA 7 1 6 + yW_1409 7 * rowA 7 1 7 + yW_1409 8 * rowA 7 1 8 ≤ db_1409 7 1 := by
  have hleft : yW_1409 0 * rowA 7 1 0 + yW_1409 1 * rowA 7 1 1 + yW_1409 2 * rowA 7 1 2 + yW_1409 3 * rowA 7 1 3 + yW_1409 4 * rowA 7 1 4 + yW_1409 5 * rowA 7 1 5 + yW_1409 6 * rowA 7 1 6 + yW_1409 7 * rowA 7 1 7 + yW_1409 8 * rowA 7 1 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 7 1 = (-3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_7_2 :
    yW_1409 0 * rowA 7 2 0 + yW_1409 1 * rowA 7 2 1 + yW_1409 2 * rowA 7 2 2 + yW_1409 3 * rowA 7 2 3 + yW_1409 4 * rowA 7 2 4 + yW_1409 5 * rowA 7 2 5 + yW_1409 6 * rowA 7 2 6 + yW_1409 7 * rowA 7 2 7 + yW_1409 8 * rowA 7 2 8 ≤ db_1409 7 2 := by
  have hleft : yW_1409 0 * rowA 7 2 0 + yW_1409 1 * rowA 7 2 1 + yW_1409 2 * rowA 7 2 2 + yW_1409 3 * rowA 7 2 3 + yW_1409 4 * rowA 7 2 4 + yW_1409 5 * rowA 7 2 5 + yW_1409 6 * rowA 7 2 6 + yW_1409 7 * rowA 7 2 7 + yW_1409 8 * rowA 7 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 7 2 = (-3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_7_3 :
    yW_1409 0 * rowA 7 3 0 + yW_1409 1 * rowA 7 3 1 + yW_1409 2 * rowA 7 3 2 + yW_1409 3 * rowA 7 3 3 + yW_1409 4 * rowA 7 3 4 + yW_1409 5 * rowA 7 3 5 + yW_1409 6 * rowA 7 3 6 + yW_1409 7 * rowA 7 3 7 + yW_1409 8 * rowA 7 3 8 ≤ db_1409 7 3 := by
  have hleft : yW_1409 0 * rowA 7 3 0 + yW_1409 1 * rowA 7 3 1 + yW_1409 2 * rowA 7 3 2 + yW_1409 3 * rowA 7 3 3 + yW_1409 4 * rowA 7 3 4 + yW_1409 5 * rowA 7 3 5 + yW_1409 6 * rowA 7 3 6 + yW_1409 7 * rowA 7 3 7 + yW_1409 8 * rowA 7 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 7 3 = (-3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_7_4 :
    yW_1409 0 * rowA 7 4 0 + yW_1409 1 * rowA 7 4 1 + yW_1409 2 * rowA 7 4 2 + yW_1409 3 * rowA 7 4 3 + yW_1409 4 * rowA 7 4 4 + yW_1409 5 * rowA 7 4 5 + yW_1409 6 * rowA 7 4 6 + yW_1409 7 * rowA 7 4 7 + yW_1409 8 * rowA 7 4 8 ≤ db_1409 7 4 := by
  have hleft : yW_1409 0 * rowA 7 4 0 + yW_1409 1 * rowA 7 4 1 + yW_1409 2 * rowA 7 4 2 + yW_1409 3 * rowA 7 4 3 + yW_1409 4 * rowA 7 4 4 + yW_1409 5 * rowA 7 4 5 + yW_1409 6 * rowA 7 4 6 + yW_1409 7 * rowA 7 4 7 + yW_1409 8 * rowA 7 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 7 4 = (-1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_7_5 :
    yW_1409 0 * rowA 7 5 0 + yW_1409 1 * rowA 7 5 1 + yW_1409 2 * rowA 7 5 2 + yW_1409 3 * rowA 7 5 3 + yW_1409 4 * rowA 7 5 4 + yW_1409 5 * rowA 7 5 5 + yW_1409 6 * rowA 7 5 6 + yW_1409 7 * rowA 7 5 7 + yW_1409 8 * rowA 7 5 8 ≤ db_1409 7 5 := by
  have hleft : yW_1409 0 * rowA 7 5 0 + yW_1409 1 * rowA 7 5 1 + yW_1409 2 * rowA 7 5 2 + yW_1409 3 * rowA 7 5 3 + yW_1409 4 * rowA 7 5 4 + yW_1409 5 * rowA 7 5 5 + yW_1409 6 * rowA 7 5 6 + yW_1409 7 * rowA 7 5 7 + yW_1409 8 * rowA 7 5 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 7 5 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_7_6 :
    yW_1409 0 * rowA 7 6 0 + yW_1409 1 * rowA 7 6 1 + yW_1409 2 * rowA 7 6 2 + yW_1409 3 * rowA 7 6 3 + yW_1409 4 * rowA 7 6 4 + yW_1409 5 * rowA 7 6 5 + yW_1409 6 * rowA 7 6 6 + yW_1409 7 * rowA 7 6 7 + yW_1409 8 * rowA 7 6 8 ≤ db_1409 7 6 := by
  have hleft : yW_1409 0 * rowA 7 6 0 + yW_1409 1 * rowA 7 6 1 + yW_1409 2 * rowA 7 6 2 + yW_1409 3 * rowA 7 6 3 + yW_1409 4 * rowA 7 6 4 + yW_1409 5 * rowA 7 6 5 + yW_1409 6 * rowA 7 6 6 + yW_1409 7 * rowA 7 6 7 + yW_1409 8 * rowA 7 6 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 7 6 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_7_7 :
    yW_1409 0 * rowA 7 7 0 + yW_1409 1 * rowA 7 7 1 + yW_1409 2 * rowA 7 7 2 + yW_1409 3 * rowA 7 7 3 + yW_1409 4 * rowA 7 7 4 + yW_1409 5 * rowA 7 7 5 + yW_1409 6 * rowA 7 7 6 + yW_1409 7 * rowA 7 7 7 + yW_1409 8 * rowA 7 7 8 ≤ db_1409 7 7 := by
  have hleft : yW_1409 0 * rowA 7 7 0 + yW_1409 1 * rowA 7 7 1 + yW_1409 2 * rowA 7 7 2 + yW_1409 3 * rowA 7 7 3 + yW_1409 4 * rowA 7 7 4 + yW_1409 5 * rowA 7 7 5 + yW_1409 6 * rowA 7 7 6 + yW_1409 7 * rowA 7 7 7 + yW_1409 8 * rowA 7 7 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 7 7 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_7_8 :
    yW_1409 0 * rowA 7 8 0 + yW_1409 1 * rowA 7 8 1 + yW_1409 2 * rowA 7 8 2 + yW_1409 3 * rowA 7 8 3 + yW_1409 4 * rowA 7 8 4 + yW_1409 5 * rowA 7 8 5 + yW_1409 6 * rowA 7 8 6 + yW_1409 7 * rowA 7 8 7 + yW_1409 8 * rowA 7 8 8 ≤ db_1409 7 8 := by
  have hleft : yW_1409 0 * rowA 7 8 0 + yW_1409 1 * rowA 7 8 1 + yW_1409 2 * rowA 7 8 2 + yW_1409 3 * rowA 7 8 3 + yW_1409 4 * rowA 7 8 4 + yW_1409 5 * rowA 7 8 5 + yW_1409 6 * rowA 7 8 6 + yW_1409 7 * rowA 7 8 7 + yW_1409 8 * rowA 7 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 7 8 = (1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_7_9 :
    yW_1409 0 * rowA 7 9 0 + yW_1409 1 * rowA 7 9 1 + yW_1409 2 * rowA 7 9 2 + yW_1409 3 * rowA 7 9 3 + yW_1409 4 * rowA 7 9 4 + yW_1409 5 * rowA 7 9 5 + yW_1409 6 * rowA 7 9 6 + yW_1409 7 * rowA 7 9 7 + yW_1409 8 * rowA 7 9 8 ≤ db_1409 7 9 := by
  have hleft : yW_1409 0 * rowA 7 9 0 + yW_1409 1 * rowA 7 9 1 + yW_1409 2 * rowA 7 9 2 + yW_1409 3 * rowA 7 9 3 + yW_1409 4 * rowA 7 9 4 + yW_1409 5 * rowA 7 9 5 + yW_1409 6 * rowA 7 9 6 + yW_1409 7 * rowA 7 9 7 + yW_1409 8 * rowA 7 9 8 = (3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 7 9 = (1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_8_0 :
    yW_1409 0 * rowA 8 0 0 + yW_1409 1 * rowA 8 0 1 + yW_1409 2 * rowA 8 0 2 + yW_1409 3 * rowA 8 0 3 + yW_1409 4 * rowA 8 0 4 + yW_1409 5 * rowA 8 0 5 + yW_1409 6 * rowA 8 0 6 + yW_1409 7 * rowA 8 0 7 + yW_1409 8 * rowA 8 0 8 ≤ db_1409 8 0 := by
  have hleft : yW_1409 0 * rowA 8 0 0 + yW_1409 1 * rowA 8 0 1 + yW_1409 2 * rowA 8 0 2 + yW_1409 3 * rowA 8 0 3 + yW_1409 4 * rowA 8 0 4 + yW_1409 5 * rowA 8 0 5 + yW_1409 6 * rowA 8 0 6 + yW_1409 7 * rowA 8 0 7 + yW_1409 8 * rowA 8 0 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 8 0 = (-5 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_8_1 :
    yW_1409 0 * rowA 8 1 0 + yW_1409 1 * rowA 8 1 1 + yW_1409 2 * rowA 8 1 2 + yW_1409 3 * rowA 8 1 3 + yW_1409 4 * rowA 8 1 4 + yW_1409 5 * rowA 8 1 5 + yW_1409 6 * rowA 8 1 6 + yW_1409 7 * rowA 8 1 7 + yW_1409 8 * rowA 8 1 8 ≤ db_1409 8 1 := by
  have hleft : yW_1409 0 * rowA 8 1 0 + yW_1409 1 * rowA 8 1 1 + yW_1409 2 * rowA 8 1 2 + yW_1409 3 * rowA 8 1 3 + yW_1409 4 * rowA 8 1 4 + yW_1409 5 * rowA 8 1 5 + yW_1409 6 * rowA 8 1 6 + yW_1409 7 * rowA 8 1 7 + yW_1409 8 * rowA 8 1 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 8 1 = (-1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_8_2 :
    yW_1409 0 * rowA 8 2 0 + yW_1409 1 * rowA 8 2 1 + yW_1409 2 * rowA 8 2 2 + yW_1409 3 * rowA 8 2 3 + yW_1409 4 * rowA 8 2 4 + yW_1409 5 * rowA 8 2 5 + yW_1409 6 * rowA 8 2 6 + yW_1409 7 * rowA 8 2 7 + yW_1409 8 * rowA 8 2 8 ≤ db_1409 8 2 := by
  have hleft : yW_1409 0 * rowA 8 2 0 + yW_1409 1 * rowA 8 2 1 + yW_1409 2 * rowA 8 2 2 + yW_1409 3 * rowA 8 2 3 + yW_1409 4 * rowA 8 2 4 + yW_1409 5 * rowA 8 2 5 + yW_1409 6 * rowA 8 2 6 + yW_1409 7 * rowA 8 2 7 + yW_1409 8 * rowA 8 2 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 8 2 = (-1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_8_3 :
    yW_1409 0 * rowA 8 3 0 + yW_1409 1 * rowA 8 3 1 + yW_1409 2 * rowA 8 3 2 + yW_1409 3 * rowA 8 3 3 + yW_1409 4 * rowA 8 3 4 + yW_1409 5 * rowA 8 3 5 + yW_1409 6 * rowA 8 3 6 + yW_1409 7 * rowA 8 3 7 + yW_1409 8 * rowA 8 3 8 ≤ db_1409 8 3 := by
  have hleft : yW_1409 0 * rowA 8 3 0 + yW_1409 1 * rowA 8 3 1 + yW_1409 2 * rowA 8 3 2 + yW_1409 3 * rowA 8 3 3 + yW_1409 4 * rowA 8 3 4 + yW_1409 5 * rowA 8 3 5 + yW_1409 6 * rowA 8 3 6 + yW_1409 7 * rowA 8 3 7 + yW_1409 8 * rowA 8 3 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 8 3 = (-1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_8_4 :
    yW_1409 0 * rowA 8 4 0 + yW_1409 1 * rowA 8 4 1 + yW_1409 2 * rowA 8 4 2 + yW_1409 3 * rowA 8 4 3 + yW_1409 4 * rowA 8 4 4 + yW_1409 5 * rowA 8 4 5 + yW_1409 6 * rowA 8 4 6 + yW_1409 7 * rowA 8 4 7 + yW_1409 8 * rowA 8 4 8 ≤ db_1409 8 4 := by
  have hleft : yW_1409 0 * rowA 8 4 0 + yW_1409 1 * rowA 8 4 1 + yW_1409 2 * rowA 8 4 2 + yW_1409 3 * rowA 8 4 3 + yW_1409 4 * rowA 8 4 4 + yW_1409 5 * rowA 8 4 5 + yW_1409 6 * rowA 8 4 6 + yW_1409 7 * rowA 8 4 7 + yW_1409 8 * rowA 8 4 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 8 4 = (-1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_8_5 :
    yW_1409 0 * rowA 8 5 0 + yW_1409 1 * rowA 8 5 1 + yW_1409 2 * rowA 8 5 2 + yW_1409 3 * rowA 8 5 3 + yW_1409 4 * rowA 8 5 4 + yW_1409 5 * rowA 8 5 5 + yW_1409 6 * rowA 8 5 6 + yW_1409 7 * rowA 8 5 7 + yW_1409 8 * rowA 8 5 8 ≤ db_1409 8 5 := by
  have hleft : yW_1409 0 * rowA 8 5 0 + yW_1409 1 * rowA 8 5 1 + yW_1409 2 * rowA 8 5 2 + yW_1409 3 * rowA 8 5 3 + yW_1409 4 * rowA 8 5 4 + yW_1409 5 * rowA 8 5 5 + yW_1409 6 * rowA 8 5 6 + yW_1409 7 * rowA 8 5 7 + yW_1409 8 * rowA 8 5 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 8 5 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_8_6 :
    yW_1409 0 * rowA 8 6 0 + yW_1409 1 * rowA 8 6 1 + yW_1409 2 * rowA 8 6 2 + yW_1409 3 * rowA 8 6 3 + yW_1409 4 * rowA 8 6 4 + yW_1409 5 * rowA 8 6 5 + yW_1409 6 * rowA 8 6 6 + yW_1409 7 * rowA 8 6 7 + yW_1409 8 * rowA 8 6 8 ≤ db_1409 8 6 := by
  have hleft : yW_1409 0 * rowA 8 6 0 + yW_1409 1 * rowA 8 6 1 + yW_1409 2 * rowA 8 6 2 + yW_1409 3 * rowA 8 6 3 + yW_1409 4 * rowA 8 6 4 + yW_1409 5 * rowA 8 6 5 + yW_1409 6 * rowA 8 6 6 + yW_1409 7 * rowA 8 6 7 + yW_1409 8 * rowA 8 6 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 8 6 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_8_7 :
    yW_1409 0 * rowA 8 7 0 + yW_1409 1 * rowA 8 7 1 + yW_1409 2 * rowA 8 7 2 + yW_1409 3 * rowA 8 7 3 + yW_1409 4 * rowA 8 7 4 + yW_1409 5 * rowA 8 7 5 + yW_1409 6 * rowA 8 7 6 + yW_1409 7 * rowA 8 7 7 + yW_1409 8 * rowA 8 7 8 ≤ db_1409 8 7 := by
  have hleft : yW_1409 0 * rowA 8 7 0 + yW_1409 1 * rowA 8 7 1 + yW_1409 2 * rowA 8 7 2 + yW_1409 3 * rowA 8 7 3 + yW_1409 4 * rowA 8 7 4 + yW_1409 5 * rowA 8 7 5 + yW_1409 6 * rowA 8 7 6 + yW_1409 7 * rowA 8 7 7 + yW_1409 8 * rowA 8 7 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 8 7 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_8_8 :
    yW_1409 0 * rowA 8 8 0 + yW_1409 1 * rowA 8 8 1 + yW_1409 2 * rowA 8 8 2 + yW_1409 3 * rowA 8 8 3 + yW_1409 4 * rowA 8 8 4 + yW_1409 5 * rowA 8 8 5 + yW_1409 6 * rowA 8 8 6 + yW_1409 7 * rowA 8 8 7 + yW_1409 8 * rowA 8 8 8 ≤ db_1409 8 8 := by
  have hleft : yW_1409 0 * rowA 8 8 0 + yW_1409 1 * rowA 8 8 1 + yW_1409 2 * rowA 8 8 2 + yW_1409 3 * rowA 8 8 3 + yW_1409 4 * rowA 8 8 4 + yW_1409 5 * rowA 8 8 5 + yW_1409 6 * rowA 8 8 6 + yW_1409 7 * rowA 8 8 7 + yW_1409 8 * rowA 8 8 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 8 8 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_8_9 :
    yW_1409 0 * rowA 8 9 0 + yW_1409 1 * rowA 8 9 1 + yW_1409 2 * rowA 8 9 2 + yW_1409 3 * rowA 8 9 3 + yW_1409 4 * rowA 8 9 4 + yW_1409 5 * rowA 8 9 5 + yW_1409 6 * rowA 8 9 6 + yW_1409 7 * rowA 8 9 7 + yW_1409 8 * rowA 8 9 8 ≤ db_1409 8 9 := by
  have hleft : yW_1409 0 * rowA 8 9 0 + yW_1409 1 * rowA 8 9 1 + yW_1409 2 * rowA 8 9 2 + yW_1409 3 * rowA 8 9 3 + yW_1409 4 * rowA 8 9 4 + yW_1409 5 * rowA 8 9 5 + yW_1409 6 * rowA 8 9 6 + yW_1409 7 * rowA 8 9 7 + yW_1409 8 * rowA 8 9 8 = (1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 8 9 = (3 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_9_0 :
    yW_1409 0 * rowA 9 0 0 + yW_1409 1 * rowA 9 0 1 + yW_1409 2 * rowA 9 0 2 + yW_1409 3 * rowA 9 0 3 + yW_1409 4 * rowA 9 0 4 + yW_1409 5 * rowA 9 0 5 + yW_1409 6 * rowA 9 0 6 + yW_1409 7 * rowA 9 0 7 + yW_1409 8 * rowA 9 0 8 ≤ db_1409 9 0 := by
  have hleft : yW_1409 0 * rowA 9 0 0 + yW_1409 1 * rowA 9 0 1 + yW_1409 2 * rowA 9 0 2 + yW_1409 3 * rowA 9 0 3 + yW_1409 4 * rowA 9 0 4 + yW_1409 5 * rowA 9 0 5 + yW_1409 6 * rowA 9 0 6 + yW_1409 7 * rowA 9 0 7 + yW_1409 8 * rowA 9 0 8 = (-1 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 9 0 = (-1 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_9_1 :
    yW_1409 0 * rowA 9 1 0 + yW_1409 1 * rowA 9 1 1 + yW_1409 2 * rowA 9 1 2 + yW_1409 3 * rowA 9 1 3 + yW_1409 4 * rowA 9 1 4 + yW_1409 5 * rowA 9 1 5 + yW_1409 6 * rowA 9 1 6 + yW_1409 7 * rowA 9 1 7 + yW_1409 8 * rowA 9 1 8 ≤ db_1409 9 1 := by
  have hleft : yW_1409 0 * rowA 9 1 0 + yW_1409 1 * rowA 9 1 1 + yW_1409 2 * rowA 9 1 2 + yW_1409 3 * rowA 9 1 3 + yW_1409 4 * rowA 9 1 4 + yW_1409 5 * rowA 9 1 5 + yW_1409 6 * rowA 9 1 6 + yW_1409 7 * rowA 9 1 7 + yW_1409 8 * rowA 9 1 8 = (-1 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 9 1 = (-3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_9_2 :
    yW_1409 0 * rowA 9 2 0 + yW_1409 1 * rowA 9 2 1 + yW_1409 2 * rowA 9 2 2 + yW_1409 3 * rowA 9 2 3 + yW_1409 4 * rowA 9 2 4 + yW_1409 5 * rowA 9 2 5 + yW_1409 6 * rowA 9 2 6 + yW_1409 7 * rowA 9 2 7 + yW_1409 8 * rowA 9 2 8 ≤ db_1409 9 2 := by
  have hleft : yW_1409 0 * rowA 9 2 0 + yW_1409 1 * rowA 9 2 1 + yW_1409 2 * rowA 9 2 2 + yW_1409 3 * rowA 9 2 3 + yW_1409 4 * rowA 9 2 4 + yW_1409 5 * rowA 9 2 5 + yW_1409 6 * rowA 9 2 6 + yW_1409 7 * rowA 9 2 7 + yW_1409 8 * rowA 9 2 8 = (-7 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 9 2 = (-3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_9_3 :
    yW_1409 0 * rowA 9 3 0 + yW_1409 1 * rowA 9 3 1 + yW_1409 2 * rowA 9 3 2 + yW_1409 3 * rowA 9 3 3 + yW_1409 4 * rowA 9 3 4 + yW_1409 5 * rowA 9 3 5 + yW_1409 6 * rowA 9 3 6 + yW_1409 7 * rowA 9 3 7 + yW_1409 8 * rowA 9 3 8 ≤ db_1409 9 3 := by
  have hleft : yW_1409 0 * rowA 9 3 0 + yW_1409 1 * rowA 9 3 1 + yW_1409 2 * rowA 9 3 2 + yW_1409 3 * rowA 9 3 3 + yW_1409 4 * rowA 9 3 4 + yW_1409 5 * rowA 9 3 5 + yW_1409 6 * rowA 9 3 6 + yW_1409 7 * rowA 9 3 7 + yW_1409 8 * rowA 9 3 8 = (-7 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 9 3 = (-3 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_9_4 :
    yW_1409 0 * rowA 9 4 0 + yW_1409 1 * rowA 9 4 1 + yW_1409 2 * rowA 9 4 2 + yW_1409 3 * rowA 9 4 3 + yW_1409 4 * rowA 9 4 4 + yW_1409 5 * rowA 9 4 5 + yW_1409 6 * rowA 9 4 6 + yW_1409 7 * rowA 9 4 7 + yW_1409 8 * rowA 9 4 8 ≤ db_1409 9 4 := by
  have hleft : yW_1409 0 * rowA 9 4 0 + yW_1409 1 * rowA 9 4 1 + yW_1409 2 * rowA 9 4 2 + yW_1409 3 * rowA 9 4 3 + yW_1409 4 * rowA 9 4 4 + yW_1409 5 * rowA 9 4 5 + yW_1409 6 * rowA 9 4 6 + yW_1409 7 * rowA 9 4 7 + yW_1409 8 * rowA 9 4 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 9 4 = (-1 : ℚ) / 2 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_9_5 :
    yW_1409 0 * rowA 9 5 0 + yW_1409 1 * rowA 9 5 1 + yW_1409 2 * rowA 9 5 2 + yW_1409 3 * rowA 9 5 3 + yW_1409 4 * rowA 9 5 4 + yW_1409 5 * rowA 9 5 5 + yW_1409 6 * rowA 9 5 6 + yW_1409 7 * rowA 9 5 7 + yW_1409 8 * rowA 9 5 8 ≤ db_1409 9 5 := by
  have hleft : yW_1409 0 * rowA 9 5 0 + yW_1409 1 * rowA 9 5 1 + yW_1409 2 * rowA 9 5 2 + yW_1409 3 * rowA 9 5 3 + yW_1409 4 * rowA 9 5 4 + yW_1409 5 * rowA 9 5 5 + yW_1409 6 * rowA 9 5 6 + yW_1409 7 * rowA 9 5 7 + yW_1409 8 * rowA 9 5 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 9 5 = (-1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_9_6 :
    yW_1409 0 * rowA 9 6 0 + yW_1409 1 * rowA 9 6 1 + yW_1409 2 * rowA 9 6 2 + yW_1409 3 * rowA 9 6 3 + yW_1409 4 * rowA 9 6 4 + yW_1409 5 * rowA 9 6 5 + yW_1409 6 * rowA 9 6 6 + yW_1409 7 * rowA 9 6 7 + yW_1409 8 * rowA 9 6 8 ≤ db_1409 9 6 := by
  have hleft : yW_1409 0 * rowA 9 6 0 + yW_1409 1 * rowA 9 6 1 + yW_1409 2 * rowA 9 6 2 + yW_1409 3 * rowA 9 6 3 + yW_1409 4 * rowA 9 6 4 + yW_1409 5 * rowA 9 6 5 + yW_1409 6 * rowA 9 6 6 + yW_1409 7 * rowA 9 6 7 + yW_1409 8 * rowA 9 6 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 9 6 = (-1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_9_7 :
    yW_1409 0 * rowA 9 7 0 + yW_1409 1 * rowA 9 7 1 + yW_1409 2 * rowA 9 7 2 + yW_1409 3 * rowA 9 7 3 + yW_1409 4 * rowA 9 7 4 + yW_1409 5 * rowA 9 7 5 + yW_1409 6 * rowA 9 7 6 + yW_1409 7 * rowA 9 7 7 + yW_1409 8 * rowA 9 7 8 ≤ db_1409 9 7 := by
  have hleft : yW_1409 0 * rowA 9 7 0 + yW_1409 1 * rowA 9 7 1 + yW_1409 2 * rowA 9 7 2 + yW_1409 3 * rowA 9 7 3 + yW_1409 4 * rowA 9 7 4 + yW_1409 5 * rowA 9 7 5 + yW_1409 6 * rowA 9 7 6 + yW_1409 7 * rowA 9 7 7 + yW_1409 8 * rowA 9 7 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 9 7 = (-1 : ℚ) / 4 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_9_8 :
    yW_1409 0 * rowA 9 8 0 + yW_1409 1 * rowA 9 8 1 + yW_1409 2 * rowA 9 8 2 + yW_1409 3 * rowA 9 8 3 + yW_1409 4 * rowA 9 8 4 + yW_1409 5 * rowA 9 8 5 + yW_1409 6 * rowA 9 8 6 + yW_1409 7 * rowA 9 8 7 + yW_1409 8 * rowA 9 8 8 ≤ db_1409 9 8 := by
  have hleft : yW_1409 0 * rowA 9 8 0 + yW_1409 1 * rowA 9 8 1 + yW_1409 2 * rowA 9 8 2 + yW_1409 3 * rowA 9 8 3 + yW_1409 4 * rowA 9 8 4 + yW_1409 5 * rowA 9 8 5 + yW_1409 6 * rowA 9 8 6 + yW_1409 7 * rowA 9 8 7 + yW_1409 8 * rowA 9 8 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 9 8 = (-1 : ℚ) / 8 := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_9_9 :
    yW_1409 0 * rowA 9 9 0 + yW_1409 1 * rowA 9 9 1 + yW_1409 2 * rowA 9 9 2 + yW_1409 3 * rowA 9 9 3 + yW_1409 4 * rowA 9 9 4 + yW_1409 5 * rowA 9 9 5 + yW_1409 6 * rowA 9 9 6 + yW_1409 7 * rowA 9 9 7 + yW_1409 8 * rowA 9 9 8 ≤ db_1409 9 9 := by
  have hleft : yW_1409 0 * rowA 9 9 0 + yW_1409 1 * rowA 9 9 1 + yW_1409 2 * rowA 9 9 2 + yW_1409 3 * rowA 9 9 3 + yW_1409 4 * rowA 9 9 4 + yW_1409 5 * rowA 9 9 5 + yW_1409 6 * rowA 9 9 6 + yW_1409 7 * rowA 9 9 7 + yW_1409 8 * rowA 9 9 8 = (0 : ℚ) := by
    norm_num [yW_1409, rowA]
  have hright : db_1409 9 9 = (0 : ℚ) := by
    norm_num [db_1409, dbmVal_1409]
  rw [hleft, hright]
  norm_num

theorem row_cap_1409_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 0 j q) ≤ db_1409 0 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_0_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_0_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_0_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_0_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_0_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_0_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_0_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_0_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_0_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_0_9

theorem row_cap_1409_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 1 j q) ≤ db_1409 1 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_1_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_1_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_1_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_1_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_1_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_1_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_1_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_1_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_1_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_1_9

theorem row_cap_1409_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 2 j q) ≤ db_1409 2 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_2_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_2_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_2_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_2_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_2_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_2_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_2_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_2_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_2_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_2_9

theorem row_cap_1409_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 3 j q) ≤ db_1409 3 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_3_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_3_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_3_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_3_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_3_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_3_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_3_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_3_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_3_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_3_9

theorem row_cap_1409_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 4 j q) ≤ db_1409 4 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_4_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_4_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_4_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_4_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_4_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_4_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_4_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_4_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_4_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_4_9

theorem row_cap_1409_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 5 j q) ≤ db_1409 5 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_5_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_5_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_5_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_5_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_5_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_5_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_5_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_5_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_5_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_5_9

theorem row_cap_1409_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 6 j q) ≤ db_1409 6 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_6_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_6_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_6_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_6_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_6_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_6_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_6_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_6_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_6_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_6_9

theorem row_cap_1409_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 7 j q) ≤ db_1409 7 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_7_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_7_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_7_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_7_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_7_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_7_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_7_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_7_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_7_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_7_9

theorem row_cap_1409_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 8 j q) ≤ db_1409 8 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_8_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_8_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_8_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_8_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_8_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_8_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_8_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_8_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_8_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_8_9

theorem row_cap_1409_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 9 j q) ≤ db_1409 9 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_9_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_9_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_9_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_9_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_9_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_9_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_9_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_9_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_9_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_1409_9_9

theorem row_cap_1409 (i j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA i j q) ≤ db_1409 i j := by
  fin_cases i
  · exact row_cap_1409_0 j
  · exact row_cap_1409_1 j
  · exact row_cap_1409_2 j
  · exact row_cap_1409_3 j
  · exact row_cap_1409_4 j
  · exact row_cap_1409_5 j
  · exact row_cap_1409_6 j
  · exact row_cap_1409_7 j
  · exact row_cap_1409_8 j
  · exact row_cap_1409_9 j

def dbmVal_2337 : Fin 10 → Fin 10 → ℤ
  | i, j => ![
      ![0, 768, 768, 768, 1280, 2048, 2048, 2816, 2816, 4096],
      ![0, 0, 768, 768, 1280, 2048, 2048, 2816, 2816, 4096],
      ![0, 0, 0, 768, 1280, 2048, 2048, 2816, 2816, 4096],
      ![0, 0, 0, 0, 1280, 2048, 2048, 2560, 2560, 4096],
      ![-1024, -512, -512, -512, 0, 1024, 1024, 1536, 1536, 3072],
      ![-1024, -1024, -1024, -1024, 0, 0, 1024, 1024, 1024, 3072],
      ![-1024, -1024, -1024, -1024, 0, 0, 0, 1024, 1024, 3072],
      ![-2048, -2048, -2048, -2048, -1024, 0, 0, 0, 512, 2048],
      ![-2048, -2048, -2048, -2048, -1024, -512, 0, 0, 0, 2048],
      ![-4096, -3328, -3328, -3328, -2816, -2048, -2048, -1280, -1280, 0]
    ] i j

def db_2337 (i j : Fin 10) : ℚ := (dbmVal_2337 i j : ℚ) / 4096

theorem row_cap_2337_0_0 :
    yW_2337 0 * rowA 0 0 0 + yW_2337 1 * rowA 0 0 1 + yW_2337 2 * rowA 0 0 2 + yW_2337 3 * rowA 0 0 3 + yW_2337 4 * rowA 0 0 4 + yW_2337 5 * rowA 0 0 5 + yW_2337 6 * rowA 0 0 6 + yW_2337 7 * rowA 0 0 7 + yW_2337 8 * rowA 0 0 8 ≤ db_2337 0 0 := by
  have hleft : yW_2337 0 * rowA 0 0 0 + yW_2337 1 * rowA 0 0 1 + yW_2337 2 * rowA 0 0 2 + yW_2337 3 * rowA 0 0 3 + yW_2337 4 * rowA 0 0 4 + yW_2337 5 * rowA 0 0 5 + yW_2337 6 * rowA 0 0 6 + yW_2337 7 * rowA 0 0 7 + yW_2337 8 * rowA 0 0 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 0 0 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_0_1 :
    yW_2337 0 * rowA 0 1 0 + yW_2337 1 * rowA 0 1 1 + yW_2337 2 * rowA 0 1 2 + yW_2337 3 * rowA 0 1 3 + yW_2337 4 * rowA 0 1 4 + yW_2337 5 * rowA 0 1 5 + yW_2337 6 * rowA 0 1 6 + yW_2337 7 * rowA 0 1 7 + yW_2337 8 * rowA 0 1 8 ≤ db_2337 0 1 := by
  have hleft : yW_2337 0 * rowA 0 1 0 + yW_2337 1 * rowA 0 1 1 + yW_2337 2 * rowA 0 1 2 + yW_2337 3 * rowA 0 1 3 + yW_2337 4 * rowA 0 1 4 + yW_2337 5 * rowA 0 1 5 + yW_2337 6 * rowA 0 1 6 + yW_2337 7 * rowA 0 1 7 + yW_2337 8 * rowA 0 1 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 0 1 = (3 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_0_2 :
    yW_2337 0 * rowA 0 2 0 + yW_2337 1 * rowA 0 2 1 + yW_2337 2 * rowA 0 2 2 + yW_2337 3 * rowA 0 2 3 + yW_2337 4 * rowA 0 2 4 + yW_2337 5 * rowA 0 2 5 + yW_2337 6 * rowA 0 2 6 + yW_2337 7 * rowA 0 2 7 + yW_2337 8 * rowA 0 2 8 ≤ db_2337 0 2 := by
  have hleft : yW_2337 0 * rowA 0 2 0 + yW_2337 1 * rowA 0 2 1 + yW_2337 2 * rowA 0 2 2 + yW_2337 3 * rowA 0 2 3 + yW_2337 4 * rowA 0 2 4 + yW_2337 5 * rowA 0 2 5 + yW_2337 6 * rowA 0 2 6 + yW_2337 7 * rowA 0 2 7 + yW_2337 8 * rowA 0 2 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 0 2 = (3 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_0_3 :
    yW_2337 0 * rowA 0 3 0 + yW_2337 1 * rowA 0 3 1 + yW_2337 2 * rowA 0 3 2 + yW_2337 3 * rowA 0 3 3 + yW_2337 4 * rowA 0 3 4 + yW_2337 5 * rowA 0 3 5 + yW_2337 6 * rowA 0 3 6 + yW_2337 7 * rowA 0 3 7 + yW_2337 8 * rowA 0 3 8 ≤ db_2337 0 3 := by
  have hleft : yW_2337 0 * rowA 0 3 0 + yW_2337 1 * rowA 0 3 1 + yW_2337 2 * rowA 0 3 2 + yW_2337 3 * rowA 0 3 3 + yW_2337 4 * rowA 0 3 4 + yW_2337 5 * rowA 0 3 5 + yW_2337 6 * rowA 0 3 6 + yW_2337 7 * rowA 0 3 7 + yW_2337 8 * rowA 0 3 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 0 3 = (3 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_0_4 :
    yW_2337 0 * rowA 0 4 0 + yW_2337 1 * rowA 0 4 1 + yW_2337 2 * rowA 0 4 2 + yW_2337 3 * rowA 0 4 3 + yW_2337 4 * rowA 0 4 4 + yW_2337 5 * rowA 0 4 5 + yW_2337 6 * rowA 0 4 6 + yW_2337 7 * rowA 0 4 7 + yW_2337 8 * rowA 0 4 8 ≤ db_2337 0 4 := by
  have hleft : yW_2337 0 * rowA 0 4 0 + yW_2337 1 * rowA 0 4 1 + yW_2337 2 * rowA 0 4 2 + yW_2337 3 * rowA 0 4 3 + yW_2337 4 * rowA 0 4 4 + yW_2337 5 * rowA 0 4 5 + yW_2337 6 * rowA 0 4 6 + yW_2337 7 * rowA 0 4 7 + yW_2337 8 * rowA 0 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 0 4 = (5 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_0_5 :
    yW_2337 0 * rowA 0 5 0 + yW_2337 1 * rowA 0 5 1 + yW_2337 2 * rowA 0 5 2 + yW_2337 3 * rowA 0 5 3 + yW_2337 4 * rowA 0 5 4 + yW_2337 5 * rowA 0 5 5 + yW_2337 6 * rowA 0 5 6 + yW_2337 7 * rowA 0 5 7 + yW_2337 8 * rowA 0 5 8 ≤ db_2337 0 5 := by
  have hleft : yW_2337 0 * rowA 0 5 0 + yW_2337 1 * rowA 0 5 1 + yW_2337 2 * rowA 0 5 2 + yW_2337 3 * rowA 0 5 3 + yW_2337 4 * rowA 0 5 4 + yW_2337 5 * rowA 0 5 5 + yW_2337 6 * rowA 0 5 6 + yW_2337 7 * rowA 0 5 7 + yW_2337 8 * rowA 0 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 0 5 = (1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_0_6 :
    yW_2337 0 * rowA 0 6 0 + yW_2337 1 * rowA 0 6 1 + yW_2337 2 * rowA 0 6 2 + yW_2337 3 * rowA 0 6 3 + yW_2337 4 * rowA 0 6 4 + yW_2337 5 * rowA 0 6 5 + yW_2337 6 * rowA 0 6 6 + yW_2337 7 * rowA 0 6 7 + yW_2337 8 * rowA 0 6 8 ≤ db_2337 0 6 := by
  have hleft : yW_2337 0 * rowA 0 6 0 + yW_2337 1 * rowA 0 6 1 + yW_2337 2 * rowA 0 6 2 + yW_2337 3 * rowA 0 6 3 + yW_2337 4 * rowA 0 6 4 + yW_2337 5 * rowA 0 6 5 + yW_2337 6 * rowA 0 6 6 + yW_2337 7 * rowA 0 6 7 + yW_2337 8 * rowA 0 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 0 6 = (1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_0_7 :
    yW_2337 0 * rowA 0 7 0 + yW_2337 1 * rowA 0 7 1 + yW_2337 2 * rowA 0 7 2 + yW_2337 3 * rowA 0 7 3 + yW_2337 4 * rowA 0 7 4 + yW_2337 5 * rowA 0 7 5 + yW_2337 6 * rowA 0 7 6 + yW_2337 7 * rowA 0 7 7 + yW_2337 8 * rowA 0 7 8 ≤ db_2337 0 7 := by
  have hleft : yW_2337 0 * rowA 0 7 0 + yW_2337 1 * rowA 0 7 1 + yW_2337 2 * rowA 0 7 2 + yW_2337 3 * rowA 0 7 3 + yW_2337 4 * rowA 0 7 4 + yW_2337 5 * rowA 0 7 5 + yW_2337 6 * rowA 0 7 6 + yW_2337 7 * rowA 0 7 7 + yW_2337 8 * rowA 0 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 0 7 = (11 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_0_8 :
    yW_2337 0 * rowA 0 8 0 + yW_2337 1 * rowA 0 8 1 + yW_2337 2 * rowA 0 8 2 + yW_2337 3 * rowA 0 8 3 + yW_2337 4 * rowA 0 8 4 + yW_2337 5 * rowA 0 8 5 + yW_2337 6 * rowA 0 8 6 + yW_2337 7 * rowA 0 8 7 + yW_2337 8 * rowA 0 8 8 ≤ db_2337 0 8 := by
  have hleft : yW_2337 0 * rowA 0 8 0 + yW_2337 1 * rowA 0 8 1 + yW_2337 2 * rowA 0 8 2 + yW_2337 3 * rowA 0 8 3 + yW_2337 4 * rowA 0 8 4 + yW_2337 5 * rowA 0 8 5 + yW_2337 6 * rowA 0 8 6 + yW_2337 7 * rowA 0 8 7 + yW_2337 8 * rowA 0 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 0 8 = (11 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_0_9 :
    yW_2337 0 * rowA 0 9 0 + yW_2337 1 * rowA 0 9 1 + yW_2337 2 * rowA 0 9 2 + yW_2337 3 * rowA 0 9 3 + yW_2337 4 * rowA 0 9 4 + yW_2337 5 * rowA 0 9 5 + yW_2337 6 * rowA 0 9 6 + yW_2337 7 * rowA 0 9 7 + yW_2337 8 * rowA 0 9 8 ≤ db_2337 0 9 := by
  have hleft : yW_2337 0 * rowA 0 9 0 + yW_2337 1 * rowA 0 9 1 + yW_2337 2 * rowA 0 9 2 + yW_2337 3 * rowA 0 9 3 + yW_2337 4 * rowA 0 9 4 + yW_2337 5 * rowA 0 9 5 + yW_2337 6 * rowA 0 9 6 + yW_2337 7 * rowA 0 9 7 + yW_2337 8 * rowA 0 9 8 = (1 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 0 9 = (1 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_1_0 :
    yW_2337 0 * rowA 1 0 0 + yW_2337 1 * rowA 1 0 1 + yW_2337 2 * rowA 1 0 2 + yW_2337 3 * rowA 1 0 3 + yW_2337 4 * rowA 1 0 4 + yW_2337 5 * rowA 1 0 5 + yW_2337 6 * rowA 1 0 6 + yW_2337 7 * rowA 1 0 7 + yW_2337 8 * rowA 1 0 8 ≤ db_2337 1 0 := by
  have hleft : yW_2337 0 * rowA 1 0 0 + yW_2337 1 * rowA 1 0 1 + yW_2337 2 * rowA 1 0 2 + yW_2337 3 * rowA 1 0 3 + yW_2337 4 * rowA 1 0 4 + yW_2337 5 * rowA 1 0 5 + yW_2337 6 * rowA 1 0 6 + yW_2337 7 * rowA 1 0 7 + yW_2337 8 * rowA 1 0 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 1 0 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_1_1 :
    yW_2337 0 * rowA 1 1 0 + yW_2337 1 * rowA 1 1 1 + yW_2337 2 * rowA 1 1 2 + yW_2337 3 * rowA 1 1 3 + yW_2337 4 * rowA 1 1 4 + yW_2337 5 * rowA 1 1 5 + yW_2337 6 * rowA 1 1 6 + yW_2337 7 * rowA 1 1 7 + yW_2337 8 * rowA 1 1 8 ≤ db_2337 1 1 := by
  have hleft : yW_2337 0 * rowA 1 1 0 + yW_2337 1 * rowA 1 1 1 + yW_2337 2 * rowA 1 1 2 + yW_2337 3 * rowA 1 1 3 + yW_2337 4 * rowA 1 1 4 + yW_2337 5 * rowA 1 1 5 + yW_2337 6 * rowA 1 1 6 + yW_2337 7 * rowA 1 1 7 + yW_2337 8 * rowA 1 1 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 1 1 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_1_2 :
    yW_2337 0 * rowA 1 2 0 + yW_2337 1 * rowA 1 2 1 + yW_2337 2 * rowA 1 2 2 + yW_2337 3 * rowA 1 2 3 + yW_2337 4 * rowA 1 2 4 + yW_2337 5 * rowA 1 2 5 + yW_2337 6 * rowA 1 2 6 + yW_2337 7 * rowA 1 2 7 + yW_2337 8 * rowA 1 2 8 ≤ db_2337 1 2 := by
  have hleft : yW_2337 0 * rowA 1 2 0 + yW_2337 1 * rowA 1 2 1 + yW_2337 2 * rowA 1 2 2 + yW_2337 3 * rowA 1 2 3 + yW_2337 4 * rowA 1 2 4 + yW_2337 5 * rowA 1 2 5 + yW_2337 6 * rowA 1 2 6 + yW_2337 7 * rowA 1 2 7 + yW_2337 8 * rowA 1 2 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 1 2 = (3 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_1_3 :
    yW_2337 0 * rowA 1 3 0 + yW_2337 1 * rowA 1 3 1 + yW_2337 2 * rowA 1 3 2 + yW_2337 3 * rowA 1 3 3 + yW_2337 4 * rowA 1 3 4 + yW_2337 5 * rowA 1 3 5 + yW_2337 6 * rowA 1 3 6 + yW_2337 7 * rowA 1 3 7 + yW_2337 8 * rowA 1 3 8 ≤ db_2337 1 3 := by
  have hleft : yW_2337 0 * rowA 1 3 0 + yW_2337 1 * rowA 1 3 1 + yW_2337 2 * rowA 1 3 2 + yW_2337 3 * rowA 1 3 3 + yW_2337 4 * rowA 1 3 4 + yW_2337 5 * rowA 1 3 5 + yW_2337 6 * rowA 1 3 6 + yW_2337 7 * rowA 1 3 7 + yW_2337 8 * rowA 1 3 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 1 3 = (3 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_1_4 :
    yW_2337 0 * rowA 1 4 0 + yW_2337 1 * rowA 1 4 1 + yW_2337 2 * rowA 1 4 2 + yW_2337 3 * rowA 1 4 3 + yW_2337 4 * rowA 1 4 4 + yW_2337 5 * rowA 1 4 5 + yW_2337 6 * rowA 1 4 6 + yW_2337 7 * rowA 1 4 7 + yW_2337 8 * rowA 1 4 8 ≤ db_2337 1 4 := by
  have hleft : yW_2337 0 * rowA 1 4 0 + yW_2337 1 * rowA 1 4 1 + yW_2337 2 * rowA 1 4 2 + yW_2337 3 * rowA 1 4 3 + yW_2337 4 * rowA 1 4 4 + yW_2337 5 * rowA 1 4 5 + yW_2337 6 * rowA 1 4 6 + yW_2337 7 * rowA 1 4 7 + yW_2337 8 * rowA 1 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 1 4 = (5 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_1_5 :
    yW_2337 0 * rowA 1 5 0 + yW_2337 1 * rowA 1 5 1 + yW_2337 2 * rowA 1 5 2 + yW_2337 3 * rowA 1 5 3 + yW_2337 4 * rowA 1 5 4 + yW_2337 5 * rowA 1 5 5 + yW_2337 6 * rowA 1 5 6 + yW_2337 7 * rowA 1 5 7 + yW_2337 8 * rowA 1 5 8 ≤ db_2337 1 5 := by
  have hleft : yW_2337 0 * rowA 1 5 0 + yW_2337 1 * rowA 1 5 1 + yW_2337 2 * rowA 1 5 2 + yW_2337 3 * rowA 1 5 3 + yW_2337 4 * rowA 1 5 4 + yW_2337 5 * rowA 1 5 5 + yW_2337 6 * rowA 1 5 6 + yW_2337 7 * rowA 1 5 7 + yW_2337 8 * rowA 1 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 1 5 = (1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_1_6 :
    yW_2337 0 * rowA 1 6 0 + yW_2337 1 * rowA 1 6 1 + yW_2337 2 * rowA 1 6 2 + yW_2337 3 * rowA 1 6 3 + yW_2337 4 * rowA 1 6 4 + yW_2337 5 * rowA 1 6 5 + yW_2337 6 * rowA 1 6 6 + yW_2337 7 * rowA 1 6 7 + yW_2337 8 * rowA 1 6 8 ≤ db_2337 1 6 := by
  have hleft : yW_2337 0 * rowA 1 6 0 + yW_2337 1 * rowA 1 6 1 + yW_2337 2 * rowA 1 6 2 + yW_2337 3 * rowA 1 6 3 + yW_2337 4 * rowA 1 6 4 + yW_2337 5 * rowA 1 6 5 + yW_2337 6 * rowA 1 6 6 + yW_2337 7 * rowA 1 6 7 + yW_2337 8 * rowA 1 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 1 6 = (1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_1_7 :
    yW_2337 0 * rowA 1 7 0 + yW_2337 1 * rowA 1 7 1 + yW_2337 2 * rowA 1 7 2 + yW_2337 3 * rowA 1 7 3 + yW_2337 4 * rowA 1 7 4 + yW_2337 5 * rowA 1 7 5 + yW_2337 6 * rowA 1 7 6 + yW_2337 7 * rowA 1 7 7 + yW_2337 8 * rowA 1 7 8 ≤ db_2337 1 7 := by
  have hleft : yW_2337 0 * rowA 1 7 0 + yW_2337 1 * rowA 1 7 1 + yW_2337 2 * rowA 1 7 2 + yW_2337 3 * rowA 1 7 3 + yW_2337 4 * rowA 1 7 4 + yW_2337 5 * rowA 1 7 5 + yW_2337 6 * rowA 1 7 6 + yW_2337 7 * rowA 1 7 7 + yW_2337 8 * rowA 1 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 1 7 = (11 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_1_8 :
    yW_2337 0 * rowA 1 8 0 + yW_2337 1 * rowA 1 8 1 + yW_2337 2 * rowA 1 8 2 + yW_2337 3 * rowA 1 8 3 + yW_2337 4 * rowA 1 8 4 + yW_2337 5 * rowA 1 8 5 + yW_2337 6 * rowA 1 8 6 + yW_2337 7 * rowA 1 8 7 + yW_2337 8 * rowA 1 8 8 ≤ db_2337 1 8 := by
  have hleft : yW_2337 0 * rowA 1 8 0 + yW_2337 1 * rowA 1 8 1 + yW_2337 2 * rowA 1 8 2 + yW_2337 3 * rowA 1 8 3 + yW_2337 4 * rowA 1 8 4 + yW_2337 5 * rowA 1 8 5 + yW_2337 6 * rowA 1 8 6 + yW_2337 7 * rowA 1 8 7 + yW_2337 8 * rowA 1 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 1 8 = (11 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_1_9 :
    yW_2337 0 * rowA 1 9 0 + yW_2337 1 * rowA 1 9 1 + yW_2337 2 * rowA 1 9 2 + yW_2337 3 * rowA 1 9 3 + yW_2337 4 * rowA 1 9 4 + yW_2337 5 * rowA 1 9 5 + yW_2337 6 * rowA 1 9 6 + yW_2337 7 * rowA 1 9 7 + yW_2337 8 * rowA 1 9 8 ≤ db_2337 1 9 := by
  have hleft : yW_2337 0 * rowA 1 9 0 + yW_2337 1 * rowA 1 9 1 + yW_2337 2 * rowA 1 9 2 + yW_2337 3 * rowA 1 9 3 + yW_2337 4 * rowA 1 9 4 + yW_2337 5 * rowA 1 9 5 + yW_2337 6 * rowA 1 9 6 + yW_2337 7 * rowA 1 9 7 + yW_2337 8 * rowA 1 9 8 = (1 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 1 9 = (1 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_2_0 :
    yW_2337 0 * rowA 2 0 0 + yW_2337 1 * rowA 2 0 1 + yW_2337 2 * rowA 2 0 2 + yW_2337 3 * rowA 2 0 3 + yW_2337 4 * rowA 2 0 4 + yW_2337 5 * rowA 2 0 5 + yW_2337 6 * rowA 2 0 6 + yW_2337 7 * rowA 2 0 7 + yW_2337 8 * rowA 2 0 8 ≤ db_2337 2 0 := by
  have hleft : yW_2337 0 * rowA 2 0 0 + yW_2337 1 * rowA 2 0 1 + yW_2337 2 * rowA 2 0 2 + yW_2337 3 * rowA 2 0 3 + yW_2337 4 * rowA 2 0 4 + yW_2337 5 * rowA 2 0 5 + yW_2337 6 * rowA 2 0 6 + yW_2337 7 * rowA 2 0 7 + yW_2337 8 * rowA 2 0 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 2 0 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_2_1 :
    yW_2337 0 * rowA 2 1 0 + yW_2337 1 * rowA 2 1 1 + yW_2337 2 * rowA 2 1 2 + yW_2337 3 * rowA 2 1 3 + yW_2337 4 * rowA 2 1 4 + yW_2337 5 * rowA 2 1 5 + yW_2337 6 * rowA 2 1 6 + yW_2337 7 * rowA 2 1 7 + yW_2337 8 * rowA 2 1 8 ≤ db_2337 2 1 := by
  have hleft : yW_2337 0 * rowA 2 1 0 + yW_2337 1 * rowA 2 1 1 + yW_2337 2 * rowA 2 1 2 + yW_2337 3 * rowA 2 1 3 + yW_2337 4 * rowA 2 1 4 + yW_2337 5 * rowA 2 1 5 + yW_2337 6 * rowA 2 1 6 + yW_2337 7 * rowA 2 1 7 + yW_2337 8 * rowA 2 1 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 2 1 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_2_2 :
    yW_2337 0 * rowA 2 2 0 + yW_2337 1 * rowA 2 2 1 + yW_2337 2 * rowA 2 2 2 + yW_2337 3 * rowA 2 2 3 + yW_2337 4 * rowA 2 2 4 + yW_2337 5 * rowA 2 2 5 + yW_2337 6 * rowA 2 2 6 + yW_2337 7 * rowA 2 2 7 + yW_2337 8 * rowA 2 2 8 ≤ db_2337 2 2 := by
  have hleft : yW_2337 0 * rowA 2 2 0 + yW_2337 1 * rowA 2 2 1 + yW_2337 2 * rowA 2 2 2 + yW_2337 3 * rowA 2 2 3 + yW_2337 4 * rowA 2 2 4 + yW_2337 5 * rowA 2 2 5 + yW_2337 6 * rowA 2 2 6 + yW_2337 7 * rowA 2 2 7 + yW_2337 8 * rowA 2 2 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 2 2 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_2_3 :
    yW_2337 0 * rowA 2 3 0 + yW_2337 1 * rowA 2 3 1 + yW_2337 2 * rowA 2 3 2 + yW_2337 3 * rowA 2 3 3 + yW_2337 4 * rowA 2 3 4 + yW_2337 5 * rowA 2 3 5 + yW_2337 6 * rowA 2 3 6 + yW_2337 7 * rowA 2 3 7 + yW_2337 8 * rowA 2 3 8 ≤ db_2337 2 3 := by
  have hleft : yW_2337 0 * rowA 2 3 0 + yW_2337 1 * rowA 2 3 1 + yW_2337 2 * rowA 2 3 2 + yW_2337 3 * rowA 2 3 3 + yW_2337 4 * rowA 2 3 4 + yW_2337 5 * rowA 2 3 5 + yW_2337 6 * rowA 2 3 6 + yW_2337 7 * rowA 2 3 7 + yW_2337 8 * rowA 2 3 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 2 3 = (3 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_2_4 :
    yW_2337 0 * rowA 2 4 0 + yW_2337 1 * rowA 2 4 1 + yW_2337 2 * rowA 2 4 2 + yW_2337 3 * rowA 2 4 3 + yW_2337 4 * rowA 2 4 4 + yW_2337 5 * rowA 2 4 5 + yW_2337 6 * rowA 2 4 6 + yW_2337 7 * rowA 2 4 7 + yW_2337 8 * rowA 2 4 8 ≤ db_2337 2 4 := by
  have hleft : yW_2337 0 * rowA 2 4 0 + yW_2337 1 * rowA 2 4 1 + yW_2337 2 * rowA 2 4 2 + yW_2337 3 * rowA 2 4 3 + yW_2337 4 * rowA 2 4 4 + yW_2337 5 * rowA 2 4 5 + yW_2337 6 * rowA 2 4 6 + yW_2337 7 * rowA 2 4 7 + yW_2337 8 * rowA 2 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 2 4 = (5 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_2_5 :
    yW_2337 0 * rowA 2 5 0 + yW_2337 1 * rowA 2 5 1 + yW_2337 2 * rowA 2 5 2 + yW_2337 3 * rowA 2 5 3 + yW_2337 4 * rowA 2 5 4 + yW_2337 5 * rowA 2 5 5 + yW_2337 6 * rowA 2 5 6 + yW_2337 7 * rowA 2 5 7 + yW_2337 8 * rowA 2 5 8 ≤ db_2337 2 5 := by
  have hleft : yW_2337 0 * rowA 2 5 0 + yW_2337 1 * rowA 2 5 1 + yW_2337 2 * rowA 2 5 2 + yW_2337 3 * rowA 2 5 3 + yW_2337 4 * rowA 2 5 4 + yW_2337 5 * rowA 2 5 5 + yW_2337 6 * rowA 2 5 6 + yW_2337 7 * rowA 2 5 7 + yW_2337 8 * rowA 2 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 2 5 = (1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_2_6 :
    yW_2337 0 * rowA 2 6 0 + yW_2337 1 * rowA 2 6 1 + yW_2337 2 * rowA 2 6 2 + yW_2337 3 * rowA 2 6 3 + yW_2337 4 * rowA 2 6 4 + yW_2337 5 * rowA 2 6 5 + yW_2337 6 * rowA 2 6 6 + yW_2337 7 * rowA 2 6 7 + yW_2337 8 * rowA 2 6 8 ≤ db_2337 2 6 := by
  have hleft : yW_2337 0 * rowA 2 6 0 + yW_2337 1 * rowA 2 6 1 + yW_2337 2 * rowA 2 6 2 + yW_2337 3 * rowA 2 6 3 + yW_2337 4 * rowA 2 6 4 + yW_2337 5 * rowA 2 6 5 + yW_2337 6 * rowA 2 6 6 + yW_2337 7 * rowA 2 6 7 + yW_2337 8 * rowA 2 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 2 6 = (1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_2_7 :
    yW_2337 0 * rowA 2 7 0 + yW_2337 1 * rowA 2 7 1 + yW_2337 2 * rowA 2 7 2 + yW_2337 3 * rowA 2 7 3 + yW_2337 4 * rowA 2 7 4 + yW_2337 5 * rowA 2 7 5 + yW_2337 6 * rowA 2 7 6 + yW_2337 7 * rowA 2 7 7 + yW_2337 8 * rowA 2 7 8 ≤ db_2337 2 7 := by
  have hleft : yW_2337 0 * rowA 2 7 0 + yW_2337 1 * rowA 2 7 1 + yW_2337 2 * rowA 2 7 2 + yW_2337 3 * rowA 2 7 3 + yW_2337 4 * rowA 2 7 4 + yW_2337 5 * rowA 2 7 5 + yW_2337 6 * rowA 2 7 6 + yW_2337 7 * rowA 2 7 7 + yW_2337 8 * rowA 2 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 2 7 = (11 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_2_8 :
    yW_2337 0 * rowA 2 8 0 + yW_2337 1 * rowA 2 8 1 + yW_2337 2 * rowA 2 8 2 + yW_2337 3 * rowA 2 8 3 + yW_2337 4 * rowA 2 8 4 + yW_2337 5 * rowA 2 8 5 + yW_2337 6 * rowA 2 8 6 + yW_2337 7 * rowA 2 8 7 + yW_2337 8 * rowA 2 8 8 ≤ db_2337 2 8 := by
  have hleft : yW_2337 0 * rowA 2 8 0 + yW_2337 1 * rowA 2 8 1 + yW_2337 2 * rowA 2 8 2 + yW_2337 3 * rowA 2 8 3 + yW_2337 4 * rowA 2 8 4 + yW_2337 5 * rowA 2 8 5 + yW_2337 6 * rowA 2 8 6 + yW_2337 7 * rowA 2 8 7 + yW_2337 8 * rowA 2 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 2 8 = (11 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_2_9 :
    yW_2337 0 * rowA 2 9 0 + yW_2337 1 * rowA 2 9 1 + yW_2337 2 * rowA 2 9 2 + yW_2337 3 * rowA 2 9 3 + yW_2337 4 * rowA 2 9 4 + yW_2337 5 * rowA 2 9 5 + yW_2337 6 * rowA 2 9 6 + yW_2337 7 * rowA 2 9 7 + yW_2337 8 * rowA 2 9 8 ≤ db_2337 2 9 := by
  have hleft : yW_2337 0 * rowA 2 9 0 + yW_2337 1 * rowA 2 9 1 + yW_2337 2 * rowA 2 9 2 + yW_2337 3 * rowA 2 9 3 + yW_2337 4 * rowA 2 9 4 + yW_2337 5 * rowA 2 9 5 + yW_2337 6 * rowA 2 9 6 + yW_2337 7 * rowA 2 9 7 + yW_2337 8 * rowA 2 9 8 = (1 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 2 9 = (1 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_3_0 :
    yW_2337 0 * rowA 3 0 0 + yW_2337 1 * rowA 3 0 1 + yW_2337 2 * rowA 3 0 2 + yW_2337 3 * rowA 3 0 3 + yW_2337 4 * rowA 3 0 4 + yW_2337 5 * rowA 3 0 5 + yW_2337 6 * rowA 3 0 6 + yW_2337 7 * rowA 3 0 7 + yW_2337 8 * rowA 3 0 8 ≤ db_2337 3 0 := by
  have hleft : yW_2337 0 * rowA 3 0 0 + yW_2337 1 * rowA 3 0 1 + yW_2337 2 * rowA 3 0 2 + yW_2337 3 * rowA 3 0 3 + yW_2337 4 * rowA 3 0 4 + yW_2337 5 * rowA 3 0 5 + yW_2337 6 * rowA 3 0 6 + yW_2337 7 * rowA 3 0 7 + yW_2337 8 * rowA 3 0 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 3 0 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_3_1 :
    yW_2337 0 * rowA 3 1 0 + yW_2337 1 * rowA 3 1 1 + yW_2337 2 * rowA 3 1 2 + yW_2337 3 * rowA 3 1 3 + yW_2337 4 * rowA 3 1 4 + yW_2337 5 * rowA 3 1 5 + yW_2337 6 * rowA 3 1 6 + yW_2337 7 * rowA 3 1 7 + yW_2337 8 * rowA 3 1 8 ≤ db_2337 3 1 := by
  have hleft : yW_2337 0 * rowA 3 1 0 + yW_2337 1 * rowA 3 1 1 + yW_2337 2 * rowA 3 1 2 + yW_2337 3 * rowA 3 1 3 + yW_2337 4 * rowA 3 1 4 + yW_2337 5 * rowA 3 1 5 + yW_2337 6 * rowA 3 1 6 + yW_2337 7 * rowA 3 1 7 + yW_2337 8 * rowA 3 1 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 3 1 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_3_2 :
    yW_2337 0 * rowA 3 2 0 + yW_2337 1 * rowA 3 2 1 + yW_2337 2 * rowA 3 2 2 + yW_2337 3 * rowA 3 2 3 + yW_2337 4 * rowA 3 2 4 + yW_2337 5 * rowA 3 2 5 + yW_2337 6 * rowA 3 2 6 + yW_2337 7 * rowA 3 2 7 + yW_2337 8 * rowA 3 2 8 ≤ db_2337 3 2 := by
  have hleft : yW_2337 0 * rowA 3 2 0 + yW_2337 1 * rowA 3 2 1 + yW_2337 2 * rowA 3 2 2 + yW_2337 3 * rowA 3 2 3 + yW_2337 4 * rowA 3 2 4 + yW_2337 5 * rowA 3 2 5 + yW_2337 6 * rowA 3 2 6 + yW_2337 7 * rowA 3 2 7 + yW_2337 8 * rowA 3 2 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 3 2 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_3_3 :
    yW_2337 0 * rowA 3 3 0 + yW_2337 1 * rowA 3 3 1 + yW_2337 2 * rowA 3 3 2 + yW_2337 3 * rowA 3 3 3 + yW_2337 4 * rowA 3 3 4 + yW_2337 5 * rowA 3 3 5 + yW_2337 6 * rowA 3 3 6 + yW_2337 7 * rowA 3 3 7 + yW_2337 8 * rowA 3 3 8 ≤ db_2337 3 3 := by
  have hleft : yW_2337 0 * rowA 3 3 0 + yW_2337 1 * rowA 3 3 1 + yW_2337 2 * rowA 3 3 2 + yW_2337 3 * rowA 3 3 3 + yW_2337 4 * rowA 3 3 4 + yW_2337 5 * rowA 3 3 5 + yW_2337 6 * rowA 3 3 6 + yW_2337 7 * rowA 3 3 7 + yW_2337 8 * rowA 3 3 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 3 3 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_3_4 :
    yW_2337 0 * rowA 3 4 0 + yW_2337 1 * rowA 3 4 1 + yW_2337 2 * rowA 3 4 2 + yW_2337 3 * rowA 3 4 3 + yW_2337 4 * rowA 3 4 4 + yW_2337 5 * rowA 3 4 5 + yW_2337 6 * rowA 3 4 6 + yW_2337 7 * rowA 3 4 7 + yW_2337 8 * rowA 3 4 8 ≤ db_2337 3 4 := by
  have hleft : yW_2337 0 * rowA 3 4 0 + yW_2337 1 * rowA 3 4 1 + yW_2337 2 * rowA 3 4 2 + yW_2337 3 * rowA 3 4 3 + yW_2337 4 * rowA 3 4 4 + yW_2337 5 * rowA 3 4 5 + yW_2337 6 * rowA 3 4 6 + yW_2337 7 * rowA 3 4 7 + yW_2337 8 * rowA 3 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 3 4 = (5 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_3_5 :
    yW_2337 0 * rowA 3 5 0 + yW_2337 1 * rowA 3 5 1 + yW_2337 2 * rowA 3 5 2 + yW_2337 3 * rowA 3 5 3 + yW_2337 4 * rowA 3 5 4 + yW_2337 5 * rowA 3 5 5 + yW_2337 6 * rowA 3 5 6 + yW_2337 7 * rowA 3 5 7 + yW_2337 8 * rowA 3 5 8 ≤ db_2337 3 5 := by
  have hleft : yW_2337 0 * rowA 3 5 0 + yW_2337 1 * rowA 3 5 1 + yW_2337 2 * rowA 3 5 2 + yW_2337 3 * rowA 3 5 3 + yW_2337 4 * rowA 3 5 4 + yW_2337 5 * rowA 3 5 5 + yW_2337 6 * rowA 3 5 6 + yW_2337 7 * rowA 3 5 7 + yW_2337 8 * rowA 3 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 3 5 = (1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_3_6 :
    yW_2337 0 * rowA 3 6 0 + yW_2337 1 * rowA 3 6 1 + yW_2337 2 * rowA 3 6 2 + yW_2337 3 * rowA 3 6 3 + yW_2337 4 * rowA 3 6 4 + yW_2337 5 * rowA 3 6 5 + yW_2337 6 * rowA 3 6 6 + yW_2337 7 * rowA 3 6 7 + yW_2337 8 * rowA 3 6 8 ≤ db_2337 3 6 := by
  have hleft : yW_2337 0 * rowA 3 6 0 + yW_2337 1 * rowA 3 6 1 + yW_2337 2 * rowA 3 6 2 + yW_2337 3 * rowA 3 6 3 + yW_2337 4 * rowA 3 6 4 + yW_2337 5 * rowA 3 6 5 + yW_2337 6 * rowA 3 6 6 + yW_2337 7 * rowA 3 6 7 + yW_2337 8 * rowA 3 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 3 6 = (1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_3_7 :
    yW_2337 0 * rowA 3 7 0 + yW_2337 1 * rowA 3 7 1 + yW_2337 2 * rowA 3 7 2 + yW_2337 3 * rowA 3 7 3 + yW_2337 4 * rowA 3 7 4 + yW_2337 5 * rowA 3 7 5 + yW_2337 6 * rowA 3 7 6 + yW_2337 7 * rowA 3 7 7 + yW_2337 8 * rowA 3 7 8 ≤ db_2337 3 7 := by
  have hleft : yW_2337 0 * rowA 3 7 0 + yW_2337 1 * rowA 3 7 1 + yW_2337 2 * rowA 3 7 2 + yW_2337 3 * rowA 3 7 3 + yW_2337 4 * rowA 3 7 4 + yW_2337 5 * rowA 3 7 5 + yW_2337 6 * rowA 3 7 6 + yW_2337 7 * rowA 3 7 7 + yW_2337 8 * rowA 3 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 3 7 = (5 : ℚ) / 8 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_3_8 :
    yW_2337 0 * rowA 3 8 0 + yW_2337 1 * rowA 3 8 1 + yW_2337 2 * rowA 3 8 2 + yW_2337 3 * rowA 3 8 3 + yW_2337 4 * rowA 3 8 4 + yW_2337 5 * rowA 3 8 5 + yW_2337 6 * rowA 3 8 6 + yW_2337 7 * rowA 3 8 7 + yW_2337 8 * rowA 3 8 8 ≤ db_2337 3 8 := by
  have hleft : yW_2337 0 * rowA 3 8 0 + yW_2337 1 * rowA 3 8 1 + yW_2337 2 * rowA 3 8 2 + yW_2337 3 * rowA 3 8 3 + yW_2337 4 * rowA 3 8 4 + yW_2337 5 * rowA 3 8 5 + yW_2337 6 * rowA 3 8 6 + yW_2337 7 * rowA 3 8 7 + yW_2337 8 * rowA 3 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 3 8 = (5 : ℚ) / 8 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_3_9 :
    yW_2337 0 * rowA 3 9 0 + yW_2337 1 * rowA 3 9 1 + yW_2337 2 * rowA 3 9 2 + yW_2337 3 * rowA 3 9 3 + yW_2337 4 * rowA 3 9 4 + yW_2337 5 * rowA 3 9 5 + yW_2337 6 * rowA 3 9 6 + yW_2337 7 * rowA 3 9 7 + yW_2337 8 * rowA 3 9 8 ≤ db_2337 3 9 := by
  have hleft : yW_2337 0 * rowA 3 9 0 + yW_2337 1 * rowA 3 9 1 + yW_2337 2 * rowA 3 9 2 + yW_2337 3 * rowA 3 9 3 + yW_2337 4 * rowA 3 9 4 + yW_2337 5 * rowA 3 9 5 + yW_2337 6 * rowA 3 9 6 + yW_2337 7 * rowA 3 9 7 + yW_2337 8 * rowA 3 9 8 = (1 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 3 9 = (1 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_4_0 :
    yW_2337 0 * rowA 4 0 0 + yW_2337 1 * rowA 4 0 1 + yW_2337 2 * rowA 4 0 2 + yW_2337 3 * rowA 4 0 3 + yW_2337 4 * rowA 4 0 4 + yW_2337 5 * rowA 4 0 5 + yW_2337 6 * rowA 4 0 6 + yW_2337 7 * rowA 4 0 7 + yW_2337 8 * rowA 4 0 8 ≤ db_2337 4 0 := by
  have hleft : yW_2337 0 * rowA 4 0 0 + yW_2337 1 * rowA 4 0 1 + yW_2337 2 * rowA 4 0 2 + yW_2337 3 * rowA 4 0 3 + yW_2337 4 * rowA 4 0 4 + yW_2337 5 * rowA 4 0 5 + yW_2337 6 * rowA 4 0 6 + yW_2337 7 * rowA 4 0 7 + yW_2337 8 * rowA 4 0 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 4 0 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_4_1 :
    yW_2337 0 * rowA 4 1 0 + yW_2337 1 * rowA 4 1 1 + yW_2337 2 * rowA 4 1 2 + yW_2337 3 * rowA 4 1 3 + yW_2337 4 * rowA 4 1 4 + yW_2337 5 * rowA 4 1 5 + yW_2337 6 * rowA 4 1 6 + yW_2337 7 * rowA 4 1 7 + yW_2337 8 * rowA 4 1 8 ≤ db_2337 4 1 := by
  have hleft : yW_2337 0 * rowA 4 1 0 + yW_2337 1 * rowA 4 1 1 + yW_2337 2 * rowA 4 1 2 + yW_2337 3 * rowA 4 1 3 + yW_2337 4 * rowA 4 1 4 + yW_2337 5 * rowA 4 1 5 + yW_2337 6 * rowA 4 1 6 + yW_2337 7 * rowA 4 1 7 + yW_2337 8 * rowA 4 1 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 4 1 = (-1 : ℚ) / 8 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_4_2 :
    yW_2337 0 * rowA 4 2 0 + yW_2337 1 * rowA 4 2 1 + yW_2337 2 * rowA 4 2 2 + yW_2337 3 * rowA 4 2 3 + yW_2337 4 * rowA 4 2 4 + yW_2337 5 * rowA 4 2 5 + yW_2337 6 * rowA 4 2 6 + yW_2337 7 * rowA 4 2 7 + yW_2337 8 * rowA 4 2 8 ≤ db_2337 4 2 := by
  have hleft : yW_2337 0 * rowA 4 2 0 + yW_2337 1 * rowA 4 2 1 + yW_2337 2 * rowA 4 2 2 + yW_2337 3 * rowA 4 2 3 + yW_2337 4 * rowA 4 2 4 + yW_2337 5 * rowA 4 2 5 + yW_2337 6 * rowA 4 2 6 + yW_2337 7 * rowA 4 2 7 + yW_2337 8 * rowA 4 2 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 4 2 = (-1 : ℚ) / 8 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_4_3 :
    yW_2337 0 * rowA 4 3 0 + yW_2337 1 * rowA 4 3 1 + yW_2337 2 * rowA 4 3 2 + yW_2337 3 * rowA 4 3 3 + yW_2337 4 * rowA 4 3 4 + yW_2337 5 * rowA 4 3 5 + yW_2337 6 * rowA 4 3 6 + yW_2337 7 * rowA 4 3 7 + yW_2337 8 * rowA 4 3 8 ≤ db_2337 4 3 := by
  have hleft : yW_2337 0 * rowA 4 3 0 + yW_2337 1 * rowA 4 3 1 + yW_2337 2 * rowA 4 3 2 + yW_2337 3 * rowA 4 3 3 + yW_2337 4 * rowA 4 3 4 + yW_2337 5 * rowA 4 3 5 + yW_2337 6 * rowA 4 3 6 + yW_2337 7 * rowA 4 3 7 + yW_2337 8 * rowA 4 3 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 4 3 = (-1 : ℚ) / 8 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_4_4 :
    yW_2337 0 * rowA 4 4 0 + yW_2337 1 * rowA 4 4 1 + yW_2337 2 * rowA 4 4 2 + yW_2337 3 * rowA 4 4 3 + yW_2337 4 * rowA 4 4 4 + yW_2337 5 * rowA 4 4 5 + yW_2337 6 * rowA 4 4 6 + yW_2337 7 * rowA 4 4 7 + yW_2337 8 * rowA 4 4 8 ≤ db_2337 4 4 := by
  have hleft : yW_2337 0 * rowA 4 4 0 + yW_2337 1 * rowA 4 4 1 + yW_2337 2 * rowA 4 4 2 + yW_2337 3 * rowA 4 4 3 + yW_2337 4 * rowA 4 4 4 + yW_2337 5 * rowA 4 4 5 + yW_2337 6 * rowA 4 4 6 + yW_2337 7 * rowA 4 4 7 + yW_2337 8 * rowA 4 4 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 4 4 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_4_5 :
    yW_2337 0 * rowA 4 5 0 + yW_2337 1 * rowA 4 5 1 + yW_2337 2 * rowA 4 5 2 + yW_2337 3 * rowA 4 5 3 + yW_2337 4 * rowA 4 5 4 + yW_2337 5 * rowA 4 5 5 + yW_2337 6 * rowA 4 5 6 + yW_2337 7 * rowA 4 5 7 + yW_2337 8 * rowA 4 5 8 ≤ db_2337 4 5 := by
  have hleft : yW_2337 0 * rowA 4 5 0 + yW_2337 1 * rowA 4 5 1 + yW_2337 2 * rowA 4 5 2 + yW_2337 3 * rowA 4 5 3 + yW_2337 4 * rowA 4 5 4 + yW_2337 5 * rowA 4 5 5 + yW_2337 6 * rowA 4 5 6 + yW_2337 7 * rowA 4 5 7 + yW_2337 8 * rowA 4 5 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 4 5 = (1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_4_6 :
    yW_2337 0 * rowA 4 6 0 + yW_2337 1 * rowA 4 6 1 + yW_2337 2 * rowA 4 6 2 + yW_2337 3 * rowA 4 6 3 + yW_2337 4 * rowA 4 6 4 + yW_2337 5 * rowA 4 6 5 + yW_2337 6 * rowA 4 6 6 + yW_2337 7 * rowA 4 6 7 + yW_2337 8 * rowA 4 6 8 ≤ db_2337 4 6 := by
  have hleft : yW_2337 0 * rowA 4 6 0 + yW_2337 1 * rowA 4 6 1 + yW_2337 2 * rowA 4 6 2 + yW_2337 3 * rowA 4 6 3 + yW_2337 4 * rowA 4 6 4 + yW_2337 5 * rowA 4 6 5 + yW_2337 6 * rowA 4 6 6 + yW_2337 7 * rowA 4 6 7 + yW_2337 8 * rowA 4 6 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 4 6 = (1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_4_7 :
    yW_2337 0 * rowA 4 7 0 + yW_2337 1 * rowA 4 7 1 + yW_2337 2 * rowA 4 7 2 + yW_2337 3 * rowA 4 7 3 + yW_2337 4 * rowA 4 7 4 + yW_2337 5 * rowA 4 7 5 + yW_2337 6 * rowA 4 7 6 + yW_2337 7 * rowA 4 7 7 + yW_2337 8 * rowA 4 7 8 ≤ db_2337 4 7 := by
  have hleft : yW_2337 0 * rowA 4 7 0 + yW_2337 1 * rowA 4 7 1 + yW_2337 2 * rowA 4 7 2 + yW_2337 3 * rowA 4 7 3 + yW_2337 4 * rowA 4 7 4 + yW_2337 5 * rowA 4 7 5 + yW_2337 6 * rowA 4 7 6 + yW_2337 7 * rowA 4 7 7 + yW_2337 8 * rowA 4 7 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 4 7 = (3 : ℚ) / 8 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_4_8 :
    yW_2337 0 * rowA 4 8 0 + yW_2337 1 * rowA 4 8 1 + yW_2337 2 * rowA 4 8 2 + yW_2337 3 * rowA 4 8 3 + yW_2337 4 * rowA 4 8 4 + yW_2337 5 * rowA 4 8 5 + yW_2337 6 * rowA 4 8 6 + yW_2337 7 * rowA 4 8 7 + yW_2337 8 * rowA 4 8 8 ≤ db_2337 4 8 := by
  have hleft : yW_2337 0 * rowA 4 8 0 + yW_2337 1 * rowA 4 8 1 + yW_2337 2 * rowA 4 8 2 + yW_2337 3 * rowA 4 8 3 + yW_2337 4 * rowA 4 8 4 + yW_2337 5 * rowA 4 8 5 + yW_2337 6 * rowA 4 8 6 + yW_2337 7 * rowA 4 8 7 + yW_2337 8 * rowA 4 8 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 4 8 = (3 : ℚ) / 8 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_4_9 :
    yW_2337 0 * rowA 4 9 0 + yW_2337 1 * rowA 4 9 1 + yW_2337 2 * rowA 4 9 2 + yW_2337 3 * rowA 4 9 3 + yW_2337 4 * rowA 4 9 4 + yW_2337 5 * rowA 4 9 5 + yW_2337 6 * rowA 4 9 6 + yW_2337 7 * rowA 4 9 7 + yW_2337 8 * rowA 4 9 8 ≤ db_2337 4 9 := by
  have hleft : yW_2337 0 * rowA 4 9 0 + yW_2337 1 * rowA 4 9 1 + yW_2337 2 * rowA 4 9 2 + yW_2337 3 * rowA 4 9 3 + yW_2337 4 * rowA 4 9 4 + yW_2337 5 * rowA 4 9 5 + yW_2337 6 * rowA 4 9 6 + yW_2337 7 * rowA 4 9 7 + yW_2337 8 * rowA 4 9 8 = (3 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 4 9 = (3 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_5_0 :
    yW_2337 0 * rowA 5 0 0 + yW_2337 1 * rowA 5 0 1 + yW_2337 2 * rowA 5 0 2 + yW_2337 3 * rowA 5 0 3 + yW_2337 4 * rowA 5 0 4 + yW_2337 5 * rowA 5 0 5 + yW_2337 6 * rowA 5 0 6 + yW_2337 7 * rowA 5 0 7 + yW_2337 8 * rowA 5 0 8 ≤ db_2337 5 0 := by
  have hleft : yW_2337 0 * rowA 5 0 0 + yW_2337 1 * rowA 5 0 1 + yW_2337 2 * rowA 5 0 2 + yW_2337 3 * rowA 5 0 3 + yW_2337 4 * rowA 5 0 4 + yW_2337 5 * rowA 5 0 5 + yW_2337 6 * rowA 5 0 6 + yW_2337 7 * rowA 5 0 7 + yW_2337 8 * rowA 5 0 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 5 0 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_5_1 :
    yW_2337 0 * rowA 5 1 0 + yW_2337 1 * rowA 5 1 1 + yW_2337 2 * rowA 5 1 2 + yW_2337 3 * rowA 5 1 3 + yW_2337 4 * rowA 5 1 4 + yW_2337 5 * rowA 5 1 5 + yW_2337 6 * rowA 5 1 6 + yW_2337 7 * rowA 5 1 7 + yW_2337 8 * rowA 5 1 8 ≤ db_2337 5 1 := by
  have hleft : yW_2337 0 * rowA 5 1 0 + yW_2337 1 * rowA 5 1 1 + yW_2337 2 * rowA 5 1 2 + yW_2337 3 * rowA 5 1 3 + yW_2337 4 * rowA 5 1 4 + yW_2337 5 * rowA 5 1 5 + yW_2337 6 * rowA 5 1 6 + yW_2337 7 * rowA 5 1 7 + yW_2337 8 * rowA 5 1 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 5 1 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_5_2 :
    yW_2337 0 * rowA 5 2 0 + yW_2337 1 * rowA 5 2 1 + yW_2337 2 * rowA 5 2 2 + yW_2337 3 * rowA 5 2 3 + yW_2337 4 * rowA 5 2 4 + yW_2337 5 * rowA 5 2 5 + yW_2337 6 * rowA 5 2 6 + yW_2337 7 * rowA 5 2 7 + yW_2337 8 * rowA 5 2 8 ≤ db_2337 5 2 := by
  have hleft : yW_2337 0 * rowA 5 2 0 + yW_2337 1 * rowA 5 2 1 + yW_2337 2 * rowA 5 2 2 + yW_2337 3 * rowA 5 2 3 + yW_2337 4 * rowA 5 2 4 + yW_2337 5 * rowA 5 2 5 + yW_2337 6 * rowA 5 2 6 + yW_2337 7 * rowA 5 2 7 + yW_2337 8 * rowA 5 2 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 5 2 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_5_3 :
    yW_2337 0 * rowA 5 3 0 + yW_2337 1 * rowA 5 3 1 + yW_2337 2 * rowA 5 3 2 + yW_2337 3 * rowA 5 3 3 + yW_2337 4 * rowA 5 3 4 + yW_2337 5 * rowA 5 3 5 + yW_2337 6 * rowA 5 3 6 + yW_2337 7 * rowA 5 3 7 + yW_2337 8 * rowA 5 3 8 ≤ db_2337 5 3 := by
  have hleft : yW_2337 0 * rowA 5 3 0 + yW_2337 1 * rowA 5 3 1 + yW_2337 2 * rowA 5 3 2 + yW_2337 3 * rowA 5 3 3 + yW_2337 4 * rowA 5 3 4 + yW_2337 5 * rowA 5 3 5 + yW_2337 6 * rowA 5 3 6 + yW_2337 7 * rowA 5 3 7 + yW_2337 8 * rowA 5 3 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 5 3 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_5_4 :
    yW_2337 0 * rowA 5 4 0 + yW_2337 1 * rowA 5 4 1 + yW_2337 2 * rowA 5 4 2 + yW_2337 3 * rowA 5 4 3 + yW_2337 4 * rowA 5 4 4 + yW_2337 5 * rowA 5 4 5 + yW_2337 6 * rowA 5 4 6 + yW_2337 7 * rowA 5 4 7 + yW_2337 8 * rowA 5 4 8 ≤ db_2337 5 4 := by
  have hleft : yW_2337 0 * rowA 5 4 0 + yW_2337 1 * rowA 5 4 1 + yW_2337 2 * rowA 5 4 2 + yW_2337 3 * rowA 5 4 3 + yW_2337 4 * rowA 5 4 4 + yW_2337 5 * rowA 5 4 5 + yW_2337 6 * rowA 5 4 6 + yW_2337 7 * rowA 5 4 7 + yW_2337 8 * rowA 5 4 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 5 4 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_5_5 :
    yW_2337 0 * rowA 5 5 0 + yW_2337 1 * rowA 5 5 1 + yW_2337 2 * rowA 5 5 2 + yW_2337 3 * rowA 5 5 3 + yW_2337 4 * rowA 5 5 4 + yW_2337 5 * rowA 5 5 5 + yW_2337 6 * rowA 5 5 6 + yW_2337 7 * rowA 5 5 7 + yW_2337 8 * rowA 5 5 8 ≤ db_2337 5 5 := by
  have hleft : yW_2337 0 * rowA 5 5 0 + yW_2337 1 * rowA 5 5 1 + yW_2337 2 * rowA 5 5 2 + yW_2337 3 * rowA 5 5 3 + yW_2337 4 * rowA 5 5 4 + yW_2337 5 * rowA 5 5 5 + yW_2337 6 * rowA 5 5 6 + yW_2337 7 * rowA 5 5 7 + yW_2337 8 * rowA 5 5 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 5 5 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_5_6 :
    yW_2337 0 * rowA 5 6 0 + yW_2337 1 * rowA 5 6 1 + yW_2337 2 * rowA 5 6 2 + yW_2337 3 * rowA 5 6 3 + yW_2337 4 * rowA 5 6 4 + yW_2337 5 * rowA 5 6 5 + yW_2337 6 * rowA 5 6 6 + yW_2337 7 * rowA 5 6 7 + yW_2337 8 * rowA 5 6 8 ≤ db_2337 5 6 := by
  have hleft : yW_2337 0 * rowA 5 6 0 + yW_2337 1 * rowA 5 6 1 + yW_2337 2 * rowA 5 6 2 + yW_2337 3 * rowA 5 6 3 + yW_2337 4 * rowA 5 6 4 + yW_2337 5 * rowA 5 6 5 + yW_2337 6 * rowA 5 6 6 + yW_2337 7 * rowA 5 6 7 + yW_2337 8 * rowA 5 6 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 5 6 = (1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_5_7 :
    yW_2337 0 * rowA 5 7 0 + yW_2337 1 * rowA 5 7 1 + yW_2337 2 * rowA 5 7 2 + yW_2337 3 * rowA 5 7 3 + yW_2337 4 * rowA 5 7 4 + yW_2337 5 * rowA 5 7 5 + yW_2337 6 * rowA 5 7 6 + yW_2337 7 * rowA 5 7 7 + yW_2337 8 * rowA 5 7 8 ≤ db_2337 5 7 := by
  have hleft : yW_2337 0 * rowA 5 7 0 + yW_2337 1 * rowA 5 7 1 + yW_2337 2 * rowA 5 7 2 + yW_2337 3 * rowA 5 7 3 + yW_2337 4 * rowA 5 7 4 + yW_2337 5 * rowA 5 7 5 + yW_2337 6 * rowA 5 7 6 + yW_2337 7 * rowA 5 7 7 + yW_2337 8 * rowA 5 7 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 5 7 = (1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_5_8 :
    yW_2337 0 * rowA 5 8 0 + yW_2337 1 * rowA 5 8 1 + yW_2337 2 * rowA 5 8 2 + yW_2337 3 * rowA 5 8 3 + yW_2337 4 * rowA 5 8 4 + yW_2337 5 * rowA 5 8 5 + yW_2337 6 * rowA 5 8 6 + yW_2337 7 * rowA 5 8 7 + yW_2337 8 * rowA 5 8 8 ≤ db_2337 5 8 := by
  have hleft : yW_2337 0 * rowA 5 8 0 + yW_2337 1 * rowA 5 8 1 + yW_2337 2 * rowA 5 8 2 + yW_2337 3 * rowA 5 8 3 + yW_2337 4 * rowA 5 8 4 + yW_2337 5 * rowA 5 8 5 + yW_2337 6 * rowA 5 8 6 + yW_2337 7 * rowA 5 8 7 + yW_2337 8 * rowA 5 8 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 5 8 = (1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_5_9 :
    yW_2337 0 * rowA 5 9 0 + yW_2337 1 * rowA 5 9 1 + yW_2337 2 * rowA 5 9 2 + yW_2337 3 * rowA 5 9 3 + yW_2337 4 * rowA 5 9 4 + yW_2337 5 * rowA 5 9 5 + yW_2337 6 * rowA 5 9 6 + yW_2337 7 * rowA 5 9 7 + yW_2337 8 * rowA 5 9 8 ≤ db_2337 5 9 := by
  have hleft : yW_2337 0 * rowA 5 9 0 + yW_2337 1 * rowA 5 9 1 + yW_2337 2 * rowA 5 9 2 + yW_2337 3 * rowA 5 9 3 + yW_2337 4 * rowA 5 9 4 + yW_2337 5 * rowA 5 9 5 + yW_2337 6 * rowA 5 9 6 + yW_2337 7 * rowA 5 9 7 + yW_2337 8 * rowA 5 9 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 5 9 = (3 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_6_0 :
    yW_2337 0 * rowA 6 0 0 + yW_2337 1 * rowA 6 0 1 + yW_2337 2 * rowA 6 0 2 + yW_2337 3 * rowA 6 0 3 + yW_2337 4 * rowA 6 0 4 + yW_2337 5 * rowA 6 0 5 + yW_2337 6 * rowA 6 0 6 + yW_2337 7 * rowA 6 0 7 + yW_2337 8 * rowA 6 0 8 ≤ db_2337 6 0 := by
  have hleft : yW_2337 0 * rowA 6 0 0 + yW_2337 1 * rowA 6 0 1 + yW_2337 2 * rowA 6 0 2 + yW_2337 3 * rowA 6 0 3 + yW_2337 4 * rowA 6 0 4 + yW_2337 5 * rowA 6 0 5 + yW_2337 6 * rowA 6 0 6 + yW_2337 7 * rowA 6 0 7 + yW_2337 8 * rowA 6 0 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 6 0 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_6_1 :
    yW_2337 0 * rowA 6 1 0 + yW_2337 1 * rowA 6 1 1 + yW_2337 2 * rowA 6 1 2 + yW_2337 3 * rowA 6 1 3 + yW_2337 4 * rowA 6 1 4 + yW_2337 5 * rowA 6 1 5 + yW_2337 6 * rowA 6 1 6 + yW_2337 7 * rowA 6 1 7 + yW_2337 8 * rowA 6 1 8 ≤ db_2337 6 1 := by
  have hleft : yW_2337 0 * rowA 6 1 0 + yW_2337 1 * rowA 6 1 1 + yW_2337 2 * rowA 6 1 2 + yW_2337 3 * rowA 6 1 3 + yW_2337 4 * rowA 6 1 4 + yW_2337 5 * rowA 6 1 5 + yW_2337 6 * rowA 6 1 6 + yW_2337 7 * rowA 6 1 7 + yW_2337 8 * rowA 6 1 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 6 1 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_6_2 :
    yW_2337 0 * rowA 6 2 0 + yW_2337 1 * rowA 6 2 1 + yW_2337 2 * rowA 6 2 2 + yW_2337 3 * rowA 6 2 3 + yW_2337 4 * rowA 6 2 4 + yW_2337 5 * rowA 6 2 5 + yW_2337 6 * rowA 6 2 6 + yW_2337 7 * rowA 6 2 7 + yW_2337 8 * rowA 6 2 8 ≤ db_2337 6 2 := by
  have hleft : yW_2337 0 * rowA 6 2 0 + yW_2337 1 * rowA 6 2 1 + yW_2337 2 * rowA 6 2 2 + yW_2337 3 * rowA 6 2 3 + yW_2337 4 * rowA 6 2 4 + yW_2337 5 * rowA 6 2 5 + yW_2337 6 * rowA 6 2 6 + yW_2337 7 * rowA 6 2 7 + yW_2337 8 * rowA 6 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 6 2 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_6_3 :
    yW_2337 0 * rowA 6 3 0 + yW_2337 1 * rowA 6 3 1 + yW_2337 2 * rowA 6 3 2 + yW_2337 3 * rowA 6 3 3 + yW_2337 4 * rowA 6 3 4 + yW_2337 5 * rowA 6 3 5 + yW_2337 6 * rowA 6 3 6 + yW_2337 7 * rowA 6 3 7 + yW_2337 8 * rowA 6 3 8 ≤ db_2337 6 3 := by
  have hleft : yW_2337 0 * rowA 6 3 0 + yW_2337 1 * rowA 6 3 1 + yW_2337 2 * rowA 6 3 2 + yW_2337 3 * rowA 6 3 3 + yW_2337 4 * rowA 6 3 4 + yW_2337 5 * rowA 6 3 5 + yW_2337 6 * rowA 6 3 6 + yW_2337 7 * rowA 6 3 7 + yW_2337 8 * rowA 6 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 6 3 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_6_4 :
    yW_2337 0 * rowA 6 4 0 + yW_2337 1 * rowA 6 4 1 + yW_2337 2 * rowA 6 4 2 + yW_2337 3 * rowA 6 4 3 + yW_2337 4 * rowA 6 4 4 + yW_2337 5 * rowA 6 4 5 + yW_2337 6 * rowA 6 4 6 + yW_2337 7 * rowA 6 4 7 + yW_2337 8 * rowA 6 4 8 ≤ db_2337 6 4 := by
  have hleft : yW_2337 0 * rowA 6 4 0 + yW_2337 1 * rowA 6 4 1 + yW_2337 2 * rowA 6 4 2 + yW_2337 3 * rowA 6 4 3 + yW_2337 4 * rowA 6 4 4 + yW_2337 5 * rowA 6 4 5 + yW_2337 6 * rowA 6 4 6 + yW_2337 7 * rowA 6 4 7 + yW_2337 8 * rowA 6 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 6 4 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_6_5 :
    yW_2337 0 * rowA 6 5 0 + yW_2337 1 * rowA 6 5 1 + yW_2337 2 * rowA 6 5 2 + yW_2337 3 * rowA 6 5 3 + yW_2337 4 * rowA 6 5 4 + yW_2337 5 * rowA 6 5 5 + yW_2337 6 * rowA 6 5 6 + yW_2337 7 * rowA 6 5 7 + yW_2337 8 * rowA 6 5 8 ≤ db_2337 6 5 := by
  have hleft : yW_2337 0 * rowA 6 5 0 + yW_2337 1 * rowA 6 5 1 + yW_2337 2 * rowA 6 5 2 + yW_2337 3 * rowA 6 5 3 + yW_2337 4 * rowA 6 5 4 + yW_2337 5 * rowA 6 5 5 + yW_2337 6 * rowA 6 5 6 + yW_2337 7 * rowA 6 5 7 + yW_2337 8 * rowA 6 5 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 6 5 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_6_6 :
    yW_2337 0 * rowA 6 6 0 + yW_2337 1 * rowA 6 6 1 + yW_2337 2 * rowA 6 6 2 + yW_2337 3 * rowA 6 6 3 + yW_2337 4 * rowA 6 6 4 + yW_2337 5 * rowA 6 6 5 + yW_2337 6 * rowA 6 6 6 + yW_2337 7 * rowA 6 6 7 + yW_2337 8 * rowA 6 6 8 ≤ db_2337 6 6 := by
  have hleft : yW_2337 0 * rowA 6 6 0 + yW_2337 1 * rowA 6 6 1 + yW_2337 2 * rowA 6 6 2 + yW_2337 3 * rowA 6 6 3 + yW_2337 4 * rowA 6 6 4 + yW_2337 5 * rowA 6 6 5 + yW_2337 6 * rowA 6 6 6 + yW_2337 7 * rowA 6 6 7 + yW_2337 8 * rowA 6 6 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 6 6 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_6_7 :
    yW_2337 0 * rowA 6 7 0 + yW_2337 1 * rowA 6 7 1 + yW_2337 2 * rowA 6 7 2 + yW_2337 3 * rowA 6 7 3 + yW_2337 4 * rowA 6 7 4 + yW_2337 5 * rowA 6 7 5 + yW_2337 6 * rowA 6 7 6 + yW_2337 7 * rowA 6 7 7 + yW_2337 8 * rowA 6 7 8 ≤ db_2337 6 7 := by
  have hleft : yW_2337 0 * rowA 6 7 0 + yW_2337 1 * rowA 6 7 1 + yW_2337 2 * rowA 6 7 2 + yW_2337 3 * rowA 6 7 3 + yW_2337 4 * rowA 6 7 4 + yW_2337 5 * rowA 6 7 5 + yW_2337 6 * rowA 6 7 6 + yW_2337 7 * rowA 6 7 7 + yW_2337 8 * rowA 6 7 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 6 7 = (1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_6_8 :
    yW_2337 0 * rowA 6 8 0 + yW_2337 1 * rowA 6 8 1 + yW_2337 2 * rowA 6 8 2 + yW_2337 3 * rowA 6 8 3 + yW_2337 4 * rowA 6 8 4 + yW_2337 5 * rowA 6 8 5 + yW_2337 6 * rowA 6 8 6 + yW_2337 7 * rowA 6 8 7 + yW_2337 8 * rowA 6 8 8 ≤ db_2337 6 8 := by
  have hleft : yW_2337 0 * rowA 6 8 0 + yW_2337 1 * rowA 6 8 1 + yW_2337 2 * rowA 6 8 2 + yW_2337 3 * rowA 6 8 3 + yW_2337 4 * rowA 6 8 4 + yW_2337 5 * rowA 6 8 5 + yW_2337 6 * rowA 6 8 6 + yW_2337 7 * rowA 6 8 7 + yW_2337 8 * rowA 6 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 6 8 = (1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_6_9 :
    yW_2337 0 * rowA 6 9 0 + yW_2337 1 * rowA 6 9 1 + yW_2337 2 * rowA 6 9 2 + yW_2337 3 * rowA 6 9 3 + yW_2337 4 * rowA 6 9 4 + yW_2337 5 * rowA 6 9 5 + yW_2337 6 * rowA 6 9 6 + yW_2337 7 * rowA 6 9 7 + yW_2337 8 * rowA 6 9 8 ≤ db_2337 6 9 := by
  have hleft : yW_2337 0 * rowA 6 9 0 + yW_2337 1 * rowA 6 9 1 + yW_2337 2 * rowA 6 9 2 + yW_2337 3 * rowA 6 9 3 + yW_2337 4 * rowA 6 9 4 + yW_2337 5 * rowA 6 9 5 + yW_2337 6 * rowA 6 9 6 + yW_2337 7 * rowA 6 9 7 + yW_2337 8 * rowA 6 9 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 6 9 = (3 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_7_0 :
    yW_2337 0 * rowA 7 0 0 + yW_2337 1 * rowA 7 0 1 + yW_2337 2 * rowA 7 0 2 + yW_2337 3 * rowA 7 0 3 + yW_2337 4 * rowA 7 0 4 + yW_2337 5 * rowA 7 0 5 + yW_2337 6 * rowA 7 0 6 + yW_2337 7 * rowA 7 0 7 + yW_2337 8 * rowA 7 0 8 ≤ db_2337 7 0 := by
  have hleft : yW_2337 0 * rowA 7 0 0 + yW_2337 1 * rowA 7 0 1 + yW_2337 2 * rowA 7 0 2 + yW_2337 3 * rowA 7 0 3 + yW_2337 4 * rowA 7 0 4 + yW_2337 5 * rowA 7 0 5 + yW_2337 6 * rowA 7 0 6 + yW_2337 7 * rowA 7 0 7 + yW_2337 8 * rowA 7 0 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 7 0 = (-1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_7_1 :
    yW_2337 0 * rowA 7 1 0 + yW_2337 1 * rowA 7 1 1 + yW_2337 2 * rowA 7 1 2 + yW_2337 3 * rowA 7 1 3 + yW_2337 4 * rowA 7 1 4 + yW_2337 5 * rowA 7 1 5 + yW_2337 6 * rowA 7 1 6 + yW_2337 7 * rowA 7 1 7 + yW_2337 8 * rowA 7 1 8 ≤ db_2337 7 1 := by
  have hleft : yW_2337 0 * rowA 7 1 0 + yW_2337 1 * rowA 7 1 1 + yW_2337 2 * rowA 7 1 2 + yW_2337 3 * rowA 7 1 3 + yW_2337 4 * rowA 7 1 4 + yW_2337 5 * rowA 7 1 5 + yW_2337 6 * rowA 7 1 6 + yW_2337 7 * rowA 7 1 7 + yW_2337 8 * rowA 7 1 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 7 1 = (-1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_7_2 :
    yW_2337 0 * rowA 7 2 0 + yW_2337 1 * rowA 7 2 1 + yW_2337 2 * rowA 7 2 2 + yW_2337 3 * rowA 7 2 3 + yW_2337 4 * rowA 7 2 4 + yW_2337 5 * rowA 7 2 5 + yW_2337 6 * rowA 7 2 6 + yW_2337 7 * rowA 7 2 7 + yW_2337 8 * rowA 7 2 8 ≤ db_2337 7 2 := by
  have hleft : yW_2337 0 * rowA 7 2 0 + yW_2337 1 * rowA 7 2 1 + yW_2337 2 * rowA 7 2 2 + yW_2337 3 * rowA 7 2 3 + yW_2337 4 * rowA 7 2 4 + yW_2337 5 * rowA 7 2 5 + yW_2337 6 * rowA 7 2 6 + yW_2337 7 * rowA 7 2 7 + yW_2337 8 * rowA 7 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 7 2 = (-1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_7_3 :
    yW_2337 0 * rowA 7 3 0 + yW_2337 1 * rowA 7 3 1 + yW_2337 2 * rowA 7 3 2 + yW_2337 3 * rowA 7 3 3 + yW_2337 4 * rowA 7 3 4 + yW_2337 5 * rowA 7 3 5 + yW_2337 6 * rowA 7 3 6 + yW_2337 7 * rowA 7 3 7 + yW_2337 8 * rowA 7 3 8 ≤ db_2337 7 3 := by
  have hleft : yW_2337 0 * rowA 7 3 0 + yW_2337 1 * rowA 7 3 1 + yW_2337 2 * rowA 7 3 2 + yW_2337 3 * rowA 7 3 3 + yW_2337 4 * rowA 7 3 4 + yW_2337 5 * rowA 7 3 5 + yW_2337 6 * rowA 7 3 6 + yW_2337 7 * rowA 7 3 7 + yW_2337 8 * rowA 7 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 7 3 = (-1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_7_4 :
    yW_2337 0 * rowA 7 4 0 + yW_2337 1 * rowA 7 4 1 + yW_2337 2 * rowA 7 4 2 + yW_2337 3 * rowA 7 4 3 + yW_2337 4 * rowA 7 4 4 + yW_2337 5 * rowA 7 4 5 + yW_2337 6 * rowA 7 4 6 + yW_2337 7 * rowA 7 4 7 + yW_2337 8 * rowA 7 4 8 ≤ db_2337 7 4 := by
  have hleft : yW_2337 0 * rowA 7 4 0 + yW_2337 1 * rowA 7 4 1 + yW_2337 2 * rowA 7 4 2 + yW_2337 3 * rowA 7 4 3 + yW_2337 4 * rowA 7 4 4 + yW_2337 5 * rowA 7 4 5 + yW_2337 6 * rowA 7 4 6 + yW_2337 7 * rowA 7 4 7 + yW_2337 8 * rowA 7 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 7 4 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_7_5 :
    yW_2337 0 * rowA 7 5 0 + yW_2337 1 * rowA 7 5 1 + yW_2337 2 * rowA 7 5 2 + yW_2337 3 * rowA 7 5 3 + yW_2337 4 * rowA 7 5 4 + yW_2337 5 * rowA 7 5 5 + yW_2337 6 * rowA 7 5 6 + yW_2337 7 * rowA 7 5 7 + yW_2337 8 * rowA 7 5 8 ≤ db_2337 7 5 := by
  have hleft : yW_2337 0 * rowA 7 5 0 + yW_2337 1 * rowA 7 5 1 + yW_2337 2 * rowA 7 5 2 + yW_2337 3 * rowA 7 5 3 + yW_2337 4 * rowA 7 5 4 + yW_2337 5 * rowA 7 5 5 + yW_2337 6 * rowA 7 5 6 + yW_2337 7 * rowA 7 5 7 + yW_2337 8 * rowA 7 5 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 7 5 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_7_6 :
    yW_2337 0 * rowA 7 6 0 + yW_2337 1 * rowA 7 6 1 + yW_2337 2 * rowA 7 6 2 + yW_2337 3 * rowA 7 6 3 + yW_2337 4 * rowA 7 6 4 + yW_2337 5 * rowA 7 6 5 + yW_2337 6 * rowA 7 6 6 + yW_2337 7 * rowA 7 6 7 + yW_2337 8 * rowA 7 6 8 ≤ db_2337 7 6 := by
  have hleft : yW_2337 0 * rowA 7 6 0 + yW_2337 1 * rowA 7 6 1 + yW_2337 2 * rowA 7 6 2 + yW_2337 3 * rowA 7 6 3 + yW_2337 4 * rowA 7 6 4 + yW_2337 5 * rowA 7 6 5 + yW_2337 6 * rowA 7 6 6 + yW_2337 7 * rowA 7 6 7 + yW_2337 8 * rowA 7 6 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 7 6 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_7_7 :
    yW_2337 0 * rowA 7 7 0 + yW_2337 1 * rowA 7 7 1 + yW_2337 2 * rowA 7 7 2 + yW_2337 3 * rowA 7 7 3 + yW_2337 4 * rowA 7 7 4 + yW_2337 5 * rowA 7 7 5 + yW_2337 6 * rowA 7 7 6 + yW_2337 7 * rowA 7 7 7 + yW_2337 8 * rowA 7 7 8 ≤ db_2337 7 7 := by
  have hleft : yW_2337 0 * rowA 7 7 0 + yW_2337 1 * rowA 7 7 1 + yW_2337 2 * rowA 7 7 2 + yW_2337 3 * rowA 7 7 3 + yW_2337 4 * rowA 7 7 4 + yW_2337 5 * rowA 7 7 5 + yW_2337 6 * rowA 7 7 6 + yW_2337 7 * rowA 7 7 7 + yW_2337 8 * rowA 7 7 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 7 7 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_7_8 :
    yW_2337 0 * rowA 7 8 0 + yW_2337 1 * rowA 7 8 1 + yW_2337 2 * rowA 7 8 2 + yW_2337 3 * rowA 7 8 3 + yW_2337 4 * rowA 7 8 4 + yW_2337 5 * rowA 7 8 5 + yW_2337 6 * rowA 7 8 6 + yW_2337 7 * rowA 7 8 7 + yW_2337 8 * rowA 7 8 8 ≤ db_2337 7 8 := by
  have hleft : yW_2337 0 * rowA 7 8 0 + yW_2337 1 * rowA 7 8 1 + yW_2337 2 * rowA 7 8 2 + yW_2337 3 * rowA 7 8 3 + yW_2337 4 * rowA 7 8 4 + yW_2337 5 * rowA 7 8 5 + yW_2337 6 * rowA 7 8 6 + yW_2337 7 * rowA 7 8 7 + yW_2337 8 * rowA 7 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 7 8 = (1 : ℚ) / 8 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_7_9 :
    yW_2337 0 * rowA 7 9 0 + yW_2337 1 * rowA 7 9 1 + yW_2337 2 * rowA 7 9 2 + yW_2337 3 * rowA 7 9 3 + yW_2337 4 * rowA 7 9 4 + yW_2337 5 * rowA 7 9 5 + yW_2337 6 * rowA 7 9 6 + yW_2337 7 * rowA 7 9 7 + yW_2337 8 * rowA 7 9 8 ≤ db_2337 7 9 := by
  have hleft : yW_2337 0 * rowA 7 9 0 + yW_2337 1 * rowA 7 9 1 + yW_2337 2 * rowA 7 9 2 + yW_2337 3 * rowA 7 9 3 + yW_2337 4 * rowA 7 9 4 + yW_2337 5 * rowA 7 9 5 + yW_2337 6 * rowA 7 9 6 + yW_2337 7 * rowA 7 9 7 + yW_2337 8 * rowA 7 9 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 7 9 = (1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_8_0 :
    yW_2337 0 * rowA 8 0 0 + yW_2337 1 * rowA 8 0 1 + yW_2337 2 * rowA 8 0 2 + yW_2337 3 * rowA 8 0 3 + yW_2337 4 * rowA 8 0 4 + yW_2337 5 * rowA 8 0 5 + yW_2337 6 * rowA 8 0 6 + yW_2337 7 * rowA 8 0 7 + yW_2337 8 * rowA 8 0 8 ≤ db_2337 8 0 := by
  have hleft : yW_2337 0 * rowA 8 0 0 + yW_2337 1 * rowA 8 0 1 + yW_2337 2 * rowA 8 0 2 + yW_2337 3 * rowA 8 0 3 + yW_2337 4 * rowA 8 0 4 + yW_2337 5 * rowA 8 0 5 + yW_2337 6 * rowA 8 0 6 + yW_2337 7 * rowA 8 0 7 + yW_2337 8 * rowA 8 0 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 8 0 = (-1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_8_1 :
    yW_2337 0 * rowA 8 1 0 + yW_2337 1 * rowA 8 1 1 + yW_2337 2 * rowA 8 1 2 + yW_2337 3 * rowA 8 1 3 + yW_2337 4 * rowA 8 1 4 + yW_2337 5 * rowA 8 1 5 + yW_2337 6 * rowA 8 1 6 + yW_2337 7 * rowA 8 1 7 + yW_2337 8 * rowA 8 1 8 ≤ db_2337 8 1 := by
  have hleft : yW_2337 0 * rowA 8 1 0 + yW_2337 1 * rowA 8 1 1 + yW_2337 2 * rowA 8 1 2 + yW_2337 3 * rowA 8 1 3 + yW_2337 4 * rowA 8 1 4 + yW_2337 5 * rowA 8 1 5 + yW_2337 6 * rowA 8 1 6 + yW_2337 7 * rowA 8 1 7 + yW_2337 8 * rowA 8 1 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 8 1 = (-1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_8_2 :
    yW_2337 0 * rowA 8 2 0 + yW_2337 1 * rowA 8 2 1 + yW_2337 2 * rowA 8 2 2 + yW_2337 3 * rowA 8 2 3 + yW_2337 4 * rowA 8 2 4 + yW_2337 5 * rowA 8 2 5 + yW_2337 6 * rowA 8 2 6 + yW_2337 7 * rowA 8 2 7 + yW_2337 8 * rowA 8 2 8 ≤ db_2337 8 2 := by
  have hleft : yW_2337 0 * rowA 8 2 0 + yW_2337 1 * rowA 8 2 1 + yW_2337 2 * rowA 8 2 2 + yW_2337 3 * rowA 8 2 3 + yW_2337 4 * rowA 8 2 4 + yW_2337 5 * rowA 8 2 5 + yW_2337 6 * rowA 8 2 6 + yW_2337 7 * rowA 8 2 7 + yW_2337 8 * rowA 8 2 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 8 2 = (-1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_8_3 :
    yW_2337 0 * rowA 8 3 0 + yW_2337 1 * rowA 8 3 1 + yW_2337 2 * rowA 8 3 2 + yW_2337 3 * rowA 8 3 3 + yW_2337 4 * rowA 8 3 4 + yW_2337 5 * rowA 8 3 5 + yW_2337 6 * rowA 8 3 6 + yW_2337 7 * rowA 8 3 7 + yW_2337 8 * rowA 8 3 8 ≤ db_2337 8 3 := by
  have hleft : yW_2337 0 * rowA 8 3 0 + yW_2337 1 * rowA 8 3 1 + yW_2337 2 * rowA 8 3 2 + yW_2337 3 * rowA 8 3 3 + yW_2337 4 * rowA 8 3 4 + yW_2337 5 * rowA 8 3 5 + yW_2337 6 * rowA 8 3 6 + yW_2337 7 * rowA 8 3 7 + yW_2337 8 * rowA 8 3 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 8 3 = (-1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_8_4 :
    yW_2337 0 * rowA 8 4 0 + yW_2337 1 * rowA 8 4 1 + yW_2337 2 * rowA 8 4 2 + yW_2337 3 * rowA 8 4 3 + yW_2337 4 * rowA 8 4 4 + yW_2337 5 * rowA 8 4 5 + yW_2337 6 * rowA 8 4 6 + yW_2337 7 * rowA 8 4 7 + yW_2337 8 * rowA 8 4 8 ≤ db_2337 8 4 := by
  have hleft : yW_2337 0 * rowA 8 4 0 + yW_2337 1 * rowA 8 4 1 + yW_2337 2 * rowA 8 4 2 + yW_2337 3 * rowA 8 4 3 + yW_2337 4 * rowA 8 4 4 + yW_2337 5 * rowA 8 4 5 + yW_2337 6 * rowA 8 4 6 + yW_2337 7 * rowA 8 4 7 + yW_2337 8 * rowA 8 4 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 8 4 = (-1 : ℚ) / 4 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_8_5 :
    yW_2337 0 * rowA 8 5 0 + yW_2337 1 * rowA 8 5 1 + yW_2337 2 * rowA 8 5 2 + yW_2337 3 * rowA 8 5 3 + yW_2337 4 * rowA 8 5 4 + yW_2337 5 * rowA 8 5 5 + yW_2337 6 * rowA 8 5 6 + yW_2337 7 * rowA 8 5 7 + yW_2337 8 * rowA 8 5 8 ≤ db_2337 8 5 := by
  have hleft : yW_2337 0 * rowA 8 5 0 + yW_2337 1 * rowA 8 5 1 + yW_2337 2 * rowA 8 5 2 + yW_2337 3 * rowA 8 5 3 + yW_2337 4 * rowA 8 5 4 + yW_2337 5 * rowA 8 5 5 + yW_2337 6 * rowA 8 5 6 + yW_2337 7 * rowA 8 5 7 + yW_2337 8 * rowA 8 5 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 8 5 = (-1 : ℚ) / 8 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_8_6 :
    yW_2337 0 * rowA 8 6 0 + yW_2337 1 * rowA 8 6 1 + yW_2337 2 * rowA 8 6 2 + yW_2337 3 * rowA 8 6 3 + yW_2337 4 * rowA 8 6 4 + yW_2337 5 * rowA 8 6 5 + yW_2337 6 * rowA 8 6 6 + yW_2337 7 * rowA 8 6 7 + yW_2337 8 * rowA 8 6 8 ≤ db_2337 8 6 := by
  have hleft : yW_2337 0 * rowA 8 6 0 + yW_2337 1 * rowA 8 6 1 + yW_2337 2 * rowA 8 6 2 + yW_2337 3 * rowA 8 6 3 + yW_2337 4 * rowA 8 6 4 + yW_2337 5 * rowA 8 6 5 + yW_2337 6 * rowA 8 6 6 + yW_2337 7 * rowA 8 6 7 + yW_2337 8 * rowA 8 6 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 8 6 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_8_7 :
    yW_2337 0 * rowA 8 7 0 + yW_2337 1 * rowA 8 7 1 + yW_2337 2 * rowA 8 7 2 + yW_2337 3 * rowA 8 7 3 + yW_2337 4 * rowA 8 7 4 + yW_2337 5 * rowA 8 7 5 + yW_2337 6 * rowA 8 7 6 + yW_2337 7 * rowA 8 7 7 + yW_2337 8 * rowA 8 7 8 ≤ db_2337 8 7 := by
  have hleft : yW_2337 0 * rowA 8 7 0 + yW_2337 1 * rowA 8 7 1 + yW_2337 2 * rowA 8 7 2 + yW_2337 3 * rowA 8 7 3 + yW_2337 4 * rowA 8 7 4 + yW_2337 5 * rowA 8 7 5 + yW_2337 6 * rowA 8 7 6 + yW_2337 7 * rowA 8 7 7 + yW_2337 8 * rowA 8 7 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 8 7 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_8_8 :
    yW_2337 0 * rowA 8 8 0 + yW_2337 1 * rowA 8 8 1 + yW_2337 2 * rowA 8 8 2 + yW_2337 3 * rowA 8 8 3 + yW_2337 4 * rowA 8 8 4 + yW_2337 5 * rowA 8 8 5 + yW_2337 6 * rowA 8 8 6 + yW_2337 7 * rowA 8 8 7 + yW_2337 8 * rowA 8 8 8 ≤ db_2337 8 8 := by
  have hleft : yW_2337 0 * rowA 8 8 0 + yW_2337 1 * rowA 8 8 1 + yW_2337 2 * rowA 8 8 2 + yW_2337 3 * rowA 8 8 3 + yW_2337 4 * rowA 8 8 4 + yW_2337 5 * rowA 8 8 5 + yW_2337 6 * rowA 8 8 6 + yW_2337 7 * rowA 8 8 7 + yW_2337 8 * rowA 8 8 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 8 8 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_8_9 :
    yW_2337 0 * rowA 8 9 0 + yW_2337 1 * rowA 8 9 1 + yW_2337 2 * rowA 8 9 2 + yW_2337 3 * rowA 8 9 3 + yW_2337 4 * rowA 8 9 4 + yW_2337 5 * rowA 8 9 5 + yW_2337 6 * rowA 8 9 6 + yW_2337 7 * rowA 8 9 7 + yW_2337 8 * rowA 8 9 8 ≤ db_2337 8 9 := by
  have hleft : yW_2337 0 * rowA 8 9 0 + yW_2337 1 * rowA 8 9 1 + yW_2337 2 * rowA 8 9 2 + yW_2337 3 * rowA 8 9 3 + yW_2337 4 * rowA 8 9 4 + yW_2337 5 * rowA 8 9 5 + yW_2337 6 * rowA 8 9 6 + yW_2337 7 * rowA 8 9 7 + yW_2337 8 * rowA 8 9 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 8 9 = (1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_9_0 :
    yW_2337 0 * rowA 9 0 0 + yW_2337 1 * rowA 9 0 1 + yW_2337 2 * rowA 9 0 2 + yW_2337 3 * rowA 9 0 3 + yW_2337 4 * rowA 9 0 4 + yW_2337 5 * rowA 9 0 5 + yW_2337 6 * rowA 9 0 6 + yW_2337 7 * rowA 9 0 7 + yW_2337 8 * rowA 9 0 8 ≤ db_2337 9 0 := by
  have hleft : yW_2337 0 * rowA 9 0 0 + yW_2337 1 * rowA 9 0 1 + yW_2337 2 * rowA 9 0 2 + yW_2337 3 * rowA 9 0 3 + yW_2337 4 * rowA 9 0 4 + yW_2337 5 * rowA 9 0 5 + yW_2337 6 * rowA 9 0 6 + yW_2337 7 * rowA 9 0 7 + yW_2337 8 * rowA 9 0 8 = (-1 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 9 0 = (-1 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_9_1 :
    yW_2337 0 * rowA 9 1 0 + yW_2337 1 * rowA 9 1 1 + yW_2337 2 * rowA 9 1 2 + yW_2337 3 * rowA 9 1 3 + yW_2337 4 * rowA 9 1 4 + yW_2337 5 * rowA 9 1 5 + yW_2337 6 * rowA 9 1 6 + yW_2337 7 * rowA 9 1 7 + yW_2337 8 * rowA 9 1 8 ≤ db_2337 9 1 := by
  have hleft : yW_2337 0 * rowA 9 1 0 + yW_2337 1 * rowA 9 1 1 + yW_2337 2 * rowA 9 1 2 + yW_2337 3 * rowA 9 1 3 + yW_2337 4 * rowA 9 1 4 + yW_2337 5 * rowA 9 1 5 + yW_2337 6 * rowA 9 1 6 + yW_2337 7 * rowA 9 1 7 + yW_2337 8 * rowA 9 1 8 = (-1 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 9 1 = (-13 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_9_2 :
    yW_2337 0 * rowA 9 2 0 + yW_2337 1 * rowA 9 2 1 + yW_2337 2 * rowA 9 2 2 + yW_2337 3 * rowA 9 2 3 + yW_2337 4 * rowA 9 2 4 + yW_2337 5 * rowA 9 2 5 + yW_2337 6 * rowA 9 2 6 + yW_2337 7 * rowA 9 2 7 + yW_2337 8 * rowA 9 2 8 ≤ db_2337 9 2 := by
  have hleft : yW_2337 0 * rowA 9 2 0 + yW_2337 1 * rowA 9 2 1 + yW_2337 2 * rowA 9 2 2 + yW_2337 3 * rowA 9 2 3 + yW_2337 4 * rowA 9 2 4 + yW_2337 5 * rowA 9 2 5 + yW_2337 6 * rowA 9 2 6 + yW_2337 7 * rowA 9 2 7 + yW_2337 8 * rowA 9 2 8 = (-1 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 9 2 = (-13 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_9_3 :
    yW_2337 0 * rowA 9 3 0 + yW_2337 1 * rowA 9 3 1 + yW_2337 2 * rowA 9 3 2 + yW_2337 3 * rowA 9 3 3 + yW_2337 4 * rowA 9 3 4 + yW_2337 5 * rowA 9 3 5 + yW_2337 6 * rowA 9 3 6 + yW_2337 7 * rowA 9 3 7 + yW_2337 8 * rowA 9 3 8 ≤ db_2337 9 3 := by
  have hleft : yW_2337 0 * rowA 9 3 0 + yW_2337 1 * rowA 9 3 1 + yW_2337 2 * rowA 9 3 2 + yW_2337 3 * rowA 9 3 3 + yW_2337 4 * rowA 9 3 4 + yW_2337 5 * rowA 9 3 5 + yW_2337 6 * rowA 9 3 6 + yW_2337 7 * rowA 9 3 7 + yW_2337 8 * rowA 9 3 8 = (-1 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 9 3 = (-13 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_9_4 :
    yW_2337 0 * rowA 9 4 0 + yW_2337 1 * rowA 9 4 1 + yW_2337 2 * rowA 9 4 2 + yW_2337 3 * rowA 9 4 3 + yW_2337 4 * rowA 9 4 4 + yW_2337 5 * rowA 9 4 5 + yW_2337 6 * rowA 9 4 6 + yW_2337 7 * rowA 9 4 7 + yW_2337 8 * rowA 9 4 8 ≤ db_2337 9 4 := by
  have hleft : yW_2337 0 * rowA 9 4 0 + yW_2337 1 * rowA 9 4 1 + yW_2337 2 * rowA 9 4 2 + yW_2337 3 * rowA 9 4 3 + yW_2337 4 * rowA 9 4 4 + yW_2337 5 * rowA 9 4 5 + yW_2337 6 * rowA 9 4 6 + yW_2337 7 * rowA 9 4 7 + yW_2337 8 * rowA 9 4 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 9 4 = (-11 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_9_5 :
    yW_2337 0 * rowA 9 5 0 + yW_2337 1 * rowA 9 5 1 + yW_2337 2 * rowA 9 5 2 + yW_2337 3 * rowA 9 5 3 + yW_2337 4 * rowA 9 5 4 + yW_2337 5 * rowA 9 5 5 + yW_2337 6 * rowA 9 5 6 + yW_2337 7 * rowA 9 5 7 + yW_2337 8 * rowA 9 5 8 ≤ db_2337 9 5 := by
  have hleft : yW_2337 0 * rowA 9 5 0 + yW_2337 1 * rowA 9 5 1 + yW_2337 2 * rowA 9 5 2 + yW_2337 3 * rowA 9 5 3 + yW_2337 4 * rowA 9 5 4 + yW_2337 5 * rowA 9 5 5 + yW_2337 6 * rowA 9 5 6 + yW_2337 7 * rowA 9 5 7 + yW_2337 8 * rowA 9 5 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 9 5 = (-1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_9_6 :
    yW_2337 0 * rowA 9 6 0 + yW_2337 1 * rowA 9 6 1 + yW_2337 2 * rowA 9 6 2 + yW_2337 3 * rowA 9 6 3 + yW_2337 4 * rowA 9 6 4 + yW_2337 5 * rowA 9 6 5 + yW_2337 6 * rowA 9 6 6 + yW_2337 7 * rowA 9 6 7 + yW_2337 8 * rowA 9 6 8 ≤ db_2337 9 6 := by
  have hleft : yW_2337 0 * rowA 9 6 0 + yW_2337 1 * rowA 9 6 1 + yW_2337 2 * rowA 9 6 2 + yW_2337 3 * rowA 9 6 3 + yW_2337 4 * rowA 9 6 4 + yW_2337 5 * rowA 9 6 5 + yW_2337 6 * rowA 9 6 6 + yW_2337 7 * rowA 9 6 7 + yW_2337 8 * rowA 9 6 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 9 6 = (-1 : ℚ) / 2 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_9_7 :
    yW_2337 0 * rowA 9 7 0 + yW_2337 1 * rowA 9 7 1 + yW_2337 2 * rowA 9 7 2 + yW_2337 3 * rowA 9 7 3 + yW_2337 4 * rowA 9 7 4 + yW_2337 5 * rowA 9 7 5 + yW_2337 6 * rowA 9 7 6 + yW_2337 7 * rowA 9 7 7 + yW_2337 8 * rowA 9 7 8 ≤ db_2337 9 7 := by
  have hleft : yW_2337 0 * rowA 9 7 0 + yW_2337 1 * rowA 9 7 1 + yW_2337 2 * rowA 9 7 2 + yW_2337 3 * rowA 9 7 3 + yW_2337 4 * rowA 9 7 4 + yW_2337 5 * rowA 9 7 5 + yW_2337 6 * rowA 9 7 6 + yW_2337 7 * rowA 9 7 7 + yW_2337 8 * rowA 9 7 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 9 7 = (-5 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_9_8 :
    yW_2337 0 * rowA 9 8 0 + yW_2337 1 * rowA 9 8 1 + yW_2337 2 * rowA 9 8 2 + yW_2337 3 * rowA 9 8 3 + yW_2337 4 * rowA 9 8 4 + yW_2337 5 * rowA 9 8 5 + yW_2337 6 * rowA 9 8 6 + yW_2337 7 * rowA 9 8 7 + yW_2337 8 * rowA 9 8 8 ≤ db_2337 9 8 := by
  have hleft : yW_2337 0 * rowA 9 8 0 + yW_2337 1 * rowA 9 8 1 + yW_2337 2 * rowA 9 8 2 + yW_2337 3 * rowA 9 8 3 + yW_2337 4 * rowA 9 8 4 + yW_2337 5 * rowA 9 8 5 + yW_2337 6 * rowA 9 8 6 + yW_2337 7 * rowA 9 8 7 + yW_2337 8 * rowA 9 8 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 9 8 = (-5 : ℚ) / 16 := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_9_9 :
    yW_2337 0 * rowA 9 9 0 + yW_2337 1 * rowA 9 9 1 + yW_2337 2 * rowA 9 9 2 + yW_2337 3 * rowA 9 9 3 + yW_2337 4 * rowA 9 9 4 + yW_2337 5 * rowA 9 9 5 + yW_2337 6 * rowA 9 9 6 + yW_2337 7 * rowA 9 9 7 + yW_2337 8 * rowA 9 9 8 ≤ db_2337 9 9 := by
  have hleft : yW_2337 0 * rowA 9 9 0 + yW_2337 1 * rowA 9 9 1 + yW_2337 2 * rowA 9 9 2 + yW_2337 3 * rowA 9 9 3 + yW_2337 4 * rowA 9 9 4 + yW_2337 5 * rowA 9 9 5 + yW_2337 6 * rowA 9 9 6 + yW_2337 7 * rowA 9 9 7 + yW_2337 8 * rowA 9 9 8 = (0 : ℚ) := by
    norm_num [yW_2337, rowA]
  have hright : db_2337 9 9 = (0 : ℚ) := by
    norm_num [db_2337, dbmVal_2337]
  rw [hleft, hright]
  norm_num

theorem row_cap_2337_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 0 j q) ≤ db_2337 0 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_0_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_0_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_0_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_0_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_0_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_0_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_0_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_0_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_0_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_0_9

theorem row_cap_2337_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 1 j q) ≤ db_2337 1 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_1_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_1_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_1_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_1_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_1_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_1_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_1_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_1_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_1_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_1_9

theorem row_cap_2337_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 2 j q) ≤ db_2337 2 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_2_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_2_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_2_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_2_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_2_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_2_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_2_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_2_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_2_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_2_9

theorem row_cap_2337_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 3 j q) ≤ db_2337 3 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_3_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_3_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_3_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_3_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_3_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_3_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_3_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_3_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_3_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_3_9

theorem row_cap_2337_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 4 j q) ≤ db_2337 4 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_4_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_4_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_4_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_4_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_4_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_4_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_4_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_4_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_4_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_4_9

theorem row_cap_2337_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 5 j q) ≤ db_2337 5 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_5_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_5_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_5_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_5_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_5_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_5_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_5_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_5_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_5_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_5_9

theorem row_cap_2337_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 6 j q) ≤ db_2337 6 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_6_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_6_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_6_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_6_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_6_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_6_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_6_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_6_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_6_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_6_9

theorem row_cap_2337_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 7 j q) ≤ db_2337 7 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_7_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_7_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_7_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_7_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_7_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_7_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_7_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_7_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_7_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_7_9

theorem row_cap_2337_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 8 j q) ≤ db_2337 8 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_8_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_8_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_8_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_8_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_8_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_8_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_8_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_8_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_8_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_8_9

theorem row_cap_2337_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 9 j q) ≤ db_2337 9 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_9_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_9_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_9_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_9_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_9_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_9_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_9_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_9_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_9_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2337_9_9

theorem row_cap_2337 (i j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA i j q) ≤ db_2337 i j := by
  fin_cases i
  · exact row_cap_2337_0 j
  · exact row_cap_2337_1 j
  · exact row_cap_2337_2 j
  · exact row_cap_2337_3 j
  · exact row_cap_2337_4 j
  · exact row_cap_2337_5 j
  · exact row_cap_2337_6 j
  · exact row_cap_2337_7 j
  · exact row_cap_2337_8 j
  · exact row_cap_2337_9 j

def dbmVal_2341 : Fin 10 → Fin 10 → ℤ
  | i, j => ![
      ![0, 512, 512, 512, 1536, 2048, 3072, 3072, 3072, 4096],
      ![0, 0, 512, 512, 1536, 2048, 3072, 3072, 3072, 4096],
      ![0, 0, 0, 512, 1536, 2048, 3072, 3072, 3072, 4096],
      ![0, 0, 0, 0, 1536, 2048, 2560, 2560, 2560, 4096],
      ![-1024, -512, -512, -512, 0, 1024, 1536, 1536, 1536, 3072],
      ![-1024, -1024, -1024, -1024, 0, 0, 1024, 1024, 1024, 3072],
      ![-2048, -1536, -1536, -1536, -512, 0, 0, 1024, 1024, 2048],
      ![-2048, -2048, -2048, -2048, -1024, 0, 0, 0, 512, 2048],
      ![-2048, -2048, -2048, -2048, -1024, -512, 0, 0, 0, 2048],
      ![-4096, -3584, -3584, -3584, -2560, -2048, -1024, -1024, -1024, 0]
    ] i j

def db_2341 (i j : Fin 10) : ℚ := (dbmVal_2341 i j : ℚ) / 4096

theorem row_cap_2341_0_0 :
    yW_2341 0 * rowA 0 0 0 + yW_2341 1 * rowA 0 0 1 + yW_2341 2 * rowA 0 0 2 + yW_2341 3 * rowA 0 0 3 + yW_2341 4 * rowA 0 0 4 + yW_2341 5 * rowA 0 0 5 + yW_2341 6 * rowA 0 0 6 + yW_2341 7 * rowA 0 0 7 + yW_2341 8 * rowA 0 0 8 ≤ db_2341 0 0 := by
  have hleft : yW_2341 0 * rowA 0 0 0 + yW_2341 1 * rowA 0 0 1 + yW_2341 2 * rowA 0 0 2 + yW_2341 3 * rowA 0 0 3 + yW_2341 4 * rowA 0 0 4 + yW_2341 5 * rowA 0 0 5 + yW_2341 6 * rowA 0 0 6 + yW_2341 7 * rowA 0 0 7 + yW_2341 8 * rowA 0 0 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 0 0 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_0_1 :
    yW_2341 0 * rowA 0 1 0 + yW_2341 1 * rowA 0 1 1 + yW_2341 2 * rowA 0 1 2 + yW_2341 3 * rowA 0 1 3 + yW_2341 4 * rowA 0 1 4 + yW_2341 5 * rowA 0 1 5 + yW_2341 6 * rowA 0 1 6 + yW_2341 7 * rowA 0 1 7 + yW_2341 8 * rowA 0 1 8 ≤ db_2341 0 1 := by
  have hleft : yW_2341 0 * rowA 0 1 0 + yW_2341 1 * rowA 0 1 1 + yW_2341 2 * rowA 0 1 2 + yW_2341 3 * rowA 0 1 3 + yW_2341 4 * rowA 0 1 4 + yW_2341 5 * rowA 0 1 5 + yW_2341 6 * rowA 0 1 6 + yW_2341 7 * rowA 0 1 7 + yW_2341 8 * rowA 0 1 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 0 1 = (1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_0_2 :
    yW_2341 0 * rowA 0 2 0 + yW_2341 1 * rowA 0 2 1 + yW_2341 2 * rowA 0 2 2 + yW_2341 3 * rowA 0 2 3 + yW_2341 4 * rowA 0 2 4 + yW_2341 5 * rowA 0 2 5 + yW_2341 6 * rowA 0 2 6 + yW_2341 7 * rowA 0 2 7 + yW_2341 8 * rowA 0 2 8 ≤ db_2341 0 2 := by
  have hleft : yW_2341 0 * rowA 0 2 0 + yW_2341 1 * rowA 0 2 1 + yW_2341 2 * rowA 0 2 2 + yW_2341 3 * rowA 0 2 3 + yW_2341 4 * rowA 0 2 4 + yW_2341 5 * rowA 0 2 5 + yW_2341 6 * rowA 0 2 6 + yW_2341 7 * rowA 0 2 7 + yW_2341 8 * rowA 0 2 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 0 2 = (1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_0_3 :
    yW_2341 0 * rowA 0 3 0 + yW_2341 1 * rowA 0 3 1 + yW_2341 2 * rowA 0 3 2 + yW_2341 3 * rowA 0 3 3 + yW_2341 4 * rowA 0 3 4 + yW_2341 5 * rowA 0 3 5 + yW_2341 6 * rowA 0 3 6 + yW_2341 7 * rowA 0 3 7 + yW_2341 8 * rowA 0 3 8 ≤ db_2341 0 3 := by
  have hleft : yW_2341 0 * rowA 0 3 0 + yW_2341 1 * rowA 0 3 1 + yW_2341 2 * rowA 0 3 2 + yW_2341 3 * rowA 0 3 3 + yW_2341 4 * rowA 0 3 4 + yW_2341 5 * rowA 0 3 5 + yW_2341 6 * rowA 0 3 6 + yW_2341 7 * rowA 0 3 7 + yW_2341 8 * rowA 0 3 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 0 3 = (1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_0_4 :
    yW_2341 0 * rowA 0 4 0 + yW_2341 1 * rowA 0 4 1 + yW_2341 2 * rowA 0 4 2 + yW_2341 3 * rowA 0 4 3 + yW_2341 4 * rowA 0 4 4 + yW_2341 5 * rowA 0 4 5 + yW_2341 6 * rowA 0 4 6 + yW_2341 7 * rowA 0 4 7 + yW_2341 8 * rowA 0 4 8 ≤ db_2341 0 4 := by
  have hleft : yW_2341 0 * rowA 0 4 0 + yW_2341 1 * rowA 0 4 1 + yW_2341 2 * rowA 0 4 2 + yW_2341 3 * rowA 0 4 3 + yW_2341 4 * rowA 0 4 4 + yW_2341 5 * rowA 0 4 5 + yW_2341 6 * rowA 0 4 6 + yW_2341 7 * rowA 0 4 7 + yW_2341 8 * rowA 0 4 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 0 4 = (3 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_0_5 :
    yW_2341 0 * rowA 0 5 0 + yW_2341 1 * rowA 0 5 1 + yW_2341 2 * rowA 0 5 2 + yW_2341 3 * rowA 0 5 3 + yW_2341 4 * rowA 0 5 4 + yW_2341 5 * rowA 0 5 5 + yW_2341 6 * rowA 0 5 6 + yW_2341 7 * rowA 0 5 7 + yW_2341 8 * rowA 0 5 8 ≤ db_2341 0 5 := by
  have hleft : yW_2341 0 * rowA 0 5 0 + yW_2341 1 * rowA 0 5 1 + yW_2341 2 * rowA 0 5 2 + yW_2341 3 * rowA 0 5 3 + yW_2341 4 * rowA 0 5 4 + yW_2341 5 * rowA 0 5 5 + yW_2341 6 * rowA 0 5 6 + yW_2341 7 * rowA 0 5 7 + yW_2341 8 * rowA 0 5 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 0 5 = (1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_0_6 :
    yW_2341 0 * rowA 0 6 0 + yW_2341 1 * rowA 0 6 1 + yW_2341 2 * rowA 0 6 2 + yW_2341 3 * rowA 0 6 3 + yW_2341 4 * rowA 0 6 4 + yW_2341 5 * rowA 0 6 5 + yW_2341 6 * rowA 0 6 6 + yW_2341 7 * rowA 0 6 7 + yW_2341 8 * rowA 0 6 8 ≤ db_2341 0 6 := by
  have hleft : yW_2341 0 * rowA 0 6 0 + yW_2341 1 * rowA 0 6 1 + yW_2341 2 * rowA 0 6 2 + yW_2341 3 * rowA 0 6 3 + yW_2341 4 * rowA 0 6 4 + yW_2341 5 * rowA 0 6 5 + yW_2341 6 * rowA 0 6 6 + yW_2341 7 * rowA 0 6 7 + yW_2341 8 * rowA 0 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 0 6 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_0_7 :
    yW_2341 0 * rowA 0 7 0 + yW_2341 1 * rowA 0 7 1 + yW_2341 2 * rowA 0 7 2 + yW_2341 3 * rowA 0 7 3 + yW_2341 4 * rowA 0 7 4 + yW_2341 5 * rowA 0 7 5 + yW_2341 6 * rowA 0 7 6 + yW_2341 7 * rowA 0 7 7 + yW_2341 8 * rowA 0 7 8 ≤ db_2341 0 7 := by
  have hleft : yW_2341 0 * rowA 0 7 0 + yW_2341 1 * rowA 0 7 1 + yW_2341 2 * rowA 0 7 2 + yW_2341 3 * rowA 0 7 3 + yW_2341 4 * rowA 0 7 4 + yW_2341 5 * rowA 0 7 5 + yW_2341 6 * rowA 0 7 6 + yW_2341 7 * rowA 0 7 7 + yW_2341 8 * rowA 0 7 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 0 7 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_0_8 :
    yW_2341 0 * rowA 0 8 0 + yW_2341 1 * rowA 0 8 1 + yW_2341 2 * rowA 0 8 2 + yW_2341 3 * rowA 0 8 3 + yW_2341 4 * rowA 0 8 4 + yW_2341 5 * rowA 0 8 5 + yW_2341 6 * rowA 0 8 6 + yW_2341 7 * rowA 0 8 7 + yW_2341 8 * rowA 0 8 8 ≤ db_2341 0 8 := by
  have hleft : yW_2341 0 * rowA 0 8 0 + yW_2341 1 * rowA 0 8 1 + yW_2341 2 * rowA 0 8 2 + yW_2341 3 * rowA 0 8 3 + yW_2341 4 * rowA 0 8 4 + yW_2341 5 * rowA 0 8 5 + yW_2341 6 * rowA 0 8 6 + yW_2341 7 * rowA 0 8 7 + yW_2341 8 * rowA 0 8 8 = (3 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 0 8 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_0_9 :
    yW_2341 0 * rowA 0 9 0 + yW_2341 1 * rowA 0 9 1 + yW_2341 2 * rowA 0 9 2 + yW_2341 3 * rowA 0 9 3 + yW_2341 4 * rowA 0 9 4 + yW_2341 5 * rowA 0 9 5 + yW_2341 6 * rowA 0 9 6 + yW_2341 7 * rowA 0 9 7 + yW_2341 8 * rowA 0 9 8 ≤ db_2341 0 9 := by
  have hleft : yW_2341 0 * rowA 0 9 0 + yW_2341 1 * rowA 0 9 1 + yW_2341 2 * rowA 0 9 2 + yW_2341 3 * rowA 0 9 3 + yW_2341 4 * rowA 0 9 4 + yW_2341 5 * rowA 0 9 5 + yW_2341 6 * rowA 0 9 6 + yW_2341 7 * rowA 0 9 7 + yW_2341 8 * rowA 0 9 8 = (1 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 0 9 = (1 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_1_0 :
    yW_2341 0 * rowA 1 0 0 + yW_2341 1 * rowA 1 0 1 + yW_2341 2 * rowA 1 0 2 + yW_2341 3 * rowA 1 0 3 + yW_2341 4 * rowA 1 0 4 + yW_2341 5 * rowA 1 0 5 + yW_2341 6 * rowA 1 0 6 + yW_2341 7 * rowA 1 0 7 + yW_2341 8 * rowA 1 0 8 ≤ db_2341 1 0 := by
  have hleft : yW_2341 0 * rowA 1 0 0 + yW_2341 1 * rowA 1 0 1 + yW_2341 2 * rowA 1 0 2 + yW_2341 3 * rowA 1 0 3 + yW_2341 4 * rowA 1 0 4 + yW_2341 5 * rowA 1 0 5 + yW_2341 6 * rowA 1 0 6 + yW_2341 7 * rowA 1 0 7 + yW_2341 8 * rowA 1 0 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 1 0 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_1_1 :
    yW_2341 0 * rowA 1 1 0 + yW_2341 1 * rowA 1 1 1 + yW_2341 2 * rowA 1 1 2 + yW_2341 3 * rowA 1 1 3 + yW_2341 4 * rowA 1 1 4 + yW_2341 5 * rowA 1 1 5 + yW_2341 6 * rowA 1 1 6 + yW_2341 7 * rowA 1 1 7 + yW_2341 8 * rowA 1 1 8 ≤ db_2341 1 1 := by
  have hleft : yW_2341 0 * rowA 1 1 0 + yW_2341 1 * rowA 1 1 1 + yW_2341 2 * rowA 1 1 2 + yW_2341 3 * rowA 1 1 3 + yW_2341 4 * rowA 1 1 4 + yW_2341 5 * rowA 1 1 5 + yW_2341 6 * rowA 1 1 6 + yW_2341 7 * rowA 1 1 7 + yW_2341 8 * rowA 1 1 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 1 1 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_1_2 :
    yW_2341 0 * rowA 1 2 0 + yW_2341 1 * rowA 1 2 1 + yW_2341 2 * rowA 1 2 2 + yW_2341 3 * rowA 1 2 3 + yW_2341 4 * rowA 1 2 4 + yW_2341 5 * rowA 1 2 5 + yW_2341 6 * rowA 1 2 6 + yW_2341 7 * rowA 1 2 7 + yW_2341 8 * rowA 1 2 8 ≤ db_2341 1 2 := by
  have hleft : yW_2341 0 * rowA 1 2 0 + yW_2341 1 * rowA 1 2 1 + yW_2341 2 * rowA 1 2 2 + yW_2341 3 * rowA 1 2 3 + yW_2341 4 * rowA 1 2 4 + yW_2341 5 * rowA 1 2 5 + yW_2341 6 * rowA 1 2 6 + yW_2341 7 * rowA 1 2 7 + yW_2341 8 * rowA 1 2 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 1 2 = (1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_1_3 :
    yW_2341 0 * rowA 1 3 0 + yW_2341 1 * rowA 1 3 1 + yW_2341 2 * rowA 1 3 2 + yW_2341 3 * rowA 1 3 3 + yW_2341 4 * rowA 1 3 4 + yW_2341 5 * rowA 1 3 5 + yW_2341 6 * rowA 1 3 6 + yW_2341 7 * rowA 1 3 7 + yW_2341 8 * rowA 1 3 8 ≤ db_2341 1 3 := by
  have hleft : yW_2341 0 * rowA 1 3 0 + yW_2341 1 * rowA 1 3 1 + yW_2341 2 * rowA 1 3 2 + yW_2341 3 * rowA 1 3 3 + yW_2341 4 * rowA 1 3 4 + yW_2341 5 * rowA 1 3 5 + yW_2341 6 * rowA 1 3 6 + yW_2341 7 * rowA 1 3 7 + yW_2341 8 * rowA 1 3 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 1 3 = (1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_1_4 :
    yW_2341 0 * rowA 1 4 0 + yW_2341 1 * rowA 1 4 1 + yW_2341 2 * rowA 1 4 2 + yW_2341 3 * rowA 1 4 3 + yW_2341 4 * rowA 1 4 4 + yW_2341 5 * rowA 1 4 5 + yW_2341 6 * rowA 1 4 6 + yW_2341 7 * rowA 1 4 7 + yW_2341 8 * rowA 1 4 8 ≤ db_2341 1 4 := by
  have hleft : yW_2341 0 * rowA 1 4 0 + yW_2341 1 * rowA 1 4 1 + yW_2341 2 * rowA 1 4 2 + yW_2341 3 * rowA 1 4 3 + yW_2341 4 * rowA 1 4 4 + yW_2341 5 * rowA 1 4 5 + yW_2341 6 * rowA 1 4 6 + yW_2341 7 * rowA 1 4 7 + yW_2341 8 * rowA 1 4 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 1 4 = (3 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_1_5 :
    yW_2341 0 * rowA 1 5 0 + yW_2341 1 * rowA 1 5 1 + yW_2341 2 * rowA 1 5 2 + yW_2341 3 * rowA 1 5 3 + yW_2341 4 * rowA 1 5 4 + yW_2341 5 * rowA 1 5 5 + yW_2341 6 * rowA 1 5 6 + yW_2341 7 * rowA 1 5 7 + yW_2341 8 * rowA 1 5 8 ≤ db_2341 1 5 := by
  have hleft : yW_2341 0 * rowA 1 5 0 + yW_2341 1 * rowA 1 5 1 + yW_2341 2 * rowA 1 5 2 + yW_2341 3 * rowA 1 5 3 + yW_2341 4 * rowA 1 5 4 + yW_2341 5 * rowA 1 5 5 + yW_2341 6 * rowA 1 5 6 + yW_2341 7 * rowA 1 5 7 + yW_2341 8 * rowA 1 5 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 1 5 = (1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_1_6 :
    yW_2341 0 * rowA 1 6 0 + yW_2341 1 * rowA 1 6 1 + yW_2341 2 * rowA 1 6 2 + yW_2341 3 * rowA 1 6 3 + yW_2341 4 * rowA 1 6 4 + yW_2341 5 * rowA 1 6 5 + yW_2341 6 * rowA 1 6 6 + yW_2341 7 * rowA 1 6 7 + yW_2341 8 * rowA 1 6 8 ≤ db_2341 1 6 := by
  have hleft : yW_2341 0 * rowA 1 6 0 + yW_2341 1 * rowA 1 6 1 + yW_2341 2 * rowA 1 6 2 + yW_2341 3 * rowA 1 6 3 + yW_2341 4 * rowA 1 6 4 + yW_2341 5 * rowA 1 6 5 + yW_2341 6 * rowA 1 6 6 + yW_2341 7 * rowA 1 6 7 + yW_2341 8 * rowA 1 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 1 6 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_1_7 :
    yW_2341 0 * rowA 1 7 0 + yW_2341 1 * rowA 1 7 1 + yW_2341 2 * rowA 1 7 2 + yW_2341 3 * rowA 1 7 3 + yW_2341 4 * rowA 1 7 4 + yW_2341 5 * rowA 1 7 5 + yW_2341 6 * rowA 1 7 6 + yW_2341 7 * rowA 1 7 7 + yW_2341 8 * rowA 1 7 8 ≤ db_2341 1 7 := by
  have hleft : yW_2341 0 * rowA 1 7 0 + yW_2341 1 * rowA 1 7 1 + yW_2341 2 * rowA 1 7 2 + yW_2341 3 * rowA 1 7 3 + yW_2341 4 * rowA 1 7 4 + yW_2341 5 * rowA 1 7 5 + yW_2341 6 * rowA 1 7 6 + yW_2341 7 * rowA 1 7 7 + yW_2341 8 * rowA 1 7 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 1 7 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_1_8 :
    yW_2341 0 * rowA 1 8 0 + yW_2341 1 * rowA 1 8 1 + yW_2341 2 * rowA 1 8 2 + yW_2341 3 * rowA 1 8 3 + yW_2341 4 * rowA 1 8 4 + yW_2341 5 * rowA 1 8 5 + yW_2341 6 * rowA 1 8 6 + yW_2341 7 * rowA 1 8 7 + yW_2341 8 * rowA 1 8 8 ≤ db_2341 1 8 := by
  have hleft : yW_2341 0 * rowA 1 8 0 + yW_2341 1 * rowA 1 8 1 + yW_2341 2 * rowA 1 8 2 + yW_2341 3 * rowA 1 8 3 + yW_2341 4 * rowA 1 8 4 + yW_2341 5 * rowA 1 8 5 + yW_2341 6 * rowA 1 8 6 + yW_2341 7 * rowA 1 8 7 + yW_2341 8 * rowA 1 8 8 = (3 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 1 8 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_1_9 :
    yW_2341 0 * rowA 1 9 0 + yW_2341 1 * rowA 1 9 1 + yW_2341 2 * rowA 1 9 2 + yW_2341 3 * rowA 1 9 3 + yW_2341 4 * rowA 1 9 4 + yW_2341 5 * rowA 1 9 5 + yW_2341 6 * rowA 1 9 6 + yW_2341 7 * rowA 1 9 7 + yW_2341 8 * rowA 1 9 8 ≤ db_2341 1 9 := by
  have hleft : yW_2341 0 * rowA 1 9 0 + yW_2341 1 * rowA 1 9 1 + yW_2341 2 * rowA 1 9 2 + yW_2341 3 * rowA 1 9 3 + yW_2341 4 * rowA 1 9 4 + yW_2341 5 * rowA 1 9 5 + yW_2341 6 * rowA 1 9 6 + yW_2341 7 * rowA 1 9 7 + yW_2341 8 * rowA 1 9 8 = (1 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 1 9 = (1 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_2_0 :
    yW_2341 0 * rowA 2 0 0 + yW_2341 1 * rowA 2 0 1 + yW_2341 2 * rowA 2 0 2 + yW_2341 3 * rowA 2 0 3 + yW_2341 4 * rowA 2 0 4 + yW_2341 5 * rowA 2 0 5 + yW_2341 6 * rowA 2 0 6 + yW_2341 7 * rowA 2 0 7 + yW_2341 8 * rowA 2 0 8 ≤ db_2341 2 0 := by
  have hleft : yW_2341 0 * rowA 2 0 0 + yW_2341 1 * rowA 2 0 1 + yW_2341 2 * rowA 2 0 2 + yW_2341 3 * rowA 2 0 3 + yW_2341 4 * rowA 2 0 4 + yW_2341 5 * rowA 2 0 5 + yW_2341 6 * rowA 2 0 6 + yW_2341 7 * rowA 2 0 7 + yW_2341 8 * rowA 2 0 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 2 0 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_2_1 :
    yW_2341 0 * rowA 2 1 0 + yW_2341 1 * rowA 2 1 1 + yW_2341 2 * rowA 2 1 2 + yW_2341 3 * rowA 2 1 3 + yW_2341 4 * rowA 2 1 4 + yW_2341 5 * rowA 2 1 5 + yW_2341 6 * rowA 2 1 6 + yW_2341 7 * rowA 2 1 7 + yW_2341 8 * rowA 2 1 8 ≤ db_2341 2 1 := by
  have hleft : yW_2341 0 * rowA 2 1 0 + yW_2341 1 * rowA 2 1 1 + yW_2341 2 * rowA 2 1 2 + yW_2341 3 * rowA 2 1 3 + yW_2341 4 * rowA 2 1 4 + yW_2341 5 * rowA 2 1 5 + yW_2341 6 * rowA 2 1 6 + yW_2341 7 * rowA 2 1 7 + yW_2341 8 * rowA 2 1 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 2 1 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_2_2 :
    yW_2341 0 * rowA 2 2 0 + yW_2341 1 * rowA 2 2 1 + yW_2341 2 * rowA 2 2 2 + yW_2341 3 * rowA 2 2 3 + yW_2341 4 * rowA 2 2 4 + yW_2341 5 * rowA 2 2 5 + yW_2341 6 * rowA 2 2 6 + yW_2341 7 * rowA 2 2 7 + yW_2341 8 * rowA 2 2 8 ≤ db_2341 2 2 := by
  have hleft : yW_2341 0 * rowA 2 2 0 + yW_2341 1 * rowA 2 2 1 + yW_2341 2 * rowA 2 2 2 + yW_2341 3 * rowA 2 2 3 + yW_2341 4 * rowA 2 2 4 + yW_2341 5 * rowA 2 2 5 + yW_2341 6 * rowA 2 2 6 + yW_2341 7 * rowA 2 2 7 + yW_2341 8 * rowA 2 2 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 2 2 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_2_3 :
    yW_2341 0 * rowA 2 3 0 + yW_2341 1 * rowA 2 3 1 + yW_2341 2 * rowA 2 3 2 + yW_2341 3 * rowA 2 3 3 + yW_2341 4 * rowA 2 3 4 + yW_2341 5 * rowA 2 3 5 + yW_2341 6 * rowA 2 3 6 + yW_2341 7 * rowA 2 3 7 + yW_2341 8 * rowA 2 3 8 ≤ db_2341 2 3 := by
  have hleft : yW_2341 0 * rowA 2 3 0 + yW_2341 1 * rowA 2 3 1 + yW_2341 2 * rowA 2 3 2 + yW_2341 3 * rowA 2 3 3 + yW_2341 4 * rowA 2 3 4 + yW_2341 5 * rowA 2 3 5 + yW_2341 6 * rowA 2 3 6 + yW_2341 7 * rowA 2 3 7 + yW_2341 8 * rowA 2 3 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 2 3 = (1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_2_4 :
    yW_2341 0 * rowA 2 4 0 + yW_2341 1 * rowA 2 4 1 + yW_2341 2 * rowA 2 4 2 + yW_2341 3 * rowA 2 4 3 + yW_2341 4 * rowA 2 4 4 + yW_2341 5 * rowA 2 4 5 + yW_2341 6 * rowA 2 4 6 + yW_2341 7 * rowA 2 4 7 + yW_2341 8 * rowA 2 4 8 ≤ db_2341 2 4 := by
  have hleft : yW_2341 0 * rowA 2 4 0 + yW_2341 1 * rowA 2 4 1 + yW_2341 2 * rowA 2 4 2 + yW_2341 3 * rowA 2 4 3 + yW_2341 4 * rowA 2 4 4 + yW_2341 5 * rowA 2 4 5 + yW_2341 6 * rowA 2 4 6 + yW_2341 7 * rowA 2 4 7 + yW_2341 8 * rowA 2 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 2 4 = (3 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_2_5 :
    yW_2341 0 * rowA 2 5 0 + yW_2341 1 * rowA 2 5 1 + yW_2341 2 * rowA 2 5 2 + yW_2341 3 * rowA 2 5 3 + yW_2341 4 * rowA 2 5 4 + yW_2341 5 * rowA 2 5 5 + yW_2341 6 * rowA 2 5 6 + yW_2341 7 * rowA 2 5 7 + yW_2341 8 * rowA 2 5 8 ≤ db_2341 2 5 := by
  have hleft : yW_2341 0 * rowA 2 5 0 + yW_2341 1 * rowA 2 5 1 + yW_2341 2 * rowA 2 5 2 + yW_2341 3 * rowA 2 5 3 + yW_2341 4 * rowA 2 5 4 + yW_2341 5 * rowA 2 5 5 + yW_2341 6 * rowA 2 5 6 + yW_2341 7 * rowA 2 5 7 + yW_2341 8 * rowA 2 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 2 5 = (1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_2_6 :
    yW_2341 0 * rowA 2 6 0 + yW_2341 1 * rowA 2 6 1 + yW_2341 2 * rowA 2 6 2 + yW_2341 3 * rowA 2 6 3 + yW_2341 4 * rowA 2 6 4 + yW_2341 5 * rowA 2 6 5 + yW_2341 6 * rowA 2 6 6 + yW_2341 7 * rowA 2 6 7 + yW_2341 8 * rowA 2 6 8 ≤ db_2341 2 6 := by
  have hleft : yW_2341 0 * rowA 2 6 0 + yW_2341 1 * rowA 2 6 1 + yW_2341 2 * rowA 2 6 2 + yW_2341 3 * rowA 2 6 3 + yW_2341 4 * rowA 2 6 4 + yW_2341 5 * rowA 2 6 5 + yW_2341 6 * rowA 2 6 6 + yW_2341 7 * rowA 2 6 7 + yW_2341 8 * rowA 2 6 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 2 6 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_2_7 :
    yW_2341 0 * rowA 2 7 0 + yW_2341 1 * rowA 2 7 1 + yW_2341 2 * rowA 2 7 2 + yW_2341 3 * rowA 2 7 3 + yW_2341 4 * rowA 2 7 4 + yW_2341 5 * rowA 2 7 5 + yW_2341 6 * rowA 2 7 6 + yW_2341 7 * rowA 2 7 7 + yW_2341 8 * rowA 2 7 8 ≤ db_2341 2 7 := by
  have hleft : yW_2341 0 * rowA 2 7 0 + yW_2341 1 * rowA 2 7 1 + yW_2341 2 * rowA 2 7 2 + yW_2341 3 * rowA 2 7 3 + yW_2341 4 * rowA 2 7 4 + yW_2341 5 * rowA 2 7 5 + yW_2341 6 * rowA 2 7 6 + yW_2341 7 * rowA 2 7 7 + yW_2341 8 * rowA 2 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 2 7 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_2_8 :
    yW_2341 0 * rowA 2 8 0 + yW_2341 1 * rowA 2 8 1 + yW_2341 2 * rowA 2 8 2 + yW_2341 3 * rowA 2 8 3 + yW_2341 4 * rowA 2 8 4 + yW_2341 5 * rowA 2 8 5 + yW_2341 6 * rowA 2 8 6 + yW_2341 7 * rowA 2 8 7 + yW_2341 8 * rowA 2 8 8 ≤ db_2341 2 8 := by
  have hleft : yW_2341 0 * rowA 2 8 0 + yW_2341 1 * rowA 2 8 1 + yW_2341 2 * rowA 2 8 2 + yW_2341 3 * rowA 2 8 3 + yW_2341 4 * rowA 2 8 4 + yW_2341 5 * rowA 2 8 5 + yW_2341 6 * rowA 2 8 6 + yW_2341 7 * rowA 2 8 7 + yW_2341 8 * rowA 2 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 2 8 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_2_9 :
    yW_2341 0 * rowA 2 9 0 + yW_2341 1 * rowA 2 9 1 + yW_2341 2 * rowA 2 9 2 + yW_2341 3 * rowA 2 9 3 + yW_2341 4 * rowA 2 9 4 + yW_2341 5 * rowA 2 9 5 + yW_2341 6 * rowA 2 9 6 + yW_2341 7 * rowA 2 9 7 + yW_2341 8 * rowA 2 9 8 ≤ db_2341 2 9 := by
  have hleft : yW_2341 0 * rowA 2 9 0 + yW_2341 1 * rowA 2 9 1 + yW_2341 2 * rowA 2 9 2 + yW_2341 3 * rowA 2 9 3 + yW_2341 4 * rowA 2 9 4 + yW_2341 5 * rowA 2 9 5 + yW_2341 6 * rowA 2 9 6 + yW_2341 7 * rowA 2 9 7 + yW_2341 8 * rowA 2 9 8 = (7 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 2 9 = (1 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_3_0 :
    yW_2341 0 * rowA 3 0 0 + yW_2341 1 * rowA 3 0 1 + yW_2341 2 * rowA 3 0 2 + yW_2341 3 * rowA 3 0 3 + yW_2341 4 * rowA 3 0 4 + yW_2341 5 * rowA 3 0 5 + yW_2341 6 * rowA 3 0 6 + yW_2341 7 * rowA 3 0 7 + yW_2341 8 * rowA 3 0 8 ≤ db_2341 3 0 := by
  have hleft : yW_2341 0 * rowA 3 0 0 + yW_2341 1 * rowA 3 0 1 + yW_2341 2 * rowA 3 0 2 + yW_2341 3 * rowA 3 0 3 + yW_2341 4 * rowA 3 0 4 + yW_2341 5 * rowA 3 0 5 + yW_2341 6 * rowA 3 0 6 + yW_2341 7 * rowA 3 0 7 + yW_2341 8 * rowA 3 0 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 3 0 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_3_1 :
    yW_2341 0 * rowA 3 1 0 + yW_2341 1 * rowA 3 1 1 + yW_2341 2 * rowA 3 1 2 + yW_2341 3 * rowA 3 1 3 + yW_2341 4 * rowA 3 1 4 + yW_2341 5 * rowA 3 1 5 + yW_2341 6 * rowA 3 1 6 + yW_2341 7 * rowA 3 1 7 + yW_2341 8 * rowA 3 1 8 ≤ db_2341 3 1 := by
  have hleft : yW_2341 0 * rowA 3 1 0 + yW_2341 1 * rowA 3 1 1 + yW_2341 2 * rowA 3 1 2 + yW_2341 3 * rowA 3 1 3 + yW_2341 4 * rowA 3 1 4 + yW_2341 5 * rowA 3 1 5 + yW_2341 6 * rowA 3 1 6 + yW_2341 7 * rowA 3 1 7 + yW_2341 8 * rowA 3 1 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 3 1 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_3_2 :
    yW_2341 0 * rowA 3 2 0 + yW_2341 1 * rowA 3 2 1 + yW_2341 2 * rowA 3 2 2 + yW_2341 3 * rowA 3 2 3 + yW_2341 4 * rowA 3 2 4 + yW_2341 5 * rowA 3 2 5 + yW_2341 6 * rowA 3 2 6 + yW_2341 7 * rowA 3 2 7 + yW_2341 8 * rowA 3 2 8 ≤ db_2341 3 2 := by
  have hleft : yW_2341 0 * rowA 3 2 0 + yW_2341 1 * rowA 3 2 1 + yW_2341 2 * rowA 3 2 2 + yW_2341 3 * rowA 3 2 3 + yW_2341 4 * rowA 3 2 4 + yW_2341 5 * rowA 3 2 5 + yW_2341 6 * rowA 3 2 6 + yW_2341 7 * rowA 3 2 7 + yW_2341 8 * rowA 3 2 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 3 2 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_3_3 :
    yW_2341 0 * rowA 3 3 0 + yW_2341 1 * rowA 3 3 1 + yW_2341 2 * rowA 3 3 2 + yW_2341 3 * rowA 3 3 3 + yW_2341 4 * rowA 3 3 4 + yW_2341 5 * rowA 3 3 5 + yW_2341 6 * rowA 3 3 6 + yW_2341 7 * rowA 3 3 7 + yW_2341 8 * rowA 3 3 8 ≤ db_2341 3 3 := by
  have hleft : yW_2341 0 * rowA 3 3 0 + yW_2341 1 * rowA 3 3 1 + yW_2341 2 * rowA 3 3 2 + yW_2341 3 * rowA 3 3 3 + yW_2341 4 * rowA 3 3 4 + yW_2341 5 * rowA 3 3 5 + yW_2341 6 * rowA 3 3 6 + yW_2341 7 * rowA 3 3 7 + yW_2341 8 * rowA 3 3 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 3 3 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_3_4 :
    yW_2341 0 * rowA 3 4 0 + yW_2341 1 * rowA 3 4 1 + yW_2341 2 * rowA 3 4 2 + yW_2341 3 * rowA 3 4 3 + yW_2341 4 * rowA 3 4 4 + yW_2341 5 * rowA 3 4 5 + yW_2341 6 * rowA 3 4 6 + yW_2341 7 * rowA 3 4 7 + yW_2341 8 * rowA 3 4 8 ≤ db_2341 3 4 := by
  have hleft : yW_2341 0 * rowA 3 4 0 + yW_2341 1 * rowA 3 4 1 + yW_2341 2 * rowA 3 4 2 + yW_2341 3 * rowA 3 4 3 + yW_2341 4 * rowA 3 4 4 + yW_2341 5 * rowA 3 4 5 + yW_2341 6 * rowA 3 4 6 + yW_2341 7 * rowA 3 4 7 + yW_2341 8 * rowA 3 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 3 4 = (3 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_3_5 :
    yW_2341 0 * rowA 3 5 0 + yW_2341 1 * rowA 3 5 1 + yW_2341 2 * rowA 3 5 2 + yW_2341 3 * rowA 3 5 3 + yW_2341 4 * rowA 3 5 4 + yW_2341 5 * rowA 3 5 5 + yW_2341 6 * rowA 3 5 6 + yW_2341 7 * rowA 3 5 7 + yW_2341 8 * rowA 3 5 8 ≤ db_2341 3 5 := by
  have hleft : yW_2341 0 * rowA 3 5 0 + yW_2341 1 * rowA 3 5 1 + yW_2341 2 * rowA 3 5 2 + yW_2341 3 * rowA 3 5 3 + yW_2341 4 * rowA 3 5 4 + yW_2341 5 * rowA 3 5 5 + yW_2341 6 * rowA 3 5 6 + yW_2341 7 * rowA 3 5 7 + yW_2341 8 * rowA 3 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 3 5 = (1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_3_6 :
    yW_2341 0 * rowA 3 6 0 + yW_2341 1 * rowA 3 6 1 + yW_2341 2 * rowA 3 6 2 + yW_2341 3 * rowA 3 6 3 + yW_2341 4 * rowA 3 6 4 + yW_2341 5 * rowA 3 6 5 + yW_2341 6 * rowA 3 6 6 + yW_2341 7 * rowA 3 6 7 + yW_2341 8 * rowA 3 6 8 ≤ db_2341 3 6 := by
  have hleft : yW_2341 0 * rowA 3 6 0 + yW_2341 1 * rowA 3 6 1 + yW_2341 2 * rowA 3 6 2 + yW_2341 3 * rowA 3 6 3 + yW_2341 4 * rowA 3 6 4 + yW_2341 5 * rowA 3 6 5 + yW_2341 6 * rowA 3 6 6 + yW_2341 7 * rowA 3 6 7 + yW_2341 8 * rowA 3 6 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 3 6 = (5 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_3_7 :
    yW_2341 0 * rowA 3 7 0 + yW_2341 1 * rowA 3 7 1 + yW_2341 2 * rowA 3 7 2 + yW_2341 3 * rowA 3 7 3 + yW_2341 4 * rowA 3 7 4 + yW_2341 5 * rowA 3 7 5 + yW_2341 6 * rowA 3 7 6 + yW_2341 7 * rowA 3 7 7 + yW_2341 8 * rowA 3 7 8 ≤ db_2341 3 7 := by
  have hleft : yW_2341 0 * rowA 3 7 0 + yW_2341 1 * rowA 3 7 1 + yW_2341 2 * rowA 3 7 2 + yW_2341 3 * rowA 3 7 3 + yW_2341 4 * rowA 3 7 4 + yW_2341 5 * rowA 3 7 5 + yW_2341 6 * rowA 3 7 6 + yW_2341 7 * rowA 3 7 7 + yW_2341 8 * rowA 3 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 3 7 = (5 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_3_8 :
    yW_2341 0 * rowA 3 8 0 + yW_2341 1 * rowA 3 8 1 + yW_2341 2 * rowA 3 8 2 + yW_2341 3 * rowA 3 8 3 + yW_2341 4 * rowA 3 8 4 + yW_2341 5 * rowA 3 8 5 + yW_2341 6 * rowA 3 8 6 + yW_2341 7 * rowA 3 8 7 + yW_2341 8 * rowA 3 8 8 ≤ db_2341 3 8 := by
  have hleft : yW_2341 0 * rowA 3 8 0 + yW_2341 1 * rowA 3 8 1 + yW_2341 2 * rowA 3 8 2 + yW_2341 3 * rowA 3 8 3 + yW_2341 4 * rowA 3 8 4 + yW_2341 5 * rowA 3 8 5 + yW_2341 6 * rowA 3 8 6 + yW_2341 7 * rowA 3 8 7 + yW_2341 8 * rowA 3 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 3 8 = (5 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_3_9 :
    yW_2341 0 * rowA 3 9 0 + yW_2341 1 * rowA 3 9 1 + yW_2341 2 * rowA 3 9 2 + yW_2341 3 * rowA 3 9 3 + yW_2341 4 * rowA 3 9 4 + yW_2341 5 * rowA 3 9 5 + yW_2341 6 * rowA 3 9 6 + yW_2341 7 * rowA 3 9 7 + yW_2341 8 * rowA 3 9 8 ≤ db_2341 3 9 := by
  have hleft : yW_2341 0 * rowA 3 9 0 + yW_2341 1 * rowA 3 9 1 + yW_2341 2 * rowA 3 9 2 + yW_2341 3 * rowA 3 9 3 + yW_2341 4 * rowA 3 9 4 + yW_2341 5 * rowA 3 9 5 + yW_2341 6 * rowA 3 9 6 + yW_2341 7 * rowA 3 9 7 + yW_2341 8 * rowA 3 9 8 = (7 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 3 9 = (1 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_4_0 :
    yW_2341 0 * rowA 4 0 0 + yW_2341 1 * rowA 4 0 1 + yW_2341 2 * rowA 4 0 2 + yW_2341 3 * rowA 4 0 3 + yW_2341 4 * rowA 4 0 4 + yW_2341 5 * rowA 4 0 5 + yW_2341 6 * rowA 4 0 6 + yW_2341 7 * rowA 4 0 7 + yW_2341 8 * rowA 4 0 8 ≤ db_2341 4 0 := by
  have hleft : yW_2341 0 * rowA 4 0 0 + yW_2341 1 * rowA 4 0 1 + yW_2341 2 * rowA 4 0 2 + yW_2341 3 * rowA 4 0 3 + yW_2341 4 * rowA 4 0 4 + yW_2341 5 * rowA 4 0 5 + yW_2341 6 * rowA 4 0 6 + yW_2341 7 * rowA 4 0 7 + yW_2341 8 * rowA 4 0 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 4 0 = (-1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_4_1 :
    yW_2341 0 * rowA 4 1 0 + yW_2341 1 * rowA 4 1 1 + yW_2341 2 * rowA 4 1 2 + yW_2341 3 * rowA 4 1 3 + yW_2341 4 * rowA 4 1 4 + yW_2341 5 * rowA 4 1 5 + yW_2341 6 * rowA 4 1 6 + yW_2341 7 * rowA 4 1 7 + yW_2341 8 * rowA 4 1 8 ≤ db_2341 4 1 := by
  have hleft : yW_2341 0 * rowA 4 1 0 + yW_2341 1 * rowA 4 1 1 + yW_2341 2 * rowA 4 1 2 + yW_2341 3 * rowA 4 1 3 + yW_2341 4 * rowA 4 1 4 + yW_2341 5 * rowA 4 1 5 + yW_2341 6 * rowA 4 1 6 + yW_2341 7 * rowA 4 1 7 + yW_2341 8 * rowA 4 1 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 4 1 = (-1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_4_2 :
    yW_2341 0 * rowA 4 2 0 + yW_2341 1 * rowA 4 2 1 + yW_2341 2 * rowA 4 2 2 + yW_2341 3 * rowA 4 2 3 + yW_2341 4 * rowA 4 2 4 + yW_2341 5 * rowA 4 2 5 + yW_2341 6 * rowA 4 2 6 + yW_2341 7 * rowA 4 2 7 + yW_2341 8 * rowA 4 2 8 ≤ db_2341 4 2 := by
  have hleft : yW_2341 0 * rowA 4 2 0 + yW_2341 1 * rowA 4 2 1 + yW_2341 2 * rowA 4 2 2 + yW_2341 3 * rowA 4 2 3 + yW_2341 4 * rowA 4 2 4 + yW_2341 5 * rowA 4 2 5 + yW_2341 6 * rowA 4 2 6 + yW_2341 7 * rowA 4 2 7 + yW_2341 8 * rowA 4 2 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 4 2 = (-1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_4_3 :
    yW_2341 0 * rowA 4 3 0 + yW_2341 1 * rowA 4 3 1 + yW_2341 2 * rowA 4 3 2 + yW_2341 3 * rowA 4 3 3 + yW_2341 4 * rowA 4 3 4 + yW_2341 5 * rowA 4 3 5 + yW_2341 6 * rowA 4 3 6 + yW_2341 7 * rowA 4 3 7 + yW_2341 8 * rowA 4 3 8 ≤ db_2341 4 3 := by
  have hleft : yW_2341 0 * rowA 4 3 0 + yW_2341 1 * rowA 4 3 1 + yW_2341 2 * rowA 4 3 2 + yW_2341 3 * rowA 4 3 3 + yW_2341 4 * rowA 4 3 4 + yW_2341 5 * rowA 4 3 5 + yW_2341 6 * rowA 4 3 6 + yW_2341 7 * rowA 4 3 7 + yW_2341 8 * rowA 4 3 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 4 3 = (-1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_4_4 :
    yW_2341 0 * rowA 4 4 0 + yW_2341 1 * rowA 4 4 1 + yW_2341 2 * rowA 4 4 2 + yW_2341 3 * rowA 4 4 3 + yW_2341 4 * rowA 4 4 4 + yW_2341 5 * rowA 4 4 5 + yW_2341 6 * rowA 4 4 6 + yW_2341 7 * rowA 4 4 7 + yW_2341 8 * rowA 4 4 8 ≤ db_2341 4 4 := by
  have hleft : yW_2341 0 * rowA 4 4 0 + yW_2341 1 * rowA 4 4 1 + yW_2341 2 * rowA 4 4 2 + yW_2341 3 * rowA 4 4 3 + yW_2341 4 * rowA 4 4 4 + yW_2341 5 * rowA 4 4 5 + yW_2341 6 * rowA 4 4 6 + yW_2341 7 * rowA 4 4 7 + yW_2341 8 * rowA 4 4 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 4 4 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_4_5 :
    yW_2341 0 * rowA 4 5 0 + yW_2341 1 * rowA 4 5 1 + yW_2341 2 * rowA 4 5 2 + yW_2341 3 * rowA 4 5 3 + yW_2341 4 * rowA 4 5 4 + yW_2341 5 * rowA 4 5 5 + yW_2341 6 * rowA 4 5 6 + yW_2341 7 * rowA 4 5 7 + yW_2341 8 * rowA 4 5 8 ≤ db_2341 4 5 := by
  have hleft : yW_2341 0 * rowA 4 5 0 + yW_2341 1 * rowA 4 5 1 + yW_2341 2 * rowA 4 5 2 + yW_2341 3 * rowA 4 5 3 + yW_2341 4 * rowA 4 5 4 + yW_2341 5 * rowA 4 5 5 + yW_2341 6 * rowA 4 5 6 + yW_2341 7 * rowA 4 5 7 + yW_2341 8 * rowA 4 5 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 4 5 = (1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_4_6 :
    yW_2341 0 * rowA 4 6 0 + yW_2341 1 * rowA 4 6 1 + yW_2341 2 * rowA 4 6 2 + yW_2341 3 * rowA 4 6 3 + yW_2341 4 * rowA 4 6 4 + yW_2341 5 * rowA 4 6 5 + yW_2341 6 * rowA 4 6 6 + yW_2341 7 * rowA 4 6 7 + yW_2341 8 * rowA 4 6 8 ≤ db_2341 4 6 := by
  have hleft : yW_2341 0 * rowA 4 6 0 + yW_2341 1 * rowA 4 6 1 + yW_2341 2 * rowA 4 6 2 + yW_2341 3 * rowA 4 6 3 + yW_2341 4 * rowA 4 6 4 + yW_2341 5 * rowA 4 6 5 + yW_2341 6 * rowA 4 6 6 + yW_2341 7 * rowA 4 6 7 + yW_2341 8 * rowA 4 6 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 4 6 = (3 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_4_7 :
    yW_2341 0 * rowA 4 7 0 + yW_2341 1 * rowA 4 7 1 + yW_2341 2 * rowA 4 7 2 + yW_2341 3 * rowA 4 7 3 + yW_2341 4 * rowA 4 7 4 + yW_2341 5 * rowA 4 7 5 + yW_2341 6 * rowA 4 7 6 + yW_2341 7 * rowA 4 7 7 + yW_2341 8 * rowA 4 7 8 ≤ db_2341 4 7 := by
  have hleft : yW_2341 0 * rowA 4 7 0 + yW_2341 1 * rowA 4 7 1 + yW_2341 2 * rowA 4 7 2 + yW_2341 3 * rowA 4 7 3 + yW_2341 4 * rowA 4 7 4 + yW_2341 5 * rowA 4 7 5 + yW_2341 6 * rowA 4 7 6 + yW_2341 7 * rowA 4 7 7 + yW_2341 8 * rowA 4 7 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 4 7 = (3 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_4_8 :
    yW_2341 0 * rowA 4 8 0 + yW_2341 1 * rowA 4 8 1 + yW_2341 2 * rowA 4 8 2 + yW_2341 3 * rowA 4 8 3 + yW_2341 4 * rowA 4 8 4 + yW_2341 5 * rowA 4 8 5 + yW_2341 6 * rowA 4 8 6 + yW_2341 7 * rowA 4 8 7 + yW_2341 8 * rowA 4 8 8 ≤ db_2341 4 8 := by
  have hleft : yW_2341 0 * rowA 4 8 0 + yW_2341 1 * rowA 4 8 1 + yW_2341 2 * rowA 4 8 2 + yW_2341 3 * rowA 4 8 3 + yW_2341 4 * rowA 4 8 4 + yW_2341 5 * rowA 4 8 5 + yW_2341 6 * rowA 4 8 6 + yW_2341 7 * rowA 4 8 7 + yW_2341 8 * rowA 4 8 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 4 8 = (3 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_4_9 :
    yW_2341 0 * rowA 4 9 0 + yW_2341 1 * rowA 4 9 1 + yW_2341 2 * rowA 4 9 2 + yW_2341 3 * rowA 4 9 3 + yW_2341 4 * rowA 4 9 4 + yW_2341 5 * rowA 4 9 5 + yW_2341 6 * rowA 4 9 6 + yW_2341 7 * rowA 4 9 7 + yW_2341 8 * rowA 4 9 8 ≤ db_2341 4 9 := by
  have hleft : yW_2341 0 * rowA 4 9 0 + yW_2341 1 * rowA 4 9 1 + yW_2341 2 * rowA 4 9 2 + yW_2341 3 * rowA 4 9 3 + yW_2341 4 * rowA 4 9 4 + yW_2341 5 * rowA 4 9 5 + yW_2341 6 * rowA 4 9 6 + yW_2341 7 * rowA 4 9 7 + yW_2341 8 * rowA 4 9 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 4 9 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_5_0 :
    yW_2341 0 * rowA 5 0 0 + yW_2341 1 * rowA 5 0 1 + yW_2341 2 * rowA 5 0 2 + yW_2341 3 * rowA 5 0 3 + yW_2341 4 * rowA 5 0 4 + yW_2341 5 * rowA 5 0 5 + yW_2341 6 * rowA 5 0 6 + yW_2341 7 * rowA 5 0 7 + yW_2341 8 * rowA 5 0 8 ≤ db_2341 5 0 := by
  have hleft : yW_2341 0 * rowA 5 0 0 + yW_2341 1 * rowA 5 0 1 + yW_2341 2 * rowA 5 0 2 + yW_2341 3 * rowA 5 0 3 + yW_2341 4 * rowA 5 0 4 + yW_2341 5 * rowA 5 0 5 + yW_2341 6 * rowA 5 0 6 + yW_2341 7 * rowA 5 0 7 + yW_2341 8 * rowA 5 0 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 5 0 = (-1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_5_1 :
    yW_2341 0 * rowA 5 1 0 + yW_2341 1 * rowA 5 1 1 + yW_2341 2 * rowA 5 1 2 + yW_2341 3 * rowA 5 1 3 + yW_2341 4 * rowA 5 1 4 + yW_2341 5 * rowA 5 1 5 + yW_2341 6 * rowA 5 1 6 + yW_2341 7 * rowA 5 1 7 + yW_2341 8 * rowA 5 1 8 ≤ db_2341 5 1 := by
  have hleft : yW_2341 0 * rowA 5 1 0 + yW_2341 1 * rowA 5 1 1 + yW_2341 2 * rowA 5 1 2 + yW_2341 3 * rowA 5 1 3 + yW_2341 4 * rowA 5 1 4 + yW_2341 5 * rowA 5 1 5 + yW_2341 6 * rowA 5 1 6 + yW_2341 7 * rowA 5 1 7 + yW_2341 8 * rowA 5 1 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 5 1 = (-1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_5_2 :
    yW_2341 0 * rowA 5 2 0 + yW_2341 1 * rowA 5 2 1 + yW_2341 2 * rowA 5 2 2 + yW_2341 3 * rowA 5 2 3 + yW_2341 4 * rowA 5 2 4 + yW_2341 5 * rowA 5 2 5 + yW_2341 6 * rowA 5 2 6 + yW_2341 7 * rowA 5 2 7 + yW_2341 8 * rowA 5 2 8 ≤ db_2341 5 2 := by
  have hleft : yW_2341 0 * rowA 5 2 0 + yW_2341 1 * rowA 5 2 1 + yW_2341 2 * rowA 5 2 2 + yW_2341 3 * rowA 5 2 3 + yW_2341 4 * rowA 5 2 4 + yW_2341 5 * rowA 5 2 5 + yW_2341 6 * rowA 5 2 6 + yW_2341 7 * rowA 5 2 7 + yW_2341 8 * rowA 5 2 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 5 2 = (-1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_5_3 :
    yW_2341 0 * rowA 5 3 0 + yW_2341 1 * rowA 5 3 1 + yW_2341 2 * rowA 5 3 2 + yW_2341 3 * rowA 5 3 3 + yW_2341 4 * rowA 5 3 4 + yW_2341 5 * rowA 5 3 5 + yW_2341 6 * rowA 5 3 6 + yW_2341 7 * rowA 5 3 7 + yW_2341 8 * rowA 5 3 8 ≤ db_2341 5 3 := by
  have hleft : yW_2341 0 * rowA 5 3 0 + yW_2341 1 * rowA 5 3 1 + yW_2341 2 * rowA 5 3 2 + yW_2341 3 * rowA 5 3 3 + yW_2341 4 * rowA 5 3 4 + yW_2341 5 * rowA 5 3 5 + yW_2341 6 * rowA 5 3 6 + yW_2341 7 * rowA 5 3 7 + yW_2341 8 * rowA 5 3 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 5 3 = (-1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_5_4 :
    yW_2341 0 * rowA 5 4 0 + yW_2341 1 * rowA 5 4 1 + yW_2341 2 * rowA 5 4 2 + yW_2341 3 * rowA 5 4 3 + yW_2341 4 * rowA 5 4 4 + yW_2341 5 * rowA 5 4 5 + yW_2341 6 * rowA 5 4 6 + yW_2341 7 * rowA 5 4 7 + yW_2341 8 * rowA 5 4 8 ≤ db_2341 5 4 := by
  have hleft : yW_2341 0 * rowA 5 4 0 + yW_2341 1 * rowA 5 4 1 + yW_2341 2 * rowA 5 4 2 + yW_2341 3 * rowA 5 4 3 + yW_2341 4 * rowA 5 4 4 + yW_2341 5 * rowA 5 4 5 + yW_2341 6 * rowA 5 4 6 + yW_2341 7 * rowA 5 4 7 + yW_2341 8 * rowA 5 4 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 5 4 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_5_5 :
    yW_2341 0 * rowA 5 5 0 + yW_2341 1 * rowA 5 5 1 + yW_2341 2 * rowA 5 5 2 + yW_2341 3 * rowA 5 5 3 + yW_2341 4 * rowA 5 5 4 + yW_2341 5 * rowA 5 5 5 + yW_2341 6 * rowA 5 5 6 + yW_2341 7 * rowA 5 5 7 + yW_2341 8 * rowA 5 5 8 ≤ db_2341 5 5 := by
  have hleft : yW_2341 0 * rowA 5 5 0 + yW_2341 1 * rowA 5 5 1 + yW_2341 2 * rowA 5 5 2 + yW_2341 3 * rowA 5 5 3 + yW_2341 4 * rowA 5 5 4 + yW_2341 5 * rowA 5 5 5 + yW_2341 6 * rowA 5 5 6 + yW_2341 7 * rowA 5 5 7 + yW_2341 8 * rowA 5 5 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 5 5 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_5_6 :
    yW_2341 0 * rowA 5 6 0 + yW_2341 1 * rowA 5 6 1 + yW_2341 2 * rowA 5 6 2 + yW_2341 3 * rowA 5 6 3 + yW_2341 4 * rowA 5 6 4 + yW_2341 5 * rowA 5 6 5 + yW_2341 6 * rowA 5 6 6 + yW_2341 7 * rowA 5 6 7 + yW_2341 8 * rowA 5 6 8 ≤ db_2341 5 6 := by
  have hleft : yW_2341 0 * rowA 5 6 0 + yW_2341 1 * rowA 5 6 1 + yW_2341 2 * rowA 5 6 2 + yW_2341 3 * rowA 5 6 3 + yW_2341 4 * rowA 5 6 4 + yW_2341 5 * rowA 5 6 5 + yW_2341 6 * rowA 5 6 6 + yW_2341 7 * rowA 5 6 7 + yW_2341 8 * rowA 5 6 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 5 6 = (1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_5_7 :
    yW_2341 0 * rowA 5 7 0 + yW_2341 1 * rowA 5 7 1 + yW_2341 2 * rowA 5 7 2 + yW_2341 3 * rowA 5 7 3 + yW_2341 4 * rowA 5 7 4 + yW_2341 5 * rowA 5 7 5 + yW_2341 6 * rowA 5 7 6 + yW_2341 7 * rowA 5 7 7 + yW_2341 8 * rowA 5 7 8 ≤ db_2341 5 7 := by
  have hleft : yW_2341 0 * rowA 5 7 0 + yW_2341 1 * rowA 5 7 1 + yW_2341 2 * rowA 5 7 2 + yW_2341 3 * rowA 5 7 3 + yW_2341 4 * rowA 5 7 4 + yW_2341 5 * rowA 5 7 5 + yW_2341 6 * rowA 5 7 6 + yW_2341 7 * rowA 5 7 7 + yW_2341 8 * rowA 5 7 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 5 7 = (1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_5_8 :
    yW_2341 0 * rowA 5 8 0 + yW_2341 1 * rowA 5 8 1 + yW_2341 2 * rowA 5 8 2 + yW_2341 3 * rowA 5 8 3 + yW_2341 4 * rowA 5 8 4 + yW_2341 5 * rowA 5 8 5 + yW_2341 6 * rowA 5 8 6 + yW_2341 7 * rowA 5 8 7 + yW_2341 8 * rowA 5 8 8 ≤ db_2341 5 8 := by
  have hleft : yW_2341 0 * rowA 5 8 0 + yW_2341 1 * rowA 5 8 1 + yW_2341 2 * rowA 5 8 2 + yW_2341 3 * rowA 5 8 3 + yW_2341 4 * rowA 5 8 4 + yW_2341 5 * rowA 5 8 5 + yW_2341 6 * rowA 5 8 6 + yW_2341 7 * rowA 5 8 7 + yW_2341 8 * rowA 5 8 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 5 8 = (1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_5_9 :
    yW_2341 0 * rowA 5 9 0 + yW_2341 1 * rowA 5 9 1 + yW_2341 2 * rowA 5 9 2 + yW_2341 3 * rowA 5 9 3 + yW_2341 4 * rowA 5 9 4 + yW_2341 5 * rowA 5 9 5 + yW_2341 6 * rowA 5 9 6 + yW_2341 7 * rowA 5 9 7 + yW_2341 8 * rowA 5 9 8 ≤ db_2341 5 9 := by
  have hleft : yW_2341 0 * rowA 5 9 0 + yW_2341 1 * rowA 5 9 1 + yW_2341 2 * rowA 5 9 2 + yW_2341 3 * rowA 5 9 3 + yW_2341 4 * rowA 5 9 4 + yW_2341 5 * rowA 5 9 5 + yW_2341 6 * rowA 5 9 6 + yW_2341 7 * rowA 5 9 7 + yW_2341 8 * rowA 5 9 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 5 9 = (3 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_6_0 :
    yW_2341 0 * rowA 6 0 0 + yW_2341 1 * rowA 6 0 1 + yW_2341 2 * rowA 6 0 2 + yW_2341 3 * rowA 6 0 3 + yW_2341 4 * rowA 6 0 4 + yW_2341 5 * rowA 6 0 5 + yW_2341 6 * rowA 6 0 6 + yW_2341 7 * rowA 6 0 7 + yW_2341 8 * rowA 6 0 8 ≤ db_2341 6 0 := by
  have hleft : yW_2341 0 * rowA 6 0 0 + yW_2341 1 * rowA 6 0 1 + yW_2341 2 * rowA 6 0 2 + yW_2341 3 * rowA 6 0 3 + yW_2341 4 * rowA 6 0 4 + yW_2341 5 * rowA 6 0 5 + yW_2341 6 * rowA 6 0 6 + yW_2341 7 * rowA 6 0 7 + yW_2341 8 * rowA 6 0 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 6 0 = (-1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_6_1 :
    yW_2341 0 * rowA 6 1 0 + yW_2341 1 * rowA 6 1 1 + yW_2341 2 * rowA 6 1 2 + yW_2341 3 * rowA 6 1 3 + yW_2341 4 * rowA 6 1 4 + yW_2341 5 * rowA 6 1 5 + yW_2341 6 * rowA 6 1 6 + yW_2341 7 * rowA 6 1 7 + yW_2341 8 * rowA 6 1 8 ≤ db_2341 6 1 := by
  have hleft : yW_2341 0 * rowA 6 1 0 + yW_2341 1 * rowA 6 1 1 + yW_2341 2 * rowA 6 1 2 + yW_2341 3 * rowA 6 1 3 + yW_2341 4 * rowA 6 1 4 + yW_2341 5 * rowA 6 1 5 + yW_2341 6 * rowA 6 1 6 + yW_2341 7 * rowA 6 1 7 + yW_2341 8 * rowA 6 1 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 6 1 = (-3 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_6_2 :
    yW_2341 0 * rowA 6 2 0 + yW_2341 1 * rowA 6 2 1 + yW_2341 2 * rowA 6 2 2 + yW_2341 3 * rowA 6 2 3 + yW_2341 4 * rowA 6 2 4 + yW_2341 5 * rowA 6 2 5 + yW_2341 6 * rowA 6 2 6 + yW_2341 7 * rowA 6 2 7 + yW_2341 8 * rowA 6 2 8 ≤ db_2341 6 2 := by
  have hleft : yW_2341 0 * rowA 6 2 0 + yW_2341 1 * rowA 6 2 1 + yW_2341 2 * rowA 6 2 2 + yW_2341 3 * rowA 6 2 3 + yW_2341 4 * rowA 6 2 4 + yW_2341 5 * rowA 6 2 5 + yW_2341 6 * rowA 6 2 6 + yW_2341 7 * rowA 6 2 7 + yW_2341 8 * rowA 6 2 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 6 2 = (-3 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_6_3 :
    yW_2341 0 * rowA 6 3 0 + yW_2341 1 * rowA 6 3 1 + yW_2341 2 * rowA 6 3 2 + yW_2341 3 * rowA 6 3 3 + yW_2341 4 * rowA 6 3 4 + yW_2341 5 * rowA 6 3 5 + yW_2341 6 * rowA 6 3 6 + yW_2341 7 * rowA 6 3 7 + yW_2341 8 * rowA 6 3 8 ≤ db_2341 6 3 := by
  have hleft : yW_2341 0 * rowA 6 3 0 + yW_2341 1 * rowA 6 3 1 + yW_2341 2 * rowA 6 3 2 + yW_2341 3 * rowA 6 3 3 + yW_2341 4 * rowA 6 3 4 + yW_2341 5 * rowA 6 3 5 + yW_2341 6 * rowA 6 3 6 + yW_2341 7 * rowA 6 3 7 + yW_2341 8 * rowA 6 3 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 6 3 = (-3 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_6_4 :
    yW_2341 0 * rowA 6 4 0 + yW_2341 1 * rowA 6 4 1 + yW_2341 2 * rowA 6 4 2 + yW_2341 3 * rowA 6 4 3 + yW_2341 4 * rowA 6 4 4 + yW_2341 5 * rowA 6 4 5 + yW_2341 6 * rowA 6 4 6 + yW_2341 7 * rowA 6 4 7 + yW_2341 8 * rowA 6 4 8 ≤ db_2341 6 4 := by
  have hleft : yW_2341 0 * rowA 6 4 0 + yW_2341 1 * rowA 6 4 1 + yW_2341 2 * rowA 6 4 2 + yW_2341 3 * rowA 6 4 3 + yW_2341 4 * rowA 6 4 4 + yW_2341 5 * rowA 6 4 5 + yW_2341 6 * rowA 6 4 6 + yW_2341 7 * rowA 6 4 7 + yW_2341 8 * rowA 6 4 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 6 4 = (-1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_6_5 :
    yW_2341 0 * rowA 6 5 0 + yW_2341 1 * rowA 6 5 1 + yW_2341 2 * rowA 6 5 2 + yW_2341 3 * rowA 6 5 3 + yW_2341 4 * rowA 6 5 4 + yW_2341 5 * rowA 6 5 5 + yW_2341 6 * rowA 6 5 6 + yW_2341 7 * rowA 6 5 7 + yW_2341 8 * rowA 6 5 8 ≤ db_2341 6 5 := by
  have hleft : yW_2341 0 * rowA 6 5 0 + yW_2341 1 * rowA 6 5 1 + yW_2341 2 * rowA 6 5 2 + yW_2341 3 * rowA 6 5 3 + yW_2341 4 * rowA 6 5 4 + yW_2341 5 * rowA 6 5 5 + yW_2341 6 * rowA 6 5 6 + yW_2341 7 * rowA 6 5 7 + yW_2341 8 * rowA 6 5 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 6 5 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_6_6 :
    yW_2341 0 * rowA 6 6 0 + yW_2341 1 * rowA 6 6 1 + yW_2341 2 * rowA 6 6 2 + yW_2341 3 * rowA 6 6 3 + yW_2341 4 * rowA 6 6 4 + yW_2341 5 * rowA 6 6 5 + yW_2341 6 * rowA 6 6 6 + yW_2341 7 * rowA 6 6 7 + yW_2341 8 * rowA 6 6 8 ≤ db_2341 6 6 := by
  have hleft : yW_2341 0 * rowA 6 6 0 + yW_2341 1 * rowA 6 6 1 + yW_2341 2 * rowA 6 6 2 + yW_2341 3 * rowA 6 6 3 + yW_2341 4 * rowA 6 6 4 + yW_2341 5 * rowA 6 6 5 + yW_2341 6 * rowA 6 6 6 + yW_2341 7 * rowA 6 6 7 + yW_2341 8 * rowA 6 6 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 6 6 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_6_7 :
    yW_2341 0 * rowA 6 7 0 + yW_2341 1 * rowA 6 7 1 + yW_2341 2 * rowA 6 7 2 + yW_2341 3 * rowA 6 7 3 + yW_2341 4 * rowA 6 7 4 + yW_2341 5 * rowA 6 7 5 + yW_2341 6 * rowA 6 7 6 + yW_2341 7 * rowA 6 7 7 + yW_2341 8 * rowA 6 7 8 ≤ db_2341 6 7 := by
  have hleft : yW_2341 0 * rowA 6 7 0 + yW_2341 1 * rowA 6 7 1 + yW_2341 2 * rowA 6 7 2 + yW_2341 3 * rowA 6 7 3 + yW_2341 4 * rowA 6 7 4 + yW_2341 5 * rowA 6 7 5 + yW_2341 6 * rowA 6 7 6 + yW_2341 7 * rowA 6 7 7 + yW_2341 8 * rowA 6 7 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 6 7 = (1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_6_8 :
    yW_2341 0 * rowA 6 8 0 + yW_2341 1 * rowA 6 8 1 + yW_2341 2 * rowA 6 8 2 + yW_2341 3 * rowA 6 8 3 + yW_2341 4 * rowA 6 8 4 + yW_2341 5 * rowA 6 8 5 + yW_2341 6 * rowA 6 8 6 + yW_2341 7 * rowA 6 8 7 + yW_2341 8 * rowA 6 8 8 ≤ db_2341 6 8 := by
  have hleft : yW_2341 0 * rowA 6 8 0 + yW_2341 1 * rowA 6 8 1 + yW_2341 2 * rowA 6 8 2 + yW_2341 3 * rowA 6 8 3 + yW_2341 4 * rowA 6 8 4 + yW_2341 5 * rowA 6 8 5 + yW_2341 6 * rowA 6 8 6 + yW_2341 7 * rowA 6 8 7 + yW_2341 8 * rowA 6 8 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 6 8 = (1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_6_9 :
    yW_2341 0 * rowA 6 9 0 + yW_2341 1 * rowA 6 9 1 + yW_2341 2 * rowA 6 9 2 + yW_2341 3 * rowA 6 9 3 + yW_2341 4 * rowA 6 9 4 + yW_2341 5 * rowA 6 9 5 + yW_2341 6 * rowA 6 9 6 + yW_2341 7 * rowA 6 9 7 + yW_2341 8 * rowA 6 9 8 ≤ db_2341 6 9 := by
  have hleft : yW_2341 0 * rowA 6 9 0 + yW_2341 1 * rowA 6 9 1 + yW_2341 2 * rowA 6 9 2 + yW_2341 3 * rowA 6 9 3 + yW_2341 4 * rowA 6 9 4 + yW_2341 5 * rowA 6 9 5 + yW_2341 6 * rowA 6 9 6 + yW_2341 7 * rowA 6 9 7 + yW_2341 8 * rowA 6 9 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 6 9 = (1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_7_0 :
    yW_2341 0 * rowA 7 0 0 + yW_2341 1 * rowA 7 0 1 + yW_2341 2 * rowA 7 0 2 + yW_2341 3 * rowA 7 0 3 + yW_2341 4 * rowA 7 0 4 + yW_2341 5 * rowA 7 0 5 + yW_2341 6 * rowA 7 0 6 + yW_2341 7 * rowA 7 0 7 + yW_2341 8 * rowA 7 0 8 ≤ db_2341 7 0 := by
  have hleft : yW_2341 0 * rowA 7 0 0 + yW_2341 1 * rowA 7 0 1 + yW_2341 2 * rowA 7 0 2 + yW_2341 3 * rowA 7 0 3 + yW_2341 4 * rowA 7 0 4 + yW_2341 5 * rowA 7 0 5 + yW_2341 6 * rowA 7 0 6 + yW_2341 7 * rowA 7 0 7 + yW_2341 8 * rowA 7 0 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 7 0 = (-1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_7_1 :
    yW_2341 0 * rowA 7 1 0 + yW_2341 1 * rowA 7 1 1 + yW_2341 2 * rowA 7 1 2 + yW_2341 3 * rowA 7 1 3 + yW_2341 4 * rowA 7 1 4 + yW_2341 5 * rowA 7 1 5 + yW_2341 6 * rowA 7 1 6 + yW_2341 7 * rowA 7 1 7 + yW_2341 8 * rowA 7 1 8 ≤ db_2341 7 1 := by
  have hleft : yW_2341 0 * rowA 7 1 0 + yW_2341 1 * rowA 7 1 1 + yW_2341 2 * rowA 7 1 2 + yW_2341 3 * rowA 7 1 3 + yW_2341 4 * rowA 7 1 4 + yW_2341 5 * rowA 7 1 5 + yW_2341 6 * rowA 7 1 6 + yW_2341 7 * rowA 7 1 7 + yW_2341 8 * rowA 7 1 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 7 1 = (-1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_7_2 :
    yW_2341 0 * rowA 7 2 0 + yW_2341 1 * rowA 7 2 1 + yW_2341 2 * rowA 7 2 2 + yW_2341 3 * rowA 7 2 3 + yW_2341 4 * rowA 7 2 4 + yW_2341 5 * rowA 7 2 5 + yW_2341 6 * rowA 7 2 6 + yW_2341 7 * rowA 7 2 7 + yW_2341 8 * rowA 7 2 8 ≤ db_2341 7 2 := by
  have hleft : yW_2341 0 * rowA 7 2 0 + yW_2341 1 * rowA 7 2 1 + yW_2341 2 * rowA 7 2 2 + yW_2341 3 * rowA 7 2 3 + yW_2341 4 * rowA 7 2 4 + yW_2341 5 * rowA 7 2 5 + yW_2341 6 * rowA 7 2 6 + yW_2341 7 * rowA 7 2 7 + yW_2341 8 * rowA 7 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 7 2 = (-1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_7_3 :
    yW_2341 0 * rowA 7 3 0 + yW_2341 1 * rowA 7 3 1 + yW_2341 2 * rowA 7 3 2 + yW_2341 3 * rowA 7 3 3 + yW_2341 4 * rowA 7 3 4 + yW_2341 5 * rowA 7 3 5 + yW_2341 6 * rowA 7 3 6 + yW_2341 7 * rowA 7 3 7 + yW_2341 8 * rowA 7 3 8 ≤ db_2341 7 3 := by
  have hleft : yW_2341 0 * rowA 7 3 0 + yW_2341 1 * rowA 7 3 1 + yW_2341 2 * rowA 7 3 2 + yW_2341 3 * rowA 7 3 3 + yW_2341 4 * rowA 7 3 4 + yW_2341 5 * rowA 7 3 5 + yW_2341 6 * rowA 7 3 6 + yW_2341 7 * rowA 7 3 7 + yW_2341 8 * rowA 7 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 7 3 = (-1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_7_4 :
    yW_2341 0 * rowA 7 4 0 + yW_2341 1 * rowA 7 4 1 + yW_2341 2 * rowA 7 4 2 + yW_2341 3 * rowA 7 4 3 + yW_2341 4 * rowA 7 4 4 + yW_2341 5 * rowA 7 4 5 + yW_2341 6 * rowA 7 4 6 + yW_2341 7 * rowA 7 4 7 + yW_2341 8 * rowA 7 4 8 ≤ db_2341 7 4 := by
  have hleft : yW_2341 0 * rowA 7 4 0 + yW_2341 1 * rowA 7 4 1 + yW_2341 2 * rowA 7 4 2 + yW_2341 3 * rowA 7 4 3 + yW_2341 4 * rowA 7 4 4 + yW_2341 5 * rowA 7 4 5 + yW_2341 6 * rowA 7 4 6 + yW_2341 7 * rowA 7 4 7 + yW_2341 8 * rowA 7 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 7 4 = (-1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_7_5 :
    yW_2341 0 * rowA 7 5 0 + yW_2341 1 * rowA 7 5 1 + yW_2341 2 * rowA 7 5 2 + yW_2341 3 * rowA 7 5 3 + yW_2341 4 * rowA 7 5 4 + yW_2341 5 * rowA 7 5 5 + yW_2341 6 * rowA 7 5 6 + yW_2341 7 * rowA 7 5 7 + yW_2341 8 * rowA 7 5 8 ≤ db_2341 7 5 := by
  have hleft : yW_2341 0 * rowA 7 5 0 + yW_2341 1 * rowA 7 5 1 + yW_2341 2 * rowA 7 5 2 + yW_2341 3 * rowA 7 5 3 + yW_2341 4 * rowA 7 5 4 + yW_2341 5 * rowA 7 5 5 + yW_2341 6 * rowA 7 5 6 + yW_2341 7 * rowA 7 5 7 + yW_2341 8 * rowA 7 5 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 7 5 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_7_6 :
    yW_2341 0 * rowA 7 6 0 + yW_2341 1 * rowA 7 6 1 + yW_2341 2 * rowA 7 6 2 + yW_2341 3 * rowA 7 6 3 + yW_2341 4 * rowA 7 6 4 + yW_2341 5 * rowA 7 6 5 + yW_2341 6 * rowA 7 6 6 + yW_2341 7 * rowA 7 6 7 + yW_2341 8 * rowA 7 6 8 ≤ db_2341 7 6 := by
  have hleft : yW_2341 0 * rowA 7 6 0 + yW_2341 1 * rowA 7 6 1 + yW_2341 2 * rowA 7 6 2 + yW_2341 3 * rowA 7 6 3 + yW_2341 4 * rowA 7 6 4 + yW_2341 5 * rowA 7 6 5 + yW_2341 6 * rowA 7 6 6 + yW_2341 7 * rowA 7 6 7 + yW_2341 8 * rowA 7 6 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 7 6 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_7_7 :
    yW_2341 0 * rowA 7 7 0 + yW_2341 1 * rowA 7 7 1 + yW_2341 2 * rowA 7 7 2 + yW_2341 3 * rowA 7 7 3 + yW_2341 4 * rowA 7 7 4 + yW_2341 5 * rowA 7 7 5 + yW_2341 6 * rowA 7 7 6 + yW_2341 7 * rowA 7 7 7 + yW_2341 8 * rowA 7 7 8 ≤ db_2341 7 7 := by
  have hleft : yW_2341 0 * rowA 7 7 0 + yW_2341 1 * rowA 7 7 1 + yW_2341 2 * rowA 7 7 2 + yW_2341 3 * rowA 7 7 3 + yW_2341 4 * rowA 7 7 4 + yW_2341 5 * rowA 7 7 5 + yW_2341 6 * rowA 7 7 6 + yW_2341 7 * rowA 7 7 7 + yW_2341 8 * rowA 7 7 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 7 7 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_7_8 :
    yW_2341 0 * rowA 7 8 0 + yW_2341 1 * rowA 7 8 1 + yW_2341 2 * rowA 7 8 2 + yW_2341 3 * rowA 7 8 3 + yW_2341 4 * rowA 7 8 4 + yW_2341 5 * rowA 7 8 5 + yW_2341 6 * rowA 7 8 6 + yW_2341 7 * rowA 7 8 7 + yW_2341 8 * rowA 7 8 8 ≤ db_2341 7 8 := by
  have hleft : yW_2341 0 * rowA 7 8 0 + yW_2341 1 * rowA 7 8 1 + yW_2341 2 * rowA 7 8 2 + yW_2341 3 * rowA 7 8 3 + yW_2341 4 * rowA 7 8 4 + yW_2341 5 * rowA 7 8 5 + yW_2341 6 * rowA 7 8 6 + yW_2341 7 * rowA 7 8 7 + yW_2341 8 * rowA 7 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 7 8 = (1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_7_9 :
    yW_2341 0 * rowA 7 9 0 + yW_2341 1 * rowA 7 9 1 + yW_2341 2 * rowA 7 9 2 + yW_2341 3 * rowA 7 9 3 + yW_2341 4 * rowA 7 9 4 + yW_2341 5 * rowA 7 9 5 + yW_2341 6 * rowA 7 9 6 + yW_2341 7 * rowA 7 9 7 + yW_2341 8 * rowA 7 9 8 ≤ db_2341 7 9 := by
  have hleft : yW_2341 0 * rowA 7 9 0 + yW_2341 1 * rowA 7 9 1 + yW_2341 2 * rowA 7 9 2 + yW_2341 3 * rowA 7 9 3 + yW_2341 4 * rowA 7 9 4 + yW_2341 5 * rowA 7 9 5 + yW_2341 6 * rowA 7 9 6 + yW_2341 7 * rowA 7 9 7 + yW_2341 8 * rowA 7 9 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 7 9 = (1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_8_0 :
    yW_2341 0 * rowA 8 0 0 + yW_2341 1 * rowA 8 0 1 + yW_2341 2 * rowA 8 0 2 + yW_2341 3 * rowA 8 0 3 + yW_2341 4 * rowA 8 0 4 + yW_2341 5 * rowA 8 0 5 + yW_2341 6 * rowA 8 0 6 + yW_2341 7 * rowA 8 0 7 + yW_2341 8 * rowA 8 0 8 ≤ db_2341 8 0 := by
  have hleft : yW_2341 0 * rowA 8 0 0 + yW_2341 1 * rowA 8 0 1 + yW_2341 2 * rowA 8 0 2 + yW_2341 3 * rowA 8 0 3 + yW_2341 4 * rowA 8 0 4 + yW_2341 5 * rowA 8 0 5 + yW_2341 6 * rowA 8 0 6 + yW_2341 7 * rowA 8 0 7 + yW_2341 8 * rowA 8 0 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 8 0 = (-1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_8_1 :
    yW_2341 0 * rowA 8 1 0 + yW_2341 1 * rowA 8 1 1 + yW_2341 2 * rowA 8 1 2 + yW_2341 3 * rowA 8 1 3 + yW_2341 4 * rowA 8 1 4 + yW_2341 5 * rowA 8 1 5 + yW_2341 6 * rowA 8 1 6 + yW_2341 7 * rowA 8 1 7 + yW_2341 8 * rowA 8 1 8 ≤ db_2341 8 1 := by
  have hleft : yW_2341 0 * rowA 8 1 0 + yW_2341 1 * rowA 8 1 1 + yW_2341 2 * rowA 8 1 2 + yW_2341 3 * rowA 8 1 3 + yW_2341 4 * rowA 8 1 4 + yW_2341 5 * rowA 8 1 5 + yW_2341 6 * rowA 8 1 6 + yW_2341 7 * rowA 8 1 7 + yW_2341 8 * rowA 8 1 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 8 1 = (-1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_8_2 :
    yW_2341 0 * rowA 8 2 0 + yW_2341 1 * rowA 8 2 1 + yW_2341 2 * rowA 8 2 2 + yW_2341 3 * rowA 8 2 3 + yW_2341 4 * rowA 8 2 4 + yW_2341 5 * rowA 8 2 5 + yW_2341 6 * rowA 8 2 6 + yW_2341 7 * rowA 8 2 7 + yW_2341 8 * rowA 8 2 8 ≤ db_2341 8 2 := by
  have hleft : yW_2341 0 * rowA 8 2 0 + yW_2341 1 * rowA 8 2 1 + yW_2341 2 * rowA 8 2 2 + yW_2341 3 * rowA 8 2 3 + yW_2341 4 * rowA 8 2 4 + yW_2341 5 * rowA 8 2 5 + yW_2341 6 * rowA 8 2 6 + yW_2341 7 * rowA 8 2 7 + yW_2341 8 * rowA 8 2 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 8 2 = (-1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_8_3 :
    yW_2341 0 * rowA 8 3 0 + yW_2341 1 * rowA 8 3 1 + yW_2341 2 * rowA 8 3 2 + yW_2341 3 * rowA 8 3 3 + yW_2341 4 * rowA 8 3 4 + yW_2341 5 * rowA 8 3 5 + yW_2341 6 * rowA 8 3 6 + yW_2341 7 * rowA 8 3 7 + yW_2341 8 * rowA 8 3 8 ≤ db_2341 8 3 := by
  have hleft : yW_2341 0 * rowA 8 3 0 + yW_2341 1 * rowA 8 3 1 + yW_2341 2 * rowA 8 3 2 + yW_2341 3 * rowA 8 3 3 + yW_2341 4 * rowA 8 3 4 + yW_2341 5 * rowA 8 3 5 + yW_2341 6 * rowA 8 3 6 + yW_2341 7 * rowA 8 3 7 + yW_2341 8 * rowA 8 3 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 8 3 = (-1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_8_4 :
    yW_2341 0 * rowA 8 4 0 + yW_2341 1 * rowA 8 4 1 + yW_2341 2 * rowA 8 4 2 + yW_2341 3 * rowA 8 4 3 + yW_2341 4 * rowA 8 4 4 + yW_2341 5 * rowA 8 4 5 + yW_2341 6 * rowA 8 4 6 + yW_2341 7 * rowA 8 4 7 + yW_2341 8 * rowA 8 4 8 ≤ db_2341 8 4 := by
  have hleft : yW_2341 0 * rowA 8 4 0 + yW_2341 1 * rowA 8 4 1 + yW_2341 2 * rowA 8 4 2 + yW_2341 3 * rowA 8 4 3 + yW_2341 4 * rowA 8 4 4 + yW_2341 5 * rowA 8 4 5 + yW_2341 6 * rowA 8 4 6 + yW_2341 7 * rowA 8 4 7 + yW_2341 8 * rowA 8 4 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 8 4 = (-1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_8_5 :
    yW_2341 0 * rowA 8 5 0 + yW_2341 1 * rowA 8 5 1 + yW_2341 2 * rowA 8 5 2 + yW_2341 3 * rowA 8 5 3 + yW_2341 4 * rowA 8 5 4 + yW_2341 5 * rowA 8 5 5 + yW_2341 6 * rowA 8 5 6 + yW_2341 7 * rowA 8 5 7 + yW_2341 8 * rowA 8 5 8 ≤ db_2341 8 5 := by
  have hleft : yW_2341 0 * rowA 8 5 0 + yW_2341 1 * rowA 8 5 1 + yW_2341 2 * rowA 8 5 2 + yW_2341 3 * rowA 8 5 3 + yW_2341 4 * rowA 8 5 4 + yW_2341 5 * rowA 8 5 5 + yW_2341 6 * rowA 8 5 6 + yW_2341 7 * rowA 8 5 7 + yW_2341 8 * rowA 8 5 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 8 5 = (-1 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_8_6 :
    yW_2341 0 * rowA 8 6 0 + yW_2341 1 * rowA 8 6 1 + yW_2341 2 * rowA 8 6 2 + yW_2341 3 * rowA 8 6 3 + yW_2341 4 * rowA 8 6 4 + yW_2341 5 * rowA 8 6 5 + yW_2341 6 * rowA 8 6 6 + yW_2341 7 * rowA 8 6 7 + yW_2341 8 * rowA 8 6 8 ≤ db_2341 8 6 := by
  have hleft : yW_2341 0 * rowA 8 6 0 + yW_2341 1 * rowA 8 6 1 + yW_2341 2 * rowA 8 6 2 + yW_2341 3 * rowA 8 6 3 + yW_2341 4 * rowA 8 6 4 + yW_2341 5 * rowA 8 6 5 + yW_2341 6 * rowA 8 6 6 + yW_2341 7 * rowA 8 6 7 + yW_2341 8 * rowA 8 6 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 8 6 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_8_7 :
    yW_2341 0 * rowA 8 7 0 + yW_2341 1 * rowA 8 7 1 + yW_2341 2 * rowA 8 7 2 + yW_2341 3 * rowA 8 7 3 + yW_2341 4 * rowA 8 7 4 + yW_2341 5 * rowA 8 7 5 + yW_2341 6 * rowA 8 7 6 + yW_2341 7 * rowA 8 7 7 + yW_2341 8 * rowA 8 7 8 ≤ db_2341 8 7 := by
  have hleft : yW_2341 0 * rowA 8 7 0 + yW_2341 1 * rowA 8 7 1 + yW_2341 2 * rowA 8 7 2 + yW_2341 3 * rowA 8 7 3 + yW_2341 4 * rowA 8 7 4 + yW_2341 5 * rowA 8 7 5 + yW_2341 6 * rowA 8 7 6 + yW_2341 7 * rowA 8 7 7 + yW_2341 8 * rowA 8 7 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 8 7 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_8_8 :
    yW_2341 0 * rowA 8 8 0 + yW_2341 1 * rowA 8 8 1 + yW_2341 2 * rowA 8 8 2 + yW_2341 3 * rowA 8 8 3 + yW_2341 4 * rowA 8 8 4 + yW_2341 5 * rowA 8 8 5 + yW_2341 6 * rowA 8 8 6 + yW_2341 7 * rowA 8 8 7 + yW_2341 8 * rowA 8 8 8 ≤ db_2341 8 8 := by
  have hleft : yW_2341 0 * rowA 8 8 0 + yW_2341 1 * rowA 8 8 1 + yW_2341 2 * rowA 8 8 2 + yW_2341 3 * rowA 8 8 3 + yW_2341 4 * rowA 8 8 4 + yW_2341 5 * rowA 8 8 5 + yW_2341 6 * rowA 8 8 6 + yW_2341 7 * rowA 8 8 7 + yW_2341 8 * rowA 8 8 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 8 8 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_8_9 :
    yW_2341 0 * rowA 8 9 0 + yW_2341 1 * rowA 8 9 1 + yW_2341 2 * rowA 8 9 2 + yW_2341 3 * rowA 8 9 3 + yW_2341 4 * rowA 8 9 4 + yW_2341 5 * rowA 8 9 5 + yW_2341 6 * rowA 8 9 6 + yW_2341 7 * rowA 8 9 7 + yW_2341 8 * rowA 8 9 8 ≤ db_2341 8 9 := by
  have hleft : yW_2341 0 * rowA 8 9 0 + yW_2341 1 * rowA 8 9 1 + yW_2341 2 * rowA 8 9 2 + yW_2341 3 * rowA 8 9 3 + yW_2341 4 * rowA 8 9 4 + yW_2341 5 * rowA 8 9 5 + yW_2341 6 * rowA 8 9 6 + yW_2341 7 * rowA 8 9 7 + yW_2341 8 * rowA 8 9 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 8 9 = (1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_9_0 :
    yW_2341 0 * rowA 9 0 0 + yW_2341 1 * rowA 9 0 1 + yW_2341 2 * rowA 9 0 2 + yW_2341 3 * rowA 9 0 3 + yW_2341 4 * rowA 9 0 4 + yW_2341 5 * rowA 9 0 5 + yW_2341 6 * rowA 9 0 6 + yW_2341 7 * rowA 9 0 7 + yW_2341 8 * rowA 9 0 8 ≤ db_2341 9 0 := by
  have hleft : yW_2341 0 * rowA 9 0 0 + yW_2341 1 * rowA 9 0 1 + yW_2341 2 * rowA 9 0 2 + yW_2341 3 * rowA 9 0 3 + yW_2341 4 * rowA 9 0 4 + yW_2341 5 * rowA 9 0 5 + yW_2341 6 * rowA 9 0 6 + yW_2341 7 * rowA 9 0 7 + yW_2341 8 * rowA 9 0 8 = (-1 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 9 0 = (-1 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_9_1 :
    yW_2341 0 * rowA 9 1 0 + yW_2341 1 * rowA 9 1 1 + yW_2341 2 * rowA 9 1 2 + yW_2341 3 * rowA 9 1 3 + yW_2341 4 * rowA 9 1 4 + yW_2341 5 * rowA 9 1 5 + yW_2341 6 * rowA 9 1 6 + yW_2341 7 * rowA 9 1 7 + yW_2341 8 * rowA 9 1 8 ≤ db_2341 9 1 := by
  have hleft : yW_2341 0 * rowA 9 1 0 + yW_2341 1 * rowA 9 1 1 + yW_2341 2 * rowA 9 1 2 + yW_2341 3 * rowA 9 1 3 + yW_2341 4 * rowA 9 1 4 + yW_2341 5 * rowA 9 1 5 + yW_2341 6 * rowA 9 1 6 + yW_2341 7 * rowA 9 1 7 + yW_2341 8 * rowA 9 1 8 = (-1 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 9 1 = (-7 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_9_2 :
    yW_2341 0 * rowA 9 2 0 + yW_2341 1 * rowA 9 2 1 + yW_2341 2 * rowA 9 2 2 + yW_2341 3 * rowA 9 2 3 + yW_2341 4 * rowA 9 2 4 + yW_2341 5 * rowA 9 2 5 + yW_2341 6 * rowA 9 2 6 + yW_2341 7 * rowA 9 2 7 + yW_2341 8 * rowA 9 2 8 ≤ db_2341 9 2 := by
  have hleft : yW_2341 0 * rowA 9 2 0 + yW_2341 1 * rowA 9 2 1 + yW_2341 2 * rowA 9 2 2 + yW_2341 3 * rowA 9 2 3 + yW_2341 4 * rowA 9 2 4 + yW_2341 5 * rowA 9 2 5 + yW_2341 6 * rowA 9 2 6 + yW_2341 7 * rowA 9 2 7 + yW_2341 8 * rowA 9 2 8 = (-7 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 9 2 = (-7 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_9_3 :
    yW_2341 0 * rowA 9 3 0 + yW_2341 1 * rowA 9 3 1 + yW_2341 2 * rowA 9 3 2 + yW_2341 3 * rowA 9 3 3 + yW_2341 4 * rowA 9 3 4 + yW_2341 5 * rowA 9 3 5 + yW_2341 6 * rowA 9 3 6 + yW_2341 7 * rowA 9 3 7 + yW_2341 8 * rowA 9 3 8 ≤ db_2341 9 3 := by
  have hleft : yW_2341 0 * rowA 9 3 0 + yW_2341 1 * rowA 9 3 1 + yW_2341 2 * rowA 9 3 2 + yW_2341 3 * rowA 9 3 3 + yW_2341 4 * rowA 9 3 4 + yW_2341 5 * rowA 9 3 5 + yW_2341 6 * rowA 9 3 6 + yW_2341 7 * rowA 9 3 7 + yW_2341 8 * rowA 9 3 8 = (-7 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 9 3 = (-7 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_9_4 :
    yW_2341 0 * rowA 9 4 0 + yW_2341 1 * rowA 9 4 1 + yW_2341 2 * rowA 9 4 2 + yW_2341 3 * rowA 9 4 3 + yW_2341 4 * rowA 9 4 4 + yW_2341 5 * rowA 9 4 5 + yW_2341 6 * rowA 9 4 6 + yW_2341 7 * rowA 9 4 7 + yW_2341 8 * rowA 9 4 8 ≤ db_2341 9 4 := by
  have hleft : yW_2341 0 * rowA 9 4 0 + yW_2341 1 * rowA 9 4 1 + yW_2341 2 * rowA 9 4 2 + yW_2341 3 * rowA 9 4 3 + yW_2341 4 * rowA 9 4 4 + yW_2341 5 * rowA 9 4 5 + yW_2341 6 * rowA 9 4 6 + yW_2341 7 * rowA 9 4 7 + yW_2341 8 * rowA 9 4 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 9 4 = (-5 : ℚ) / 8 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_9_5 :
    yW_2341 0 * rowA 9 5 0 + yW_2341 1 * rowA 9 5 1 + yW_2341 2 * rowA 9 5 2 + yW_2341 3 * rowA 9 5 3 + yW_2341 4 * rowA 9 5 4 + yW_2341 5 * rowA 9 5 5 + yW_2341 6 * rowA 9 5 6 + yW_2341 7 * rowA 9 5 7 + yW_2341 8 * rowA 9 5 8 ≤ db_2341 9 5 := by
  have hleft : yW_2341 0 * rowA 9 5 0 + yW_2341 1 * rowA 9 5 1 + yW_2341 2 * rowA 9 5 2 + yW_2341 3 * rowA 9 5 3 + yW_2341 4 * rowA 9 5 4 + yW_2341 5 * rowA 9 5 5 + yW_2341 6 * rowA 9 5 6 + yW_2341 7 * rowA 9 5 7 + yW_2341 8 * rowA 9 5 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 9 5 = (-1 : ℚ) / 2 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_9_6 :
    yW_2341 0 * rowA 9 6 0 + yW_2341 1 * rowA 9 6 1 + yW_2341 2 * rowA 9 6 2 + yW_2341 3 * rowA 9 6 3 + yW_2341 4 * rowA 9 6 4 + yW_2341 5 * rowA 9 6 5 + yW_2341 6 * rowA 9 6 6 + yW_2341 7 * rowA 9 6 7 + yW_2341 8 * rowA 9 6 8 ≤ db_2341 9 6 := by
  have hleft : yW_2341 0 * rowA 9 6 0 + yW_2341 1 * rowA 9 6 1 + yW_2341 2 * rowA 9 6 2 + yW_2341 3 * rowA 9 6 3 + yW_2341 4 * rowA 9 6 4 + yW_2341 5 * rowA 9 6 5 + yW_2341 6 * rowA 9 6 6 + yW_2341 7 * rowA 9 6 7 + yW_2341 8 * rowA 9 6 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 9 6 = (-1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_9_7 :
    yW_2341 0 * rowA 9 7 0 + yW_2341 1 * rowA 9 7 1 + yW_2341 2 * rowA 9 7 2 + yW_2341 3 * rowA 9 7 3 + yW_2341 4 * rowA 9 7 4 + yW_2341 5 * rowA 9 7 5 + yW_2341 6 * rowA 9 7 6 + yW_2341 7 * rowA 9 7 7 + yW_2341 8 * rowA 9 7 8 ≤ db_2341 9 7 := by
  have hleft : yW_2341 0 * rowA 9 7 0 + yW_2341 1 * rowA 9 7 1 + yW_2341 2 * rowA 9 7 2 + yW_2341 3 * rowA 9 7 3 + yW_2341 4 * rowA 9 7 4 + yW_2341 5 * rowA 9 7 5 + yW_2341 6 * rowA 9 7 6 + yW_2341 7 * rowA 9 7 7 + yW_2341 8 * rowA 9 7 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 9 7 = (-1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_9_8 :
    yW_2341 0 * rowA 9 8 0 + yW_2341 1 * rowA 9 8 1 + yW_2341 2 * rowA 9 8 2 + yW_2341 3 * rowA 9 8 3 + yW_2341 4 * rowA 9 8 4 + yW_2341 5 * rowA 9 8 5 + yW_2341 6 * rowA 9 8 6 + yW_2341 7 * rowA 9 8 7 + yW_2341 8 * rowA 9 8 8 ≤ db_2341 9 8 := by
  have hleft : yW_2341 0 * rowA 9 8 0 + yW_2341 1 * rowA 9 8 1 + yW_2341 2 * rowA 9 8 2 + yW_2341 3 * rowA 9 8 3 + yW_2341 4 * rowA 9 8 4 + yW_2341 5 * rowA 9 8 5 + yW_2341 6 * rowA 9 8 6 + yW_2341 7 * rowA 9 8 7 + yW_2341 8 * rowA 9 8 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 9 8 = (-1 : ℚ) / 4 := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_9_9 :
    yW_2341 0 * rowA 9 9 0 + yW_2341 1 * rowA 9 9 1 + yW_2341 2 * rowA 9 9 2 + yW_2341 3 * rowA 9 9 3 + yW_2341 4 * rowA 9 9 4 + yW_2341 5 * rowA 9 9 5 + yW_2341 6 * rowA 9 9 6 + yW_2341 7 * rowA 9 9 7 + yW_2341 8 * rowA 9 9 8 ≤ db_2341 9 9 := by
  have hleft : yW_2341 0 * rowA 9 9 0 + yW_2341 1 * rowA 9 9 1 + yW_2341 2 * rowA 9 9 2 + yW_2341 3 * rowA 9 9 3 + yW_2341 4 * rowA 9 9 4 + yW_2341 5 * rowA 9 9 5 + yW_2341 6 * rowA 9 9 6 + yW_2341 7 * rowA 9 9 7 + yW_2341 8 * rowA 9 9 8 = (0 : ℚ) := by
    norm_num [yW_2341, rowA]
  have hright : db_2341 9 9 = (0 : ℚ) := by
    norm_num [db_2341, dbmVal_2341]
  rw [hleft, hright]
  norm_num

theorem row_cap_2341_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 0 j q) ≤ db_2341 0 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_0_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_0_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_0_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_0_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_0_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_0_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_0_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_0_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_0_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_0_9

theorem row_cap_2341_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 1 j q) ≤ db_2341 1 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_1_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_1_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_1_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_1_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_1_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_1_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_1_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_1_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_1_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_1_9

theorem row_cap_2341_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 2 j q) ≤ db_2341 2 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_2_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_2_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_2_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_2_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_2_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_2_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_2_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_2_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_2_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_2_9

theorem row_cap_2341_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 3 j q) ≤ db_2341 3 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_3_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_3_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_3_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_3_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_3_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_3_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_3_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_3_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_3_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_3_9

theorem row_cap_2341_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 4 j q) ≤ db_2341 4 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_4_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_4_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_4_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_4_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_4_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_4_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_4_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_4_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_4_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_4_9

theorem row_cap_2341_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 5 j q) ≤ db_2341 5 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_5_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_5_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_5_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_5_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_5_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_5_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_5_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_5_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_5_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_5_9

theorem row_cap_2341_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 6 j q) ≤ db_2341 6 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_6_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_6_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_6_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_6_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_6_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_6_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_6_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_6_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_6_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_6_9

theorem row_cap_2341_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 7 j q) ≤ db_2341 7 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_7_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_7_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_7_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_7_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_7_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_7_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_7_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_7_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_7_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_7_9

theorem row_cap_2341_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 8 j q) ≤ db_2341 8 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_8_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_8_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_8_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_8_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_8_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_8_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_8_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_8_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_8_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_8_9

theorem row_cap_2341_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 9 j q) ≤ db_2341 9 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_9_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_9_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_9_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_9_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_9_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_9_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_9_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_9_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_9_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2341_9_9

theorem row_cap_2341 (i j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA i j q) ≤ db_2341 i j := by
  fin_cases i
  · exact row_cap_2341_0 j
  · exact row_cap_2341_1 j
  · exact row_cap_2341_2 j
  · exact row_cap_2341_3 j
  · exact row_cap_2341_4 j
  · exact row_cap_2341_5 j
  · exact row_cap_2341_6 j
  · exact row_cap_2341_7 j
  · exact row_cap_2341_8 j
  · exact row_cap_2341_9 j

def dbmVal_2356 : Fin 10 → Fin 10 → ℤ
  | i, j => ![
      ![0, 512, 512, 512, 1280, 2048, 2304, 3072, 3072, 4096],
      ![0, 0, 512, 512, 1280, 2048, 2304, 3072, 3072, 4096],
      ![0, 0, 0, 512, 1280, 2048, 2304, 3072, 3072, 4096],
      ![-256, 0, 0, 0, 1024, 1792, 2048, 2560, 2816, 3840],
      ![-1024, -512, -512, -512, 0, 1024, 1280, 2048, 2048, 3072],
      ![-1792, -1536, -1536, -1536, -512, 0, 512, 1024, 1024, 2304],
      ![-1792, -1536, -1536, -1536, -512, 0, 0, 1024, 1024, 2304],
      ![-2304, -2048, -2048, -2048, -1024, -256, 0, 0, 768, 1792],
      ![-2816, -2560, -2560, -2560, -1536, -768, -512, 0, 0, 1280],
      ![-4096, -3584, -3584, -3584, -2816, -2048, -1792, -1024, -1024, 0]
    ] i j

def db_2356 (i j : Fin 10) : ℚ := (dbmVal_2356 i j : ℚ) / 4096

theorem row_cap_2356_0_0 :
    yW_2356 0 * rowA 0 0 0 + yW_2356 1 * rowA 0 0 1 + yW_2356 2 * rowA 0 0 2 + yW_2356 3 * rowA 0 0 3 + yW_2356 4 * rowA 0 0 4 + yW_2356 5 * rowA 0 0 5 + yW_2356 6 * rowA 0 0 6 + yW_2356 7 * rowA 0 0 7 + yW_2356 8 * rowA 0 0 8 ≤ db_2356 0 0 := by
  have hleft : yW_2356 0 * rowA 0 0 0 + yW_2356 1 * rowA 0 0 1 + yW_2356 2 * rowA 0 0 2 + yW_2356 3 * rowA 0 0 3 + yW_2356 4 * rowA 0 0 4 + yW_2356 5 * rowA 0 0 5 + yW_2356 6 * rowA 0 0 6 + yW_2356 7 * rowA 0 0 7 + yW_2356 8 * rowA 0 0 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 0 0 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_0_1 :
    yW_2356 0 * rowA 0 1 0 + yW_2356 1 * rowA 0 1 1 + yW_2356 2 * rowA 0 1 2 + yW_2356 3 * rowA 0 1 3 + yW_2356 4 * rowA 0 1 4 + yW_2356 5 * rowA 0 1 5 + yW_2356 6 * rowA 0 1 6 + yW_2356 7 * rowA 0 1 7 + yW_2356 8 * rowA 0 1 8 ≤ db_2356 0 1 := by
  have hleft : yW_2356 0 * rowA 0 1 0 + yW_2356 1 * rowA 0 1 1 + yW_2356 2 * rowA 0 1 2 + yW_2356 3 * rowA 0 1 3 + yW_2356 4 * rowA 0 1 4 + yW_2356 5 * rowA 0 1 5 + yW_2356 6 * rowA 0 1 6 + yW_2356 7 * rowA 0 1 7 + yW_2356 8 * rowA 0 1 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 0 1 = (1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_0_2 :
    yW_2356 0 * rowA 0 2 0 + yW_2356 1 * rowA 0 2 1 + yW_2356 2 * rowA 0 2 2 + yW_2356 3 * rowA 0 2 3 + yW_2356 4 * rowA 0 2 4 + yW_2356 5 * rowA 0 2 5 + yW_2356 6 * rowA 0 2 6 + yW_2356 7 * rowA 0 2 7 + yW_2356 8 * rowA 0 2 8 ≤ db_2356 0 2 := by
  have hleft : yW_2356 0 * rowA 0 2 0 + yW_2356 1 * rowA 0 2 1 + yW_2356 2 * rowA 0 2 2 + yW_2356 3 * rowA 0 2 3 + yW_2356 4 * rowA 0 2 4 + yW_2356 5 * rowA 0 2 5 + yW_2356 6 * rowA 0 2 6 + yW_2356 7 * rowA 0 2 7 + yW_2356 8 * rowA 0 2 8 = (1 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 0 2 = (1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_0_3 :
    yW_2356 0 * rowA 0 3 0 + yW_2356 1 * rowA 0 3 1 + yW_2356 2 * rowA 0 3 2 + yW_2356 3 * rowA 0 3 3 + yW_2356 4 * rowA 0 3 4 + yW_2356 5 * rowA 0 3 5 + yW_2356 6 * rowA 0 3 6 + yW_2356 7 * rowA 0 3 7 + yW_2356 8 * rowA 0 3 8 ≤ db_2356 0 3 := by
  have hleft : yW_2356 0 * rowA 0 3 0 + yW_2356 1 * rowA 0 3 1 + yW_2356 2 * rowA 0 3 2 + yW_2356 3 * rowA 0 3 3 + yW_2356 4 * rowA 0 3 4 + yW_2356 5 * rowA 0 3 5 + yW_2356 6 * rowA 0 3 6 + yW_2356 7 * rowA 0 3 7 + yW_2356 8 * rowA 0 3 8 = (1 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 0 3 = (1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_0_4 :
    yW_2356 0 * rowA 0 4 0 + yW_2356 1 * rowA 0 4 1 + yW_2356 2 * rowA 0 4 2 + yW_2356 3 * rowA 0 4 3 + yW_2356 4 * rowA 0 4 4 + yW_2356 5 * rowA 0 4 5 + yW_2356 6 * rowA 0 4 6 + yW_2356 7 * rowA 0 4 7 + yW_2356 8 * rowA 0 4 8 ≤ db_2356 0 4 := by
  have hleft : yW_2356 0 * rowA 0 4 0 + yW_2356 1 * rowA 0 4 1 + yW_2356 2 * rowA 0 4 2 + yW_2356 3 * rowA 0 4 3 + yW_2356 4 * rowA 0 4 4 + yW_2356 5 * rowA 0 4 5 + yW_2356 6 * rowA 0 4 6 + yW_2356 7 * rowA 0 4 7 + yW_2356 8 * rowA 0 4 8 = (5 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 0 4 = (5 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_0_5 :
    yW_2356 0 * rowA 0 5 0 + yW_2356 1 * rowA 0 5 1 + yW_2356 2 * rowA 0 5 2 + yW_2356 3 * rowA 0 5 3 + yW_2356 4 * rowA 0 5 4 + yW_2356 5 * rowA 0 5 5 + yW_2356 6 * rowA 0 5 6 + yW_2356 7 * rowA 0 5 7 + yW_2356 8 * rowA 0 5 8 ≤ db_2356 0 5 := by
  have hleft : yW_2356 0 * rowA 0 5 0 + yW_2356 1 * rowA 0 5 1 + yW_2356 2 * rowA 0 5 2 + yW_2356 3 * rowA 0 5 3 + yW_2356 4 * rowA 0 5 4 + yW_2356 5 * rowA 0 5 5 + yW_2356 6 * rowA 0 5 6 + yW_2356 7 * rowA 0 5 7 + yW_2356 8 * rowA 0 5 8 = (7 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 0 5 = (1 : ℚ) / 2 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_0_6 :
    yW_2356 0 * rowA 0 6 0 + yW_2356 1 * rowA 0 6 1 + yW_2356 2 * rowA 0 6 2 + yW_2356 3 * rowA 0 6 3 + yW_2356 4 * rowA 0 6 4 + yW_2356 5 * rowA 0 6 5 + yW_2356 6 * rowA 0 6 6 + yW_2356 7 * rowA 0 6 7 + yW_2356 8 * rowA 0 6 8 ≤ db_2356 0 6 := by
  have hleft : yW_2356 0 * rowA 0 6 0 + yW_2356 1 * rowA 0 6 1 + yW_2356 2 * rowA 0 6 2 + yW_2356 3 * rowA 0 6 3 + yW_2356 4 * rowA 0 6 4 + yW_2356 5 * rowA 0 6 5 + yW_2356 6 * rowA 0 6 6 + yW_2356 7 * rowA 0 6 7 + yW_2356 8 * rowA 0 6 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 0 6 = (9 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_0_7 :
    yW_2356 0 * rowA 0 7 0 + yW_2356 1 * rowA 0 7 1 + yW_2356 2 * rowA 0 7 2 + yW_2356 3 * rowA 0 7 3 + yW_2356 4 * rowA 0 7 4 + yW_2356 5 * rowA 0 7 5 + yW_2356 6 * rowA 0 7 6 + yW_2356 7 * rowA 0 7 7 + yW_2356 8 * rowA 0 7 8 ≤ db_2356 0 7 := by
  have hleft : yW_2356 0 * rowA 0 7 0 + yW_2356 1 * rowA 0 7 1 + yW_2356 2 * rowA 0 7 2 + yW_2356 3 * rowA 0 7 3 + yW_2356 4 * rowA 0 7 4 + yW_2356 5 * rowA 0 7 5 + yW_2356 6 * rowA 0 7 6 + yW_2356 7 * rowA 0 7 7 + yW_2356 8 * rowA 0 7 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 0 7 = (3 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_0_8 :
    yW_2356 0 * rowA 0 8 0 + yW_2356 1 * rowA 0 8 1 + yW_2356 2 * rowA 0 8 2 + yW_2356 3 * rowA 0 8 3 + yW_2356 4 * rowA 0 8 4 + yW_2356 5 * rowA 0 8 5 + yW_2356 6 * rowA 0 8 6 + yW_2356 7 * rowA 0 8 7 + yW_2356 8 * rowA 0 8 8 ≤ db_2356 0 8 := by
  have hleft : yW_2356 0 * rowA 0 8 0 + yW_2356 1 * rowA 0 8 1 + yW_2356 2 * rowA 0 8 2 + yW_2356 3 * rowA 0 8 3 + yW_2356 4 * rowA 0 8 4 + yW_2356 5 * rowA 0 8 5 + yW_2356 6 * rowA 0 8 6 + yW_2356 7 * rowA 0 8 7 + yW_2356 8 * rowA 0 8 8 = (11 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 0 8 = (3 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_0_9 :
    yW_2356 0 * rowA 0 9 0 + yW_2356 1 * rowA 0 9 1 + yW_2356 2 * rowA 0 9 2 + yW_2356 3 * rowA 0 9 3 + yW_2356 4 * rowA 0 9 4 + yW_2356 5 * rowA 0 9 5 + yW_2356 6 * rowA 0 9 6 + yW_2356 7 * rowA 0 9 7 + yW_2356 8 * rowA 0 9 8 ≤ db_2356 0 9 := by
  have hleft : yW_2356 0 * rowA 0 9 0 + yW_2356 1 * rowA 0 9 1 + yW_2356 2 * rowA 0 9 2 + yW_2356 3 * rowA 0 9 3 + yW_2356 4 * rowA 0 9 4 + yW_2356 5 * rowA 0 9 5 + yW_2356 6 * rowA 0 9 6 + yW_2356 7 * rowA 0 9 7 + yW_2356 8 * rowA 0 9 8 = (1 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 0 9 = (1 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_1_0 :
    yW_2356 0 * rowA 1 0 0 + yW_2356 1 * rowA 1 0 1 + yW_2356 2 * rowA 1 0 2 + yW_2356 3 * rowA 1 0 3 + yW_2356 4 * rowA 1 0 4 + yW_2356 5 * rowA 1 0 5 + yW_2356 6 * rowA 1 0 6 + yW_2356 7 * rowA 1 0 7 + yW_2356 8 * rowA 1 0 8 ≤ db_2356 1 0 := by
  have hleft : yW_2356 0 * rowA 1 0 0 + yW_2356 1 * rowA 1 0 1 + yW_2356 2 * rowA 1 0 2 + yW_2356 3 * rowA 1 0 3 + yW_2356 4 * rowA 1 0 4 + yW_2356 5 * rowA 1 0 5 + yW_2356 6 * rowA 1 0 6 + yW_2356 7 * rowA 1 0 7 + yW_2356 8 * rowA 1 0 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 1 0 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_1_1 :
    yW_2356 0 * rowA 1 1 0 + yW_2356 1 * rowA 1 1 1 + yW_2356 2 * rowA 1 1 2 + yW_2356 3 * rowA 1 1 3 + yW_2356 4 * rowA 1 1 4 + yW_2356 5 * rowA 1 1 5 + yW_2356 6 * rowA 1 1 6 + yW_2356 7 * rowA 1 1 7 + yW_2356 8 * rowA 1 1 8 ≤ db_2356 1 1 := by
  have hleft : yW_2356 0 * rowA 1 1 0 + yW_2356 1 * rowA 1 1 1 + yW_2356 2 * rowA 1 1 2 + yW_2356 3 * rowA 1 1 3 + yW_2356 4 * rowA 1 1 4 + yW_2356 5 * rowA 1 1 5 + yW_2356 6 * rowA 1 1 6 + yW_2356 7 * rowA 1 1 7 + yW_2356 8 * rowA 1 1 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 1 1 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_1_2 :
    yW_2356 0 * rowA 1 2 0 + yW_2356 1 * rowA 1 2 1 + yW_2356 2 * rowA 1 2 2 + yW_2356 3 * rowA 1 2 3 + yW_2356 4 * rowA 1 2 4 + yW_2356 5 * rowA 1 2 5 + yW_2356 6 * rowA 1 2 6 + yW_2356 7 * rowA 1 2 7 + yW_2356 8 * rowA 1 2 8 ≤ db_2356 1 2 := by
  have hleft : yW_2356 0 * rowA 1 2 0 + yW_2356 1 * rowA 1 2 1 + yW_2356 2 * rowA 1 2 2 + yW_2356 3 * rowA 1 2 3 + yW_2356 4 * rowA 1 2 4 + yW_2356 5 * rowA 1 2 5 + yW_2356 6 * rowA 1 2 6 + yW_2356 7 * rowA 1 2 7 + yW_2356 8 * rowA 1 2 8 = (1 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 1 2 = (1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_1_3 :
    yW_2356 0 * rowA 1 3 0 + yW_2356 1 * rowA 1 3 1 + yW_2356 2 * rowA 1 3 2 + yW_2356 3 * rowA 1 3 3 + yW_2356 4 * rowA 1 3 4 + yW_2356 5 * rowA 1 3 5 + yW_2356 6 * rowA 1 3 6 + yW_2356 7 * rowA 1 3 7 + yW_2356 8 * rowA 1 3 8 ≤ db_2356 1 3 := by
  have hleft : yW_2356 0 * rowA 1 3 0 + yW_2356 1 * rowA 1 3 1 + yW_2356 2 * rowA 1 3 2 + yW_2356 3 * rowA 1 3 3 + yW_2356 4 * rowA 1 3 4 + yW_2356 5 * rowA 1 3 5 + yW_2356 6 * rowA 1 3 6 + yW_2356 7 * rowA 1 3 7 + yW_2356 8 * rowA 1 3 8 = (1 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 1 3 = (1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_1_4 :
    yW_2356 0 * rowA 1 4 0 + yW_2356 1 * rowA 1 4 1 + yW_2356 2 * rowA 1 4 2 + yW_2356 3 * rowA 1 4 3 + yW_2356 4 * rowA 1 4 4 + yW_2356 5 * rowA 1 4 5 + yW_2356 6 * rowA 1 4 6 + yW_2356 7 * rowA 1 4 7 + yW_2356 8 * rowA 1 4 8 ≤ db_2356 1 4 := by
  have hleft : yW_2356 0 * rowA 1 4 0 + yW_2356 1 * rowA 1 4 1 + yW_2356 2 * rowA 1 4 2 + yW_2356 3 * rowA 1 4 3 + yW_2356 4 * rowA 1 4 4 + yW_2356 5 * rowA 1 4 5 + yW_2356 6 * rowA 1 4 6 + yW_2356 7 * rowA 1 4 7 + yW_2356 8 * rowA 1 4 8 = (5 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 1 4 = (5 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_1_5 :
    yW_2356 0 * rowA 1 5 0 + yW_2356 1 * rowA 1 5 1 + yW_2356 2 * rowA 1 5 2 + yW_2356 3 * rowA 1 5 3 + yW_2356 4 * rowA 1 5 4 + yW_2356 5 * rowA 1 5 5 + yW_2356 6 * rowA 1 5 6 + yW_2356 7 * rowA 1 5 7 + yW_2356 8 * rowA 1 5 8 ≤ db_2356 1 5 := by
  have hleft : yW_2356 0 * rowA 1 5 0 + yW_2356 1 * rowA 1 5 1 + yW_2356 2 * rowA 1 5 2 + yW_2356 3 * rowA 1 5 3 + yW_2356 4 * rowA 1 5 4 + yW_2356 5 * rowA 1 5 5 + yW_2356 6 * rowA 1 5 6 + yW_2356 7 * rowA 1 5 7 + yW_2356 8 * rowA 1 5 8 = (7 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 1 5 = (1 : ℚ) / 2 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_1_6 :
    yW_2356 0 * rowA 1 6 0 + yW_2356 1 * rowA 1 6 1 + yW_2356 2 * rowA 1 6 2 + yW_2356 3 * rowA 1 6 3 + yW_2356 4 * rowA 1 6 4 + yW_2356 5 * rowA 1 6 5 + yW_2356 6 * rowA 1 6 6 + yW_2356 7 * rowA 1 6 7 + yW_2356 8 * rowA 1 6 8 ≤ db_2356 1 6 := by
  have hleft : yW_2356 0 * rowA 1 6 0 + yW_2356 1 * rowA 1 6 1 + yW_2356 2 * rowA 1 6 2 + yW_2356 3 * rowA 1 6 3 + yW_2356 4 * rowA 1 6 4 + yW_2356 5 * rowA 1 6 5 + yW_2356 6 * rowA 1 6 6 + yW_2356 7 * rowA 1 6 7 + yW_2356 8 * rowA 1 6 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 1 6 = (9 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_1_7 :
    yW_2356 0 * rowA 1 7 0 + yW_2356 1 * rowA 1 7 1 + yW_2356 2 * rowA 1 7 2 + yW_2356 3 * rowA 1 7 3 + yW_2356 4 * rowA 1 7 4 + yW_2356 5 * rowA 1 7 5 + yW_2356 6 * rowA 1 7 6 + yW_2356 7 * rowA 1 7 7 + yW_2356 8 * rowA 1 7 8 ≤ db_2356 1 7 := by
  have hleft : yW_2356 0 * rowA 1 7 0 + yW_2356 1 * rowA 1 7 1 + yW_2356 2 * rowA 1 7 2 + yW_2356 3 * rowA 1 7 3 + yW_2356 4 * rowA 1 7 4 + yW_2356 5 * rowA 1 7 5 + yW_2356 6 * rowA 1 7 6 + yW_2356 7 * rowA 1 7 7 + yW_2356 8 * rowA 1 7 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 1 7 = (3 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_1_8 :
    yW_2356 0 * rowA 1 8 0 + yW_2356 1 * rowA 1 8 1 + yW_2356 2 * rowA 1 8 2 + yW_2356 3 * rowA 1 8 3 + yW_2356 4 * rowA 1 8 4 + yW_2356 5 * rowA 1 8 5 + yW_2356 6 * rowA 1 8 6 + yW_2356 7 * rowA 1 8 7 + yW_2356 8 * rowA 1 8 8 ≤ db_2356 1 8 := by
  have hleft : yW_2356 0 * rowA 1 8 0 + yW_2356 1 * rowA 1 8 1 + yW_2356 2 * rowA 1 8 2 + yW_2356 3 * rowA 1 8 3 + yW_2356 4 * rowA 1 8 4 + yW_2356 5 * rowA 1 8 5 + yW_2356 6 * rowA 1 8 6 + yW_2356 7 * rowA 1 8 7 + yW_2356 8 * rowA 1 8 8 = (11 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 1 8 = (3 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_1_9 :
    yW_2356 0 * rowA 1 9 0 + yW_2356 1 * rowA 1 9 1 + yW_2356 2 * rowA 1 9 2 + yW_2356 3 * rowA 1 9 3 + yW_2356 4 * rowA 1 9 4 + yW_2356 5 * rowA 1 9 5 + yW_2356 6 * rowA 1 9 6 + yW_2356 7 * rowA 1 9 7 + yW_2356 8 * rowA 1 9 8 ≤ db_2356 1 9 := by
  have hleft : yW_2356 0 * rowA 1 9 0 + yW_2356 1 * rowA 1 9 1 + yW_2356 2 * rowA 1 9 2 + yW_2356 3 * rowA 1 9 3 + yW_2356 4 * rowA 1 9 4 + yW_2356 5 * rowA 1 9 5 + yW_2356 6 * rowA 1 9 6 + yW_2356 7 * rowA 1 9 7 + yW_2356 8 * rowA 1 9 8 = (1 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 1 9 = (1 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_2_0 :
    yW_2356 0 * rowA 2 0 0 + yW_2356 1 * rowA 2 0 1 + yW_2356 2 * rowA 2 0 2 + yW_2356 3 * rowA 2 0 3 + yW_2356 4 * rowA 2 0 4 + yW_2356 5 * rowA 2 0 5 + yW_2356 6 * rowA 2 0 6 + yW_2356 7 * rowA 2 0 7 + yW_2356 8 * rowA 2 0 8 ≤ db_2356 2 0 := by
  have hleft : yW_2356 0 * rowA 2 0 0 + yW_2356 1 * rowA 2 0 1 + yW_2356 2 * rowA 2 0 2 + yW_2356 3 * rowA 2 0 3 + yW_2356 4 * rowA 2 0 4 + yW_2356 5 * rowA 2 0 5 + yW_2356 6 * rowA 2 0 6 + yW_2356 7 * rowA 2 0 7 + yW_2356 8 * rowA 2 0 8 = (-1 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 2 0 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_2_1 :
    yW_2356 0 * rowA 2 1 0 + yW_2356 1 * rowA 2 1 1 + yW_2356 2 * rowA 2 1 2 + yW_2356 3 * rowA 2 1 3 + yW_2356 4 * rowA 2 1 4 + yW_2356 5 * rowA 2 1 5 + yW_2356 6 * rowA 2 1 6 + yW_2356 7 * rowA 2 1 7 + yW_2356 8 * rowA 2 1 8 ≤ db_2356 2 1 := by
  have hleft : yW_2356 0 * rowA 2 1 0 + yW_2356 1 * rowA 2 1 1 + yW_2356 2 * rowA 2 1 2 + yW_2356 3 * rowA 2 1 3 + yW_2356 4 * rowA 2 1 4 + yW_2356 5 * rowA 2 1 5 + yW_2356 6 * rowA 2 1 6 + yW_2356 7 * rowA 2 1 7 + yW_2356 8 * rowA 2 1 8 = (-1 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 2 1 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_2_2 :
    yW_2356 0 * rowA 2 2 0 + yW_2356 1 * rowA 2 2 1 + yW_2356 2 * rowA 2 2 2 + yW_2356 3 * rowA 2 2 3 + yW_2356 4 * rowA 2 2 4 + yW_2356 5 * rowA 2 2 5 + yW_2356 6 * rowA 2 2 6 + yW_2356 7 * rowA 2 2 7 + yW_2356 8 * rowA 2 2 8 ≤ db_2356 2 2 := by
  have hleft : yW_2356 0 * rowA 2 2 0 + yW_2356 1 * rowA 2 2 1 + yW_2356 2 * rowA 2 2 2 + yW_2356 3 * rowA 2 2 3 + yW_2356 4 * rowA 2 2 4 + yW_2356 5 * rowA 2 2 5 + yW_2356 6 * rowA 2 2 6 + yW_2356 7 * rowA 2 2 7 + yW_2356 8 * rowA 2 2 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 2 2 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_2_3 :
    yW_2356 0 * rowA 2 3 0 + yW_2356 1 * rowA 2 3 1 + yW_2356 2 * rowA 2 3 2 + yW_2356 3 * rowA 2 3 3 + yW_2356 4 * rowA 2 3 4 + yW_2356 5 * rowA 2 3 5 + yW_2356 6 * rowA 2 3 6 + yW_2356 7 * rowA 2 3 7 + yW_2356 8 * rowA 2 3 8 ≤ db_2356 2 3 := by
  have hleft : yW_2356 0 * rowA 2 3 0 + yW_2356 1 * rowA 2 3 1 + yW_2356 2 * rowA 2 3 2 + yW_2356 3 * rowA 2 3 3 + yW_2356 4 * rowA 2 3 4 + yW_2356 5 * rowA 2 3 5 + yW_2356 6 * rowA 2 3 6 + yW_2356 7 * rowA 2 3 7 + yW_2356 8 * rowA 2 3 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 2 3 = (1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_2_4 :
    yW_2356 0 * rowA 2 4 0 + yW_2356 1 * rowA 2 4 1 + yW_2356 2 * rowA 2 4 2 + yW_2356 3 * rowA 2 4 3 + yW_2356 4 * rowA 2 4 4 + yW_2356 5 * rowA 2 4 5 + yW_2356 6 * rowA 2 4 6 + yW_2356 7 * rowA 2 4 7 + yW_2356 8 * rowA 2 4 8 ≤ db_2356 2 4 := by
  have hleft : yW_2356 0 * rowA 2 4 0 + yW_2356 1 * rowA 2 4 1 + yW_2356 2 * rowA 2 4 2 + yW_2356 3 * rowA 2 4 3 + yW_2356 4 * rowA 2 4 4 + yW_2356 5 * rowA 2 4 5 + yW_2356 6 * rowA 2 4 6 + yW_2356 7 * rowA 2 4 7 + yW_2356 8 * rowA 2 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 2 4 = (5 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_2_5 :
    yW_2356 0 * rowA 2 5 0 + yW_2356 1 * rowA 2 5 1 + yW_2356 2 * rowA 2 5 2 + yW_2356 3 * rowA 2 5 3 + yW_2356 4 * rowA 2 5 4 + yW_2356 5 * rowA 2 5 5 + yW_2356 6 * rowA 2 5 6 + yW_2356 7 * rowA 2 5 7 + yW_2356 8 * rowA 2 5 8 ≤ db_2356 2 5 := by
  have hleft : yW_2356 0 * rowA 2 5 0 + yW_2356 1 * rowA 2 5 1 + yW_2356 2 * rowA 2 5 2 + yW_2356 3 * rowA 2 5 3 + yW_2356 4 * rowA 2 5 4 + yW_2356 5 * rowA 2 5 5 + yW_2356 6 * rowA 2 5 6 + yW_2356 7 * rowA 2 5 7 + yW_2356 8 * rowA 2 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 2 5 = (1 : ℚ) / 2 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_2_6 :
    yW_2356 0 * rowA 2 6 0 + yW_2356 1 * rowA 2 6 1 + yW_2356 2 * rowA 2 6 2 + yW_2356 3 * rowA 2 6 3 + yW_2356 4 * rowA 2 6 4 + yW_2356 5 * rowA 2 6 5 + yW_2356 6 * rowA 2 6 6 + yW_2356 7 * rowA 2 6 7 + yW_2356 8 * rowA 2 6 8 ≤ db_2356 2 6 := by
  have hleft : yW_2356 0 * rowA 2 6 0 + yW_2356 1 * rowA 2 6 1 + yW_2356 2 * rowA 2 6 2 + yW_2356 3 * rowA 2 6 3 + yW_2356 4 * rowA 2 6 4 + yW_2356 5 * rowA 2 6 5 + yW_2356 6 * rowA 2 6 6 + yW_2356 7 * rowA 2 6 7 + yW_2356 8 * rowA 2 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 2 6 = (9 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_2_7 :
    yW_2356 0 * rowA 2 7 0 + yW_2356 1 * rowA 2 7 1 + yW_2356 2 * rowA 2 7 2 + yW_2356 3 * rowA 2 7 3 + yW_2356 4 * rowA 2 7 4 + yW_2356 5 * rowA 2 7 5 + yW_2356 6 * rowA 2 7 6 + yW_2356 7 * rowA 2 7 7 + yW_2356 8 * rowA 2 7 8 ≤ db_2356 2 7 := by
  have hleft : yW_2356 0 * rowA 2 7 0 + yW_2356 1 * rowA 2 7 1 + yW_2356 2 * rowA 2 7 2 + yW_2356 3 * rowA 2 7 3 + yW_2356 4 * rowA 2 7 4 + yW_2356 5 * rowA 2 7 5 + yW_2356 6 * rowA 2 7 6 + yW_2356 7 * rowA 2 7 7 + yW_2356 8 * rowA 2 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 2 7 = (3 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_2_8 :
    yW_2356 0 * rowA 2 8 0 + yW_2356 1 * rowA 2 8 1 + yW_2356 2 * rowA 2 8 2 + yW_2356 3 * rowA 2 8 3 + yW_2356 4 * rowA 2 8 4 + yW_2356 5 * rowA 2 8 5 + yW_2356 6 * rowA 2 8 6 + yW_2356 7 * rowA 2 8 7 + yW_2356 8 * rowA 2 8 8 ≤ db_2356 2 8 := by
  have hleft : yW_2356 0 * rowA 2 8 0 + yW_2356 1 * rowA 2 8 1 + yW_2356 2 * rowA 2 8 2 + yW_2356 3 * rowA 2 8 3 + yW_2356 4 * rowA 2 8 4 + yW_2356 5 * rowA 2 8 5 + yW_2356 6 * rowA 2 8 6 + yW_2356 7 * rowA 2 8 7 + yW_2356 8 * rowA 2 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 2 8 = (3 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_2_9 :
    yW_2356 0 * rowA 2 9 0 + yW_2356 1 * rowA 2 9 1 + yW_2356 2 * rowA 2 9 2 + yW_2356 3 * rowA 2 9 3 + yW_2356 4 * rowA 2 9 4 + yW_2356 5 * rowA 2 9 5 + yW_2356 6 * rowA 2 9 6 + yW_2356 7 * rowA 2 9 7 + yW_2356 8 * rowA 2 9 8 ≤ db_2356 2 9 := by
  have hleft : yW_2356 0 * rowA 2 9 0 + yW_2356 1 * rowA 2 9 1 + yW_2356 2 * rowA 2 9 2 + yW_2356 3 * rowA 2 9 3 + yW_2356 4 * rowA 2 9 4 + yW_2356 5 * rowA 2 9 5 + yW_2356 6 * rowA 2 9 6 + yW_2356 7 * rowA 2 9 7 + yW_2356 8 * rowA 2 9 8 = (15 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 2 9 = (1 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_3_0 :
    yW_2356 0 * rowA 3 0 0 + yW_2356 1 * rowA 3 0 1 + yW_2356 2 * rowA 3 0 2 + yW_2356 3 * rowA 3 0 3 + yW_2356 4 * rowA 3 0 4 + yW_2356 5 * rowA 3 0 5 + yW_2356 6 * rowA 3 0 6 + yW_2356 7 * rowA 3 0 7 + yW_2356 8 * rowA 3 0 8 ≤ db_2356 3 0 := by
  have hleft : yW_2356 0 * rowA 3 0 0 + yW_2356 1 * rowA 3 0 1 + yW_2356 2 * rowA 3 0 2 + yW_2356 3 * rowA 3 0 3 + yW_2356 4 * rowA 3 0 4 + yW_2356 5 * rowA 3 0 5 + yW_2356 6 * rowA 3 0 6 + yW_2356 7 * rowA 3 0 7 + yW_2356 8 * rowA 3 0 8 = (-1 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 3 0 = (-1 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_3_1 :
    yW_2356 0 * rowA 3 1 0 + yW_2356 1 * rowA 3 1 1 + yW_2356 2 * rowA 3 1 2 + yW_2356 3 * rowA 3 1 3 + yW_2356 4 * rowA 3 1 4 + yW_2356 5 * rowA 3 1 5 + yW_2356 6 * rowA 3 1 6 + yW_2356 7 * rowA 3 1 7 + yW_2356 8 * rowA 3 1 8 ≤ db_2356 3 1 := by
  have hleft : yW_2356 0 * rowA 3 1 0 + yW_2356 1 * rowA 3 1 1 + yW_2356 2 * rowA 3 1 2 + yW_2356 3 * rowA 3 1 3 + yW_2356 4 * rowA 3 1 4 + yW_2356 5 * rowA 3 1 5 + yW_2356 6 * rowA 3 1 6 + yW_2356 7 * rowA 3 1 7 + yW_2356 8 * rowA 3 1 8 = (-1 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 3 1 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_3_2 :
    yW_2356 0 * rowA 3 2 0 + yW_2356 1 * rowA 3 2 1 + yW_2356 2 * rowA 3 2 2 + yW_2356 3 * rowA 3 2 3 + yW_2356 4 * rowA 3 2 4 + yW_2356 5 * rowA 3 2 5 + yW_2356 6 * rowA 3 2 6 + yW_2356 7 * rowA 3 2 7 + yW_2356 8 * rowA 3 2 8 ≤ db_2356 3 2 := by
  have hleft : yW_2356 0 * rowA 3 2 0 + yW_2356 1 * rowA 3 2 1 + yW_2356 2 * rowA 3 2 2 + yW_2356 3 * rowA 3 2 3 + yW_2356 4 * rowA 3 2 4 + yW_2356 5 * rowA 3 2 5 + yW_2356 6 * rowA 3 2 6 + yW_2356 7 * rowA 3 2 7 + yW_2356 8 * rowA 3 2 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 3 2 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_3_3 :
    yW_2356 0 * rowA 3 3 0 + yW_2356 1 * rowA 3 3 1 + yW_2356 2 * rowA 3 3 2 + yW_2356 3 * rowA 3 3 3 + yW_2356 4 * rowA 3 3 4 + yW_2356 5 * rowA 3 3 5 + yW_2356 6 * rowA 3 3 6 + yW_2356 7 * rowA 3 3 7 + yW_2356 8 * rowA 3 3 8 ≤ db_2356 3 3 := by
  have hleft : yW_2356 0 * rowA 3 3 0 + yW_2356 1 * rowA 3 3 1 + yW_2356 2 * rowA 3 3 2 + yW_2356 3 * rowA 3 3 3 + yW_2356 4 * rowA 3 3 4 + yW_2356 5 * rowA 3 3 5 + yW_2356 6 * rowA 3 3 6 + yW_2356 7 * rowA 3 3 7 + yW_2356 8 * rowA 3 3 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 3 3 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_3_4 :
    yW_2356 0 * rowA 3 4 0 + yW_2356 1 * rowA 3 4 1 + yW_2356 2 * rowA 3 4 2 + yW_2356 3 * rowA 3 4 3 + yW_2356 4 * rowA 3 4 4 + yW_2356 5 * rowA 3 4 5 + yW_2356 6 * rowA 3 4 6 + yW_2356 7 * rowA 3 4 7 + yW_2356 8 * rowA 3 4 8 ≤ db_2356 3 4 := by
  have hleft : yW_2356 0 * rowA 3 4 0 + yW_2356 1 * rowA 3 4 1 + yW_2356 2 * rowA 3 4 2 + yW_2356 3 * rowA 3 4 3 + yW_2356 4 * rowA 3 4 4 + yW_2356 5 * rowA 3 4 5 + yW_2356 6 * rowA 3 4 6 + yW_2356 7 * rowA 3 4 7 + yW_2356 8 * rowA 3 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 3 4 = (1 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_3_5 :
    yW_2356 0 * rowA 3 5 0 + yW_2356 1 * rowA 3 5 1 + yW_2356 2 * rowA 3 5 2 + yW_2356 3 * rowA 3 5 3 + yW_2356 4 * rowA 3 5 4 + yW_2356 5 * rowA 3 5 5 + yW_2356 6 * rowA 3 5 6 + yW_2356 7 * rowA 3 5 7 + yW_2356 8 * rowA 3 5 8 ≤ db_2356 3 5 := by
  have hleft : yW_2356 0 * rowA 3 5 0 + yW_2356 1 * rowA 3 5 1 + yW_2356 2 * rowA 3 5 2 + yW_2356 3 * rowA 3 5 3 + yW_2356 4 * rowA 3 5 4 + yW_2356 5 * rowA 3 5 5 + yW_2356 6 * rowA 3 5 6 + yW_2356 7 * rowA 3 5 7 + yW_2356 8 * rowA 3 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 3 5 = (7 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_3_6 :
    yW_2356 0 * rowA 3 6 0 + yW_2356 1 * rowA 3 6 1 + yW_2356 2 * rowA 3 6 2 + yW_2356 3 * rowA 3 6 3 + yW_2356 4 * rowA 3 6 4 + yW_2356 5 * rowA 3 6 5 + yW_2356 6 * rowA 3 6 6 + yW_2356 7 * rowA 3 6 7 + yW_2356 8 * rowA 3 6 8 ≤ db_2356 3 6 := by
  have hleft : yW_2356 0 * rowA 3 6 0 + yW_2356 1 * rowA 3 6 1 + yW_2356 2 * rowA 3 6 2 + yW_2356 3 * rowA 3 6 3 + yW_2356 4 * rowA 3 6 4 + yW_2356 5 * rowA 3 6 5 + yW_2356 6 * rowA 3 6 6 + yW_2356 7 * rowA 3 6 7 + yW_2356 8 * rowA 3 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 3 6 = (1 : ℚ) / 2 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_3_7 :
    yW_2356 0 * rowA 3 7 0 + yW_2356 1 * rowA 3 7 1 + yW_2356 2 * rowA 3 7 2 + yW_2356 3 * rowA 3 7 3 + yW_2356 4 * rowA 3 7 4 + yW_2356 5 * rowA 3 7 5 + yW_2356 6 * rowA 3 7 6 + yW_2356 7 * rowA 3 7 7 + yW_2356 8 * rowA 3 7 8 ≤ db_2356 3 7 := by
  have hleft : yW_2356 0 * rowA 3 7 0 + yW_2356 1 * rowA 3 7 1 + yW_2356 2 * rowA 3 7 2 + yW_2356 3 * rowA 3 7 3 + yW_2356 4 * rowA 3 7 4 + yW_2356 5 * rowA 3 7 5 + yW_2356 6 * rowA 3 7 6 + yW_2356 7 * rowA 3 7 7 + yW_2356 8 * rowA 3 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 3 7 = (5 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_3_8 :
    yW_2356 0 * rowA 3 8 0 + yW_2356 1 * rowA 3 8 1 + yW_2356 2 * rowA 3 8 2 + yW_2356 3 * rowA 3 8 3 + yW_2356 4 * rowA 3 8 4 + yW_2356 5 * rowA 3 8 5 + yW_2356 6 * rowA 3 8 6 + yW_2356 7 * rowA 3 8 7 + yW_2356 8 * rowA 3 8 8 ≤ db_2356 3 8 := by
  have hleft : yW_2356 0 * rowA 3 8 0 + yW_2356 1 * rowA 3 8 1 + yW_2356 2 * rowA 3 8 2 + yW_2356 3 * rowA 3 8 3 + yW_2356 4 * rowA 3 8 4 + yW_2356 5 * rowA 3 8 5 + yW_2356 6 * rowA 3 8 6 + yW_2356 7 * rowA 3 8 7 + yW_2356 8 * rowA 3 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 3 8 = (11 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_3_9 :
    yW_2356 0 * rowA 3 9 0 + yW_2356 1 * rowA 3 9 1 + yW_2356 2 * rowA 3 9 2 + yW_2356 3 * rowA 3 9 3 + yW_2356 4 * rowA 3 9 4 + yW_2356 5 * rowA 3 9 5 + yW_2356 6 * rowA 3 9 6 + yW_2356 7 * rowA 3 9 7 + yW_2356 8 * rowA 3 9 8 ≤ db_2356 3 9 := by
  have hleft : yW_2356 0 * rowA 3 9 0 + yW_2356 1 * rowA 3 9 1 + yW_2356 2 * rowA 3 9 2 + yW_2356 3 * rowA 3 9 3 + yW_2356 4 * rowA 3 9 4 + yW_2356 5 * rowA 3 9 5 + yW_2356 6 * rowA 3 9 6 + yW_2356 7 * rowA 3 9 7 + yW_2356 8 * rowA 3 9 8 = (15 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 3 9 = (15 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_4_0 :
    yW_2356 0 * rowA 4 0 0 + yW_2356 1 * rowA 4 0 1 + yW_2356 2 * rowA 4 0 2 + yW_2356 3 * rowA 4 0 3 + yW_2356 4 * rowA 4 0 4 + yW_2356 5 * rowA 4 0 5 + yW_2356 6 * rowA 4 0 6 + yW_2356 7 * rowA 4 0 7 + yW_2356 8 * rowA 4 0 8 ≤ db_2356 4 0 := by
  have hleft : yW_2356 0 * rowA 4 0 0 + yW_2356 1 * rowA 4 0 1 + yW_2356 2 * rowA 4 0 2 + yW_2356 3 * rowA 4 0 3 + yW_2356 4 * rowA 4 0 4 + yW_2356 5 * rowA 4 0 5 + yW_2356 6 * rowA 4 0 6 + yW_2356 7 * rowA 4 0 7 + yW_2356 8 * rowA 4 0 8 = (-5 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 4 0 = (-1 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_4_1 :
    yW_2356 0 * rowA 4 1 0 + yW_2356 1 * rowA 4 1 1 + yW_2356 2 * rowA 4 1 2 + yW_2356 3 * rowA 4 1 3 + yW_2356 4 * rowA 4 1 4 + yW_2356 5 * rowA 4 1 5 + yW_2356 6 * rowA 4 1 6 + yW_2356 7 * rowA 4 1 7 + yW_2356 8 * rowA 4 1 8 ≤ db_2356 4 1 := by
  have hleft : yW_2356 0 * rowA 4 1 0 + yW_2356 1 * rowA 4 1 1 + yW_2356 2 * rowA 4 1 2 + yW_2356 3 * rowA 4 1 3 + yW_2356 4 * rowA 4 1 4 + yW_2356 5 * rowA 4 1 5 + yW_2356 6 * rowA 4 1 6 + yW_2356 7 * rowA 4 1 7 + yW_2356 8 * rowA 4 1 8 = (-5 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 4 1 = (-1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_4_2 :
    yW_2356 0 * rowA 4 2 0 + yW_2356 1 * rowA 4 2 1 + yW_2356 2 * rowA 4 2 2 + yW_2356 3 * rowA 4 2 3 + yW_2356 4 * rowA 4 2 4 + yW_2356 5 * rowA 4 2 5 + yW_2356 6 * rowA 4 2 6 + yW_2356 7 * rowA 4 2 7 + yW_2356 8 * rowA 4 2 8 ≤ db_2356 4 2 := by
  have hleft : yW_2356 0 * rowA 4 2 0 + yW_2356 1 * rowA 4 2 1 + yW_2356 2 * rowA 4 2 2 + yW_2356 3 * rowA 4 2 3 + yW_2356 4 * rowA 4 2 4 + yW_2356 5 * rowA 4 2 5 + yW_2356 6 * rowA 4 2 6 + yW_2356 7 * rowA 4 2 7 + yW_2356 8 * rowA 4 2 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 4 2 = (-1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_4_3 :
    yW_2356 0 * rowA 4 3 0 + yW_2356 1 * rowA 4 3 1 + yW_2356 2 * rowA 4 3 2 + yW_2356 3 * rowA 4 3 3 + yW_2356 4 * rowA 4 3 4 + yW_2356 5 * rowA 4 3 5 + yW_2356 6 * rowA 4 3 6 + yW_2356 7 * rowA 4 3 7 + yW_2356 8 * rowA 4 3 8 ≤ db_2356 4 3 := by
  have hleft : yW_2356 0 * rowA 4 3 0 + yW_2356 1 * rowA 4 3 1 + yW_2356 2 * rowA 4 3 2 + yW_2356 3 * rowA 4 3 3 + yW_2356 4 * rowA 4 3 4 + yW_2356 5 * rowA 4 3 5 + yW_2356 6 * rowA 4 3 6 + yW_2356 7 * rowA 4 3 7 + yW_2356 8 * rowA 4 3 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 4 3 = (-1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_4_4 :
    yW_2356 0 * rowA 4 4 0 + yW_2356 1 * rowA 4 4 1 + yW_2356 2 * rowA 4 4 2 + yW_2356 3 * rowA 4 4 3 + yW_2356 4 * rowA 4 4 4 + yW_2356 5 * rowA 4 4 5 + yW_2356 6 * rowA 4 4 6 + yW_2356 7 * rowA 4 4 7 + yW_2356 8 * rowA 4 4 8 ≤ db_2356 4 4 := by
  have hleft : yW_2356 0 * rowA 4 4 0 + yW_2356 1 * rowA 4 4 1 + yW_2356 2 * rowA 4 4 2 + yW_2356 3 * rowA 4 4 3 + yW_2356 4 * rowA 4 4 4 + yW_2356 5 * rowA 4 4 5 + yW_2356 6 * rowA 4 4 6 + yW_2356 7 * rowA 4 4 7 + yW_2356 8 * rowA 4 4 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 4 4 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_4_5 :
    yW_2356 0 * rowA 4 5 0 + yW_2356 1 * rowA 4 5 1 + yW_2356 2 * rowA 4 5 2 + yW_2356 3 * rowA 4 5 3 + yW_2356 4 * rowA 4 5 4 + yW_2356 5 * rowA 4 5 5 + yW_2356 6 * rowA 4 5 6 + yW_2356 7 * rowA 4 5 7 + yW_2356 8 * rowA 4 5 8 ≤ db_2356 4 5 := by
  have hleft : yW_2356 0 * rowA 4 5 0 + yW_2356 1 * rowA 4 5 1 + yW_2356 2 * rowA 4 5 2 + yW_2356 3 * rowA 4 5 3 + yW_2356 4 * rowA 4 5 4 + yW_2356 5 * rowA 4 5 5 + yW_2356 6 * rowA 4 5 6 + yW_2356 7 * rowA 4 5 7 + yW_2356 8 * rowA 4 5 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 4 5 = (1 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_4_6 :
    yW_2356 0 * rowA 4 6 0 + yW_2356 1 * rowA 4 6 1 + yW_2356 2 * rowA 4 6 2 + yW_2356 3 * rowA 4 6 3 + yW_2356 4 * rowA 4 6 4 + yW_2356 5 * rowA 4 6 5 + yW_2356 6 * rowA 4 6 6 + yW_2356 7 * rowA 4 6 7 + yW_2356 8 * rowA 4 6 8 ≤ db_2356 4 6 := by
  have hleft : yW_2356 0 * rowA 4 6 0 + yW_2356 1 * rowA 4 6 1 + yW_2356 2 * rowA 4 6 2 + yW_2356 3 * rowA 4 6 3 + yW_2356 4 * rowA 4 6 4 + yW_2356 5 * rowA 4 6 5 + yW_2356 6 * rowA 4 6 6 + yW_2356 7 * rowA 4 6 7 + yW_2356 8 * rowA 4 6 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 4 6 = (5 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_4_7 :
    yW_2356 0 * rowA 4 7 0 + yW_2356 1 * rowA 4 7 1 + yW_2356 2 * rowA 4 7 2 + yW_2356 3 * rowA 4 7 3 + yW_2356 4 * rowA 4 7 4 + yW_2356 5 * rowA 4 7 5 + yW_2356 6 * rowA 4 7 6 + yW_2356 7 * rowA 4 7 7 + yW_2356 8 * rowA 4 7 8 ≤ db_2356 4 7 := by
  have hleft : yW_2356 0 * rowA 4 7 0 + yW_2356 1 * rowA 4 7 1 + yW_2356 2 * rowA 4 7 2 + yW_2356 3 * rowA 4 7 3 + yW_2356 4 * rowA 4 7 4 + yW_2356 5 * rowA 4 7 5 + yW_2356 6 * rowA 4 7 6 + yW_2356 7 * rowA 4 7 7 + yW_2356 8 * rowA 4 7 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 4 7 = (1 : ℚ) / 2 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_4_8 :
    yW_2356 0 * rowA 4 8 0 + yW_2356 1 * rowA 4 8 1 + yW_2356 2 * rowA 4 8 2 + yW_2356 3 * rowA 4 8 3 + yW_2356 4 * rowA 4 8 4 + yW_2356 5 * rowA 4 8 5 + yW_2356 6 * rowA 4 8 6 + yW_2356 7 * rowA 4 8 7 + yW_2356 8 * rowA 4 8 8 ≤ db_2356 4 8 := by
  have hleft : yW_2356 0 * rowA 4 8 0 + yW_2356 1 * rowA 4 8 1 + yW_2356 2 * rowA 4 8 2 + yW_2356 3 * rowA 4 8 3 + yW_2356 4 * rowA 4 8 4 + yW_2356 5 * rowA 4 8 5 + yW_2356 6 * rowA 4 8 6 + yW_2356 7 * rowA 4 8 7 + yW_2356 8 * rowA 4 8 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 4 8 = (1 : ℚ) / 2 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_4_9 :
    yW_2356 0 * rowA 4 9 0 + yW_2356 1 * rowA 4 9 1 + yW_2356 2 * rowA 4 9 2 + yW_2356 3 * rowA 4 9 3 + yW_2356 4 * rowA 4 9 4 + yW_2356 5 * rowA 4 9 5 + yW_2356 6 * rowA 4 9 6 + yW_2356 7 * rowA 4 9 7 + yW_2356 8 * rowA 4 9 8 ≤ db_2356 4 9 := by
  have hleft : yW_2356 0 * rowA 4 9 0 + yW_2356 1 * rowA 4 9 1 + yW_2356 2 * rowA 4 9 2 + yW_2356 3 * rowA 4 9 3 + yW_2356 4 * rowA 4 9 4 + yW_2356 5 * rowA 4 9 5 + yW_2356 6 * rowA 4 9 6 + yW_2356 7 * rowA 4 9 7 + yW_2356 8 * rowA 4 9 8 = (11 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 4 9 = (3 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_5_0 :
    yW_2356 0 * rowA 5 0 0 + yW_2356 1 * rowA 5 0 1 + yW_2356 2 * rowA 5 0 2 + yW_2356 3 * rowA 5 0 3 + yW_2356 4 * rowA 5 0 4 + yW_2356 5 * rowA 5 0 5 + yW_2356 6 * rowA 5 0 6 + yW_2356 7 * rowA 5 0 7 + yW_2356 8 * rowA 5 0 8 ≤ db_2356 5 0 := by
  have hleft : yW_2356 0 * rowA 5 0 0 + yW_2356 1 * rowA 5 0 1 + yW_2356 2 * rowA 5 0 2 + yW_2356 3 * rowA 5 0 3 + yW_2356 4 * rowA 5 0 4 + yW_2356 5 * rowA 5 0 5 + yW_2356 6 * rowA 5 0 6 + yW_2356 7 * rowA 5 0 7 + yW_2356 8 * rowA 5 0 8 = (-7 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 5 0 = (-7 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_5_1 :
    yW_2356 0 * rowA 5 1 0 + yW_2356 1 * rowA 5 1 1 + yW_2356 2 * rowA 5 1 2 + yW_2356 3 * rowA 5 1 3 + yW_2356 4 * rowA 5 1 4 + yW_2356 5 * rowA 5 1 5 + yW_2356 6 * rowA 5 1 6 + yW_2356 7 * rowA 5 1 7 + yW_2356 8 * rowA 5 1 8 ≤ db_2356 5 1 := by
  have hleft : yW_2356 0 * rowA 5 1 0 + yW_2356 1 * rowA 5 1 1 + yW_2356 2 * rowA 5 1 2 + yW_2356 3 * rowA 5 1 3 + yW_2356 4 * rowA 5 1 4 + yW_2356 5 * rowA 5 1 5 + yW_2356 6 * rowA 5 1 6 + yW_2356 7 * rowA 5 1 7 + yW_2356 8 * rowA 5 1 8 = (-7 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 5 1 = (-3 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_5_2 :
    yW_2356 0 * rowA 5 2 0 + yW_2356 1 * rowA 5 2 1 + yW_2356 2 * rowA 5 2 2 + yW_2356 3 * rowA 5 2 3 + yW_2356 4 * rowA 5 2 4 + yW_2356 5 * rowA 5 2 5 + yW_2356 6 * rowA 5 2 6 + yW_2356 7 * rowA 5 2 7 + yW_2356 8 * rowA 5 2 8 ≤ db_2356 5 2 := by
  have hleft : yW_2356 0 * rowA 5 2 0 + yW_2356 1 * rowA 5 2 1 + yW_2356 2 * rowA 5 2 2 + yW_2356 3 * rowA 5 2 3 + yW_2356 4 * rowA 5 2 4 + yW_2356 5 * rowA 5 2 5 + yW_2356 6 * rowA 5 2 6 + yW_2356 7 * rowA 5 2 7 + yW_2356 8 * rowA 5 2 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 5 2 = (-3 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_5_3 :
    yW_2356 0 * rowA 5 3 0 + yW_2356 1 * rowA 5 3 1 + yW_2356 2 * rowA 5 3 2 + yW_2356 3 * rowA 5 3 3 + yW_2356 4 * rowA 5 3 4 + yW_2356 5 * rowA 5 3 5 + yW_2356 6 * rowA 5 3 6 + yW_2356 7 * rowA 5 3 7 + yW_2356 8 * rowA 5 3 8 ≤ db_2356 5 3 := by
  have hleft : yW_2356 0 * rowA 5 3 0 + yW_2356 1 * rowA 5 3 1 + yW_2356 2 * rowA 5 3 2 + yW_2356 3 * rowA 5 3 3 + yW_2356 4 * rowA 5 3 4 + yW_2356 5 * rowA 5 3 5 + yW_2356 6 * rowA 5 3 6 + yW_2356 7 * rowA 5 3 7 + yW_2356 8 * rowA 5 3 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 5 3 = (-3 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_5_4 :
    yW_2356 0 * rowA 5 4 0 + yW_2356 1 * rowA 5 4 1 + yW_2356 2 * rowA 5 4 2 + yW_2356 3 * rowA 5 4 3 + yW_2356 4 * rowA 5 4 4 + yW_2356 5 * rowA 5 4 5 + yW_2356 6 * rowA 5 4 6 + yW_2356 7 * rowA 5 4 7 + yW_2356 8 * rowA 5 4 8 ≤ db_2356 5 4 := by
  have hleft : yW_2356 0 * rowA 5 4 0 + yW_2356 1 * rowA 5 4 1 + yW_2356 2 * rowA 5 4 2 + yW_2356 3 * rowA 5 4 3 + yW_2356 4 * rowA 5 4 4 + yW_2356 5 * rowA 5 4 5 + yW_2356 6 * rowA 5 4 6 + yW_2356 7 * rowA 5 4 7 + yW_2356 8 * rowA 5 4 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 5 4 = (-1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_5_5 :
    yW_2356 0 * rowA 5 5 0 + yW_2356 1 * rowA 5 5 1 + yW_2356 2 * rowA 5 5 2 + yW_2356 3 * rowA 5 5 3 + yW_2356 4 * rowA 5 5 4 + yW_2356 5 * rowA 5 5 5 + yW_2356 6 * rowA 5 5 6 + yW_2356 7 * rowA 5 5 7 + yW_2356 8 * rowA 5 5 8 ≤ db_2356 5 5 := by
  have hleft : yW_2356 0 * rowA 5 5 0 + yW_2356 1 * rowA 5 5 1 + yW_2356 2 * rowA 5 5 2 + yW_2356 3 * rowA 5 5 3 + yW_2356 4 * rowA 5 5 4 + yW_2356 5 * rowA 5 5 5 + yW_2356 6 * rowA 5 5 6 + yW_2356 7 * rowA 5 5 7 + yW_2356 8 * rowA 5 5 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 5 5 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_5_6 :
    yW_2356 0 * rowA 5 6 0 + yW_2356 1 * rowA 5 6 1 + yW_2356 2 * rowA 5 6 2 + yW_2356 3 * rowA 5 6 3 + yW_2356 4 * rowA 5 6 4 + yW_2356 5 * rowA 5 6 5 + yW_2356 6 * rowA 5 6 6 + yW_2356 7 * rowA 5 6 7 + yW_2356 8 * rowA 5 6 8 ≤ db_2356 5 6 := by
  have hleft : yW_2356 0 * rowA 5 6 0 + yW_2356 1 * rowA 5 6 1 + yW_2356 2 * rowA 5 6 2 + yW_2356 3 * rowA 5 6 3 + yW_2356 4 * rowA 5 6 4 + yW_2356 5 * rowA 5 6 5 + yW_2356 6 * rowA 5 6 6 + yW_2356 7 * rowA 5 6 7 + yW_2356 8 * rowA 5 6 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 5 6 = (1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_5_7 :
    yW_2356 0 * rowA 5 7 0 + yW_2356 1 * rowA 5 7 1 + yW_2356 2 * rowA 5 7 2 + yW_2356 3 * rowA 5 7 3 + yW_2356 4 * rowA 5 7 4 + yW_2356 5 * rowA 5 7 5 + yW_2356 6 * rowA 5 7 6 + yW_2356 7 * rowA 5 7 7 + yW_2356 8 * rowA 5 7 8 ≤ db_2356 5 7 := by
  have hleft : yW_2356 0 * rowA 5 7 0 + yW_2356 1 * rowA 5 7 1 + yW_2356 2 * rowA 5 7 2 + yW_2356 3 * rowA 5 7 3 + yW_2356 4 * rowA 5 7 4 + yW_2356 5 * rowA 5 7 5 + yW_2356 6 * rowA 5 7 6 + yW_2356 7 * rowA 5 7 7 + yW_2356 8 * rowA 5 7 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 5 7 = (1 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_5_8 :
    yW_2356 0 * rowA 5 8 0 + yW_2356 1 * rowA 5 8 1 + yW_2356 2 * rowA 5 8 2 + yW_2356 3 * rowA 5 8 3 + yW_2356 4 * rowA 5 8 4 + yW_2356 5 * rowA 5 8 5 + yW_2356 6 * rowA 5 8 6 + yW_2356 7 * rowA 5 8 7 + yW_2356 8 * rowA 5 8 8 ≤ db_2356 5 8 := by
  have hleft : yW_2356 0 * rowA 5 8 0 + yW_2356 1 * rowA 5 8 1 + yW_2356 2 * rowA 5 8 2 + yW_2356 3 * rowA 5 8 3 + yW_2356 4 * rowA 5 8 4 + yW_2356 5 * rowA 5 8 5 + yW_2356 6 * rowA 5 8 6 + yW_2356 7 * rowA 5 8 7 + yW_2356 8 * rowA 5 8 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 5 8 = (1 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_5_9 :
    yW_2356 0 * rowA 5 9 0 + yW_2356 1 * rowA 5 9 1 + yW_2356 2 * rowA 5 9 2 + yW_2356 3 * rowA 5 9 3 + yW_2356 4 * rowA 5 9 4 + yW_2356 5 * rowA 5 9 5 + yW_2356 6 * rowA 5 9 6 + yW_2356 7 * rowA 5 9 7 + yW_2356 8 * rowA 5 9 8 ≤ db_2356 5 9 := by
  have hleft : yW_2356 0 * rowA 5 9 0 + yW_2356 1 * rowA 5 9 1 + yW_2356 2 * rowA 5 9 2 + yW_2356 3 * rowA 5 9 3 + yW_2356 4 * rowA 5 9 4 + yW_2356 5 * rowA 5 9 5 + yW_2356 6 * rowA 5 9 6 + yW_2356 7 * rowA 5 9 7 + yW_2356 8 * rowA 5 9 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 5 9 = (9 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_6_0 :
    yW_2356 0 * rowA 6 0 0 + yW_2356 1 * rowA 6 0 1 + yW_2356 2 * rowA 6 0 2 + yW_2356 3 * rowA 6 0 3 + yW_2356 4 * rowA 6 0 4 + yW_2356 5 * rowA 6 0 5 + yW_2356 6 * rowA 6 0 6 + yW_2356 7 * rowA 6 0 7 + yW_2356 8 * rowA 6 0 8 ≤ db_2356 6 0 := by
  have hleft : yW_2356 0 * rowA 6 0 0 + yW_2356 1 * rowA 6 0 1 + yW_2356 2 * rowA 6 0 2 + yW_2356 3 * rowA 6 0 3 + yW_2356 4 * rowA 6 0 4 + yW_2356 5 * rowA 6 0 5 + yW_2356 6 * rowA 6 0 6 + yW_2356 7 * rowA 6 0 7 + yW_2356 8 * rowA 6 0 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 6 0 = (-7 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_6_1 :
    yW_2356 0 * rowA 6 1 0 + yW_2356 1 * rowA 6 1 1 + yW_2356 2 * rowA 6 1 2 + yW_2356 3 * rowA 6 1 3 + yW_2356 4 * rowA 6 1 4 + yW_2356 5 * rowA 6 1 5 + yW_2356 6 * rowA 6 1 6 + yW_2356 7 * rowA 6 1 7 + yW_2356 8 * rowA 6 1 8 ≤ db_2356 6 1 := by
  have hleft : yW_2356 0 * rowA 6 1 0 + yW_2356 1 * rowA 6 1 1 + yW_2356 2 * rowA 6 1 2 + yW_2356 3 * rowA 6 1 3 + yW_2356 4 * rowA 6 1 4 + yW_2356 5 * rowA 6 1 5 + yW_2356 6 * rowA 6 1 6 + yW_2356 7 * rowA 6 1 7 + yW_2356 8 * rowA 6 1 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 6 1 = (-3 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_6_2 :
    yW_2356 0 * rowA 6 2 0 + yW_2356 1 * rowA 6 2 1 + yW_2356 2 * rowA 6 2 2 + yW_2356 3 * rowA 6 2 3 + yW_2356 4 * rowA 6 2 4 + yW_2356 5 * rowA 6 2 5 + yW_2356 6 * rowA 6 2 6 + yW_2356 7 * rowA 6 2 7 + yW_2356 8 * rowA 6 2 8 ≤ db_2356 6 2 := by
  have hleft : yW_2356 0 * rowA 6 2 0 + yW_2356 1 * rowA 6 2 1 + yW_2356 2 * rowA 6 2 2 + yW_2356 3 * rowA 6 2 3 + yW_2356 4 * rowA 6 2 4 + yW_2356 5 * rowA 6 2 5 + yW_2356 6 * rowA 6 2 6 + yW_2356 7 * rowA 6 2 7 + yW_2356 8 * rowA 6 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 6 2 = (-3 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_6_3 :
    yW_2356 0 * rowA 6 3 0 + yW_2356 1 * rowA 6 3 1 + yW_2356 2 * rowA 6 3 2 + yW_2356 3 * rowA 6 3 3 + yW_2356 4 * rowA 6 3 4 + yW_2356 5 * rowA 6 3 5 + yW_2356 6 * rowA 6 3 6 + yW_2356 7 * rowA 6 3 7 + yW_2356 8 * rowA 6 3 8 ≤ db_2356 6 3 := by
  have hleft : yW_2356 0 * rowA 6 3 0 + yW_2356 1 * rowA 6 3 1 + yW_2356 2 * rowA 6 3 2 + yW_2356 3 * rowA 6 3 3 + yW_2356 4 * rowA 6 3 4 + yW_2356 5 * rowA 6 3 5 + yW_2356 6 * rowA 6 3 6 + yW_2356 7 * rowA 6 3 7 + yW_2356 8 * rowA 6 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 6 3 = (-3 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_6_4 :
    yW_2356 0 * rowA 6 4 0 + yW_2356 1 * rowA 6 4 1 + yW_2356 2 * rowA 6 4 2 + yW_2356 3 * rowA 6 4 3 + yW_2356 4 * rowA 6 4 4 + yW_2356 5 * rowA 6 4 5 + yW_2356 6 * rowA 6 4 6 + yW_2356 7 * rowA 6 4 7 + yW_2356 8 * rowA 6 4 8 ≤ db_2356 6 4 := by
  have hleft : yW_2356 0 * rowA 6 4 0 + yW_2356 1 * rowA 6 4 1 + yW_2356 2 * rowA 6 4 2 + yW_2356 3 * rowA 6 4 3 + yW_2356 4 * rowA 6 4 4 + yW_2356 5 * rowA 6 4 5 + yW_2356 6 * rowA 6 4 6 + yW_2356 7 * rowA 6 4 7 + yW_2356 8 * rowA 6 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 6 4 = (-1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_6_5 :
    yW_2356 0 * rowA 6 5 0 + yW_2356 1 * rowA 6 5 1 + yW_2356 2 * rowA 6 5 2 + yW_2356 3 * rowA 6 5 3 + yW_2356 4 * rowA 6 5 4 + yW_2356 5 * rowA 6 5 5 + yW_2356 6 * rowA 6 5 6 + yW_2356 7 * rowA 6 5 7 + yW_2356 8 * rowA 6 5 8 ≤ db_2356 6 5 := by
  have hleft : yW_2356 0 * rowA 6 5 0 + yW_2356 1 * rowA 6 5 1 + yW_2356 2 * rowA 6 5 2 + yW_2356 3 * rowA 6 5 3 + yW_2356 4 * rowA 6 5 4 + yW_2356 5 * rowA 6 5 5 + yW_2356 6 * rowA 6 5 6 + yW_2356 7 * rowA 6 5 7 + yW_2356 8 * rowA 6 5 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 6 5 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_6_6 :
    yW_2356 0 * rowA 6 6 0 + yW_2356 1 * rowA 6 6 1 + yW_2356 2 * rowA 6 6 2 + yW_2356 3 * rowA 6 6 3 + yW_2356 4 * rowA 6 6 4 + yW_2356 5 * rowA 6 6 5 + yW_2356 6 * rowA 6 6 6 + yW_2356 7 * rowA 6 6 7 + yW_2356 8 * rowA 6 6 8 ≤ db_2356 6 6 := by
  have hleft : yW_2356 0 * rowA 6 6 0 + yW_2356 1 * rowA 6 6 1 + yW_2356 2 * rowA 6 6 2 + yW_2356 3 * rowA 6 6 3 + yW_2356 4 * rowA 6 6 4 + yW_2356 5 * rowA 6 6 5 + yW_2356 6 * rowA 6 6 6 + yW_2356 7 * rowA 6 6 7 + yW_2356 8 * rowA 6 6 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 6 6 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_6_7 :
    yW_2356 0 * rowA 6 7 0 + yW_2356 1 * rowA 6 7 1 + yW_2356 2 * rowA 6 7 2 + yW_2356 3 * rowA 6 7 3 + yW_2356 4 * rowA 6 7 4 + yW_2356 5 * rowA 6 7 5 + yW_2356 6 * rowA 6 7 6 + yW_2356 7 * rowA 6 7 7 + yW_2356 8 * rowA 6 7 8 ≤ db_2356 6 7 := by
  have hleft : yW_2356 0 * rowA 6 7 0 + yW_2356 1 * rowA 6 7 1 + yW_2356 2 * rowA 6 7 2 + yW_2356 3 * rowA 6 7 3 + yW_2356 4 * rowA 6 7 4 + yW_2356 5 * rowA 6 7 5 + yW_2356 6 * rowA 6 7 6 + yW_2356 7 * rowA 6 7 7 + yW_2356 8 * rowA 6 7 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 6 7 = (1 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_6_8 :
    yW_2356 0 * rowA 6 8 0 + yW_2356 1 * rowA 6 8 1 + yW_2356 2 * rowA 6 8 2 + yW_2356 3 * rowA 6 8 3 + yW_2356 4 * rowA 6 8 4 + yW_2356 5 * rowA 6 8 5 + yW_2356 6 * rowA 6 8 6 + yW_2356 7 * rowA 6 8 7 + yW_2356 8 * rowA 6 8 8 ≤ db_2356 6 8 := by
  have hleft : yW_2356 0 * rowA 6 8 0 + yW_2356 1 * rowA 6 8 1 + yW_2356 2 * rowA 6 8 2 + yW_2356 3 * rowA 6 8 3 + yW_2356 4 * rowA 6 8 4 + yW_2356 5 * rowA 6 8 5 + yW_2356 6 * rowA 6 8 6 + yW_2356 7 * rowA 6 8 7 + yW_2356 8 * rowA 6 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 6 8 = (1 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_6_9 :
    yW_2356 0 * rowA 6 9 0 + yW_2356 1 * rowA 6 9 1 + yW_2356 2 * rowA 6 9 2 + yW_2356 3 * rowA 6 9 3 + yW_2356 4 * rowA 6 9 4 + yW_2356 5 * rowA 6 9 5 + yW_2356 6 * rowA 6 9 6 + yW_2356 7 * rowA 6 9 7 + yW_2356 8 * rowA 6 9 8 ≤ db_2356 6 9 := by
  have hleft : yW_2356 0 * rowA 6 9 0 + yW_2356 1 * rowA 6 9 1 + yW_2356 2 * rowA 6 9 2 + yW_2356 3 * rowA 6 9 3 + yW_2356 4 * rowA 6 9 4 + yW_2356 5 * rowA 6 9 5 + yW_2356 6 * rowA 6 9 6 + yW_2356 7 * rowA 6 9 7 + yW_2356 8 * rowA 6 9 8 = (7 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 6 9 = (9 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_7_0 :
    yW_2356 0 * rowA 7 0 0 + yW_2356 1 * rowA 7 0 1 + yW_2356 2 * rowA 7 0 2 + yW_2356 3 * rowA 7 0 3 + yW_2356 4 * rowA 7 0 4 + yW_2356 5 * rowA 7 0 5 + yW_2356 6 * rowA 7 0 6 + yW_2356 7 * rowA 7 0 7 + yW_2356 8 * rowA 7 0 8 ≤ db_2356 7 0 := by
  have hleft : yW_2356 0 * rowA 7 0 0 + yW_2356 1 * rowA 7 0 1 + yW_2356 2 * rowA 7 0 2 + yW_2356 3 * rowA 7 0 3 + yW_2356 4 * rowA 7 0 4 + yW_2356 5 * rowA 7 0 5 + yW_2356 6 * rowA 7 0 6 + yW_2356 7 * rowA 7 0 7 + yW_2356 8 * rowA 7 0 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 7 0 = (-9 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_7_1 :
    yW_2356 0 * rowA 7 1 0 + yW_2356 1 * rowA 7 1 1 + yW_2356 2 * rowA 7 1 2 + yW_2356 3 * rowA 7 1 3 + yW_2356 4 * rowA 7 1 4 + yW_2356 5 * rowA 7 1 5 + yW_2356 6 * rowA 7 1 6 + yW_2356 7 * rowA 7 1 7 + yW_2356 8 * rowA 7 1 8 ≤ db_2356 7 1 := by
  have hleft : yW_2356 0 * rowA 7 1 0 + yW_2356 1 * rowA 7 1 1 + yW_2356 2 * rowA 7 1 2 + yW_2356 3 * rowA 7 1 3 + yW_2356 4 * rowA 7 1 4 + yW_2356 5 * rowA 7 1 5 + yW_2356 6 * rowA 7 1 6 + yW_2356 7 * rowA 7 1 7 + yW_2356 8 * rowA 7 1 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 7 1 = (-1 : ℚ) / 2 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_7_2 :
    yW_2356 0 * rowA 7 2 0 + yW_2356 1 * rowA 7 2 1 + yW_2356 2 * rowA 7 2 2 + yW_2356 3 * rowA 7 2 3 + yW_2356 4 * rowA 7 2 4 + yW_2356 5 * rowA 7 2 5 + yW_2356 6 * rowA 7 2 6 + yW_2356 7 * rowA 7 2 7 + yW_2356 8 * rowA 7 2 8 ≤ db_2356 7 2 := by
  have hleft : yW_2356 0 * rowA 7 2 0 + yW_2356 1 * rowA 7 2 1 + yW_2356 2 * rowA 7 2 2 + yW_2356 3 * rowA 7 2 3 + yW_2356 4 * rowA 7 2 4 + yW_2356 5 * rowA 7 2 5 + yW_2356 6 * rowA 7 2 6 + yW_2356 7 * rowA 7 2 7 + yW_2356 8 * rowA 7 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 7 2 = (-1 : ℚ) / 2 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_7_3 :
    yW_2356 0 * rowA 7 3 0 + yW_2356 1 * rowA 7 3 1 + yW_2356 2 * rowA 7 3 2 + yW_2356 3 * rowA 7 3 3 + yW_2356 4 * rowA 7 3 4 + yW_2356 5 * rowA 7 3 5 + yW_2356 6 * rowA 7 3 6 + yW_2356 7 * rowA 7 3 7 + yW_2356 8 * rowA 7 3 8 ≤ db_2356 7 3 := by
  have hleft : yW_2356 0 * rowA 7 3 0 + yW_2356 1 * rowA 7 3 1 + yW_2356 2 * rowA 7 3 2 + yW_2356 3 * rowA 7 3 3 + yW_2356 4 * rowA 7 3 4 + yW_2356 5 * rowA 7 3 5 + yW_2356 6 * rowA 7 3 6 + yW_2356 7 * rowA 7 3 7 + yW_2356 8 * rowA 7 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 7 3 = (-1 : ℚ) / 2 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_7_4 :
    yW_2356 0 * rowA 7 4 0 + yW_2356 1 * rowA 7 4 1 + yW_2356 2 * rowA 7 4 2 + yW_2356 3 * rowA 7 4 3 + yW_2356 4 * rowA 7 4 4 + yW_2356 5 * rowA 7 4 5 + yW_2356 6 * rowA 7 4 6 + yW_2356 7 * rowA 7 4 7 + yW_2356 8 * rowA 7 4 8 ≤ db_2356 7 4 := by
  have hleft : yW_2356 0 * rowA 7 4 0 + yW_2356 1 * rowA 7 4 1 + yW_2356 2 * rowA 7 4 2 + yW_2356 3 * rowA 7 4 3 + yW_2356 4 * rowA 7 4 4 + yW_2356 5 * rowA 7 4 5 + yW_2356 6 * rowA 7 4 6 + yW_2356 7 * rowA 7 4 7 + yW_2356 8 * rowA 7 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 7 4 = (-1 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_7_5 :
    yW_2356 0 * rowA 7 5 0 + yW_2356 1 * rowA 7 5 1 + yW_2356 2 * rowA 7 5 2 + yW_2356 3 * rowA 7 5 3 + yW_2356 4 * rowA 7 5 4 + yW_2356 5 * rowA 7 5 5 + yW_2356 6 * rowA 7 5 6 + yW_2356 7 * rowA 7 5 7 + yW_2356 8 * rowA 7 5 8 ≤ db_2356 7 5 := by
  have hleft : yW_2356 0 * rowA 7 5 0 + yW_2356 1 * rowA 7 5 1 + yW_2356 2 * rowA 7 5 2 + yW_2356 3 * rowA 7 5 3 + yW_2356 4 * rowA 7 5 4 + yW_2356 5 * rowA 7 5 5 + yW_2356 6 * rowA 7 5 6 + yW_2356 7 * rowA 7 5 7 + yW_2356 8 * rowA 7 5 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 7 5 = (-1 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_7_6 :
    yW_2356 0 * rowA 7 6 0 + yW_2356 1 * rowA 7 6 1 + yW_2356 2 * rowA 7 6 2 + yW_2356 3 * rowA 7 6 3 + yW_2356 4 * rowA 7 6 4 + yW_2356 5 * rowA 7 6 5 + yW_2356 6 * rowA 7 6 6 + yW_2356 7 * rowA 7 6 7 + yW_2356 8 * rowA 7 6 8 ≤ db_2356 7 6 := by
  have hleft : yW_2356 0 * rowA 7 6 0 + yW_2356 1 * rowA 7 6 1 + yW_2356 2 * rowA 7 6 2 + yW_2356 3 * rowA 7 6 3 + yW_2356 4 * rowA 7 6 4 + yW_2356 5 * rowA 7 6 5 + yW_2356 6 * rowA 7 6 6 + yW_2356 7 * rowA 7 6 7 + yW_2356 8 * rowA 7 6 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 7 6 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_7_7 :
    yW_2356 0 * rowA 7 7 0 + yW_2356 1 * rowA 7 7 1 + yW_2356 2 * rowA 7 7 2 + yW_2356 3 * rowA 7 7 3 + yW_2356 4 * rowA 7 7 4 + yW_2356 5 * rowA 7 7 5 + yW_2356 6 * rowA 7 7 6 + yW_2356 7 * rowA 7 7 7 + yW_2356 8 * rowA 7 7 8 ≤ db_2356 7 7 := by
  have hleft : yW_2356 0 * rowA 7 7 0 + yW_2356 1 * rowA 7 7 1 + yW_2356 2 * rowA 7 7 2 + yW_2356 3 * rowA 7 7 3 + yW_2356 4 * rowA 7 7 4 + yW_2356 5 * rowA 7 7 5 + yW_2356 6 * rowA 7 7 6 + yW_2356 7 * rowA 7 7 7 + yW_2356 8 * rowA 7 7 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 7 7 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_7_8 :
    yW_2356 0 * rowA 7 8 0 + yW_2356 1 * rowA 7 8 1 + yW_2356 2 * rowA 7 8 2 + yW_2356 3 * rowA 7 8 3 + yW_2356 4 * rowA 7 8 4 + yW_2356 5 * rowA 7 8 5 + yW_2356 6 * rowA 7 8 6 + yW_2356 7 * rowA 7 8 7 + yW_2356 8 * rowA 7 8 8 ≤ db_2356 7 8 := by
  have hleft : yW_2356 0 * rowA 7 8 0 + yW_2356 1 * rowA 7 8 1 + yW_2356 2 * rowA 7 8 2 + yW_2356 3 * rowA 7 8 3 + yW_2356 4 * rowA 7 8 4 + yW_2356 5 * rowA 7 8 5 + yW_2356 6 * rowA 7 8 6 + yW_2356 7 * rowA 7 8 7 + yW_2356 8 * rowA 7 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 7 8 = (3 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_7_9 :
    yW_2356 0 * rowA 7 9 0 + yW_2356 1 * rowA 7 9 1 + yW_2356 2 * rowA 7 9 2 + yW_2356 3 * rowA 7 9 3 + yW_2356 4 * rowA 7 9 4 + yW_2356 5 * rowA 7 9 5 + yW_2356 6 * rowA 7 9 6 + yW_2356 7 * rowA 7 9 7 + yW_2356 8 * rowA 7 9 8 ≤ db_2356 7 9 := by
  have hleft : yW_2356 0 * rowA 7 9 0 + yW_2356 1 * rowA 7 9 1 + yW_2356 2 * rowA 7 9 2 + yW_2356 3 * rowA 7 9 3 + yW_2356 4 * rowA 7 9 4 + yW_2356 5 * rowA 7 9 5 + yW_2356 6 * rowA 7 9 6 + yW_2356 7 * rowA 7 9 7 + yW_2356 8 * rowA 7 9 8 = (7 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 7 9 = (7 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_8_0 :
    yW_2356 0 * rowA 8 0 0 + yW_2356 1 * rowA 8 0 1 + yW_2356 2 * rowA 8 0 2 + yW_2356 3 * rowA 8 0 3 + yW_2356 4 * rowA 8 0 4 + yW_2356 5 * rowA 8 0 5 + yW_2356 6 * rowA 8 0 6 + yW_2356 7 * rowA 8 0 7 + yW_2356 8 * rowA 8 0 8 ≤ db_2356 8 0 := by
  have hleft : yW_2356 0 * rowA 8 0 0 + yW_2356 1 * rowA 8 0 1 + yW_2356 2 * rowA 8 0 2 + yW_2356 3 * rowA 8 0 3 + yW_2356 4 * rowA 8 0 4 + yW_2356 5 * rowA 8 0 5 + yW_2356 6 * rowA 8 0 6 + yW_2356 7 * rowA 8 0 7 + yW_2356 8 * rowA 8 0 8 = (-11 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 8 0 = (-11 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_8_1 :
    yW_2356 0 * rowA 8 1 0 + yW_2356 1 * rowA 8 1 1 + yW_2356 2 * rowA 8 1 2 + yW_2356 3 * rowA 8 1 3 + yW_2356 4 * rowA 8 1 4 + yW_2356 5 * rowA 8 1 5 + yW_2356 6 * rowA 8 1 6 + yW_2356 7 * rowA 8 1 7 + yW_2356 8 * rowA 8 1 8 ≤ db_2356 8 1 := by
  have hleft : yW_2356 0 * rowA 8 1 0 + yW_2356 1 * rowA 8 1 1 + yW_2356 2 * rowA 8 1 2 + yW_2356 3 * rowA 8 1 3 + yW_2356 4 * rowA 8 1 4 + yW_2356 5 * rowA 8 1 5 + yW_2356 6 * rowA 8 1 6 + yW_2356 7 * rowA 8 1 7 + yW_2356 8 * rowA 8 1 8 = (-11 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 8 1 = (-5 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_8_2 :
    yW_2356 0 * rowA 8 2 0 + yW_2356 1 * rowA 8 2 1 + yW_2356 2 * rowA 8 2 2 + yW_2356 3 * rowA 8 2 3 + yW_2356 4 * rowA 8 2 4 + yW_2356 5 * rowA 8 2 5 + yW_2356 6 * rowA 8 2 6 + yW_2356 7 * rowA 8 2 7 + yW_2356 8 * rowA 8 2 8 ≤ db_2356 8 2 := by
  have hleft : yW_2356 0 * rowA 8 2 0 + yW_2356 1 * rowA 8 2 1 + yW_2356 2 * rowA 8 2 2 + yW_2356 3 * rowA 8 2 3 + yW_2356 4 * rowA 8 2 4 + yW_2356 5 * rowA 8 2 5 + yW_2356 6 * rowA 8 2 6 + yW_2356 7 * rowA 8 2 7 + yW_2356 8 * rowA 8 2 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 8 2 = (-5 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_8_3 :
    yW_2356 0 * rowA 8 3 0 + yW_2356 1 * rowA 8 3 1 + yW_2356 2 * rowA 8 3 2 + yW_2356 3 * rowA 8 3 3 + yW_2356 4 * rowA 8 3 4 + yW_2356 5 * rowA 8 3 5 + yW_2356 6 * rowA 8 3 6 + yW_2356 7 * rowA 8 3 7 + yW_2356 8 * rowA 8 3 8 ≤ db_2356 8 3 := by
  have hleft : yW_2356 0 * rowA 8 3 0 + yW_2356 1 * rowA 8 3 1 + yW_2356 2 * rowA 8 3 2 + yW_2356 3 * rowA 8 3 3 + yW_2356 4 * rowA 8 3 4 + yW_2356 5 * rowA 8 3 5 + yW_2356 6 * rowA 8 3 6 + yW_2356 7 * rowA 8 3 7 + yW_2356 8 * rowA 8 3 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 8 3 = (-5 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_8_4 :
    yW_2356 0 * rowA 8 4 0 + yW_2356 1 * rowA 8 4 1 + yW_2356 2 * rowA 8 4 2 + yW_2356 3 * rowA 8 4 3 + yW_2356 4 * rowA 8 4 4 + yW_2356 5 * rowA 8 4 5 + yW_2356 6 * rowA 8 4 6 + yW_2356 7 * rowA 8 4 7 + yW_2356 8 * rowA 8 4 8 ≤ db_2356 8 4 := by
  have hleft : yW_2356 0 * rowA 8 4 0 + yW_2356 1 * rowA 8 4 1 + yW_2356 2 * rowA 8 4 2 + yW_2356 3 * rowA 8 4 3 + yW_2356 4 * rowA 8 4 4 + yW_2356 5 * rowA 8 4 5 + yW_2356 6 * rowA 8 4 6 + yW_2356 7 * rowA 8 4 7 + yW_2356 8 * rowA 8 4 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 8 4 = (-3 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_8_5 :
    yW_2356 0 * rowA 8 5 0 + yW_2356 1 * rowA 8 5 1 + yW_2356 2 * rowA 8 5 2 + yW_2356 3 * rowA 8 5 3 + yW_2356 4 * rowA 8 5 4 + yW_2356 5 * rowA 8 5 5 + yW_2356 6 * rowA 8 5 6 + yW_2356 7 * rowA 8 5 7 + yW_2356 8 * rowA 8 5 8 ≤ db_2356 8 5 := by
  have hleft : yW_2356 0 * rowA 8 5 0 + yW_2356 1 * rowA 8 5 1 + yW_2356 2 * rowA 8 5 2 + yW_2356 3 * rowA 8 5 3 + yW_2356 4 * rowA 8 5 4 + yW_2356 5 * rowA 8 5 5 + yW_2356 6 * rowA 8 5 6 + yW_2356 7 * rowA 8 5 7 + yW_2356 8 * rowA 8 5 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 8 5 = (-3 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_8_6 :
    yW_2356 0 * rowA 8 6 0 + yW_2356 1 * rowA 8 6 1 + yW_2356 2 * rowA 8 6 2 + yW_2356 3 * rowA 8 6 3 + yW_2356 4 * rowA 8 6 4 + yW_2356 5 * rowA 8 6 5 + yW_2356 6 * rowA 8 6 6 + yW_2356 7 * rowA 8 6 7 + yW_2356 8 * rowA 8 6 8 ≤ db_2356 8 6 := by
  have hleft : yW_2356 0 * rowA 8 6 0 + yW_2356 1 * rowA 8 6 1 + yW_2356 2 * rowA 8 6 2 + yW_2356 3 * rowA 8 6 3 + yW_2356 4 * rowA 8 6 4 + yW_2356 5 * rowA 8 6 5 + yW_2356 6 * rowA 8 6 6 + yW_2356 7 * rowA 8 6 7 + yW_2356 8 * rowA 8 6 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 8 6 = (-1 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_8_7 :
    yW_2356 0 * rowA 8 7 0 + yW_2356 1 * rowA 8 7 1 + yW_2356 2 * rowA 8 7 2 + yW_2356 3 * rowA 8 7 3 + yW_2356 4 * rowA 8 7 4 + yW_2356 5 * rowA 8 7 5 + yW_2356 6 * rowA 8 7 6 + yW_2356 7 * rowA 8 7 7 + yW_2356 8 * rowA 8 7 8 ≤ db_2356 8 7 := by
  have hleft : yW_2356 0 * rowA 8 7 0 + yW_2356 1 * rowA 8 7 1 + yW_2356 2 * rowA 8 7 2 + yW_2356 3 * rowA 8 7 3 + yW_2356 4 * rowA 8 7 4 + yW_2356 5 * rowA 8 7 5 + yW_2356 6 * rowA 8 7 6 + yW_2356 7 * rowA 8 7 7 + yW_2356 8 * rowA 8 7 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 8 7 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_8_8 :
    yW_2356 0 * rowA 8 8 0 + yW_2356 1 * rowA 8 8 1 + yW_2356 2 * rowA 8 8 2 + yW_2356 3 * rowA 8 8 3 + yW_2356 4 * rowA 8 8 4 + yW_2356 5 * rowA 8 8 5 + yW_2356 6 * rowA 8 8 6 + yW_2356 7 * rowA 8 8 7 + yW_2356 8 * rowA 8 8 8 ≤ db_2356 8 8 := by
  have hleft : yW_2356 0 * rowA 8 8 0 + yW_2356 1 * rowA 8 8 1 + yW_2356 2 * rowA 8 8 2 + yW_2356 3 * rowA 8 8 3 + yW_2356 4 * rowA 8 8 4 + yW_2356 5 * rowA 8 8 5 + yW_2356 6 * rowA 8 8 6 + yW_2356 7 * rowA 8 8 7 + yW_2356 8 * rowA 8 8 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 8 8 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_8_9 :
    yW_2356 0 * rowA 8 9 0 + yW_2356 1 * rowA 8 9 1 + yW_2356 2 * rowA 8 9 2 + yW_2356 3 * rowA 8 9 3 + yW_2356 4 * rowA 8 9 4 + yW_2356 5 * rowA 8 9 5 + yW_2356 6 * rowA 8 9 6 + yW_2356 7 * rowA 8 9 7 + yW_2356 8 * rowA 8 9 8 ≤ db_2356 8 9 := by
  have hleft : yW_2356 0 * rowA 8 9 0 + yW_2356 1 * rowA 8 9 1 + yW_2356 2 * rowA 8 9 2 + yW_2356 3 * rowA 8 9 3 + yW_2356 4 * rowA 8 9 4 + yW_2356 5 * rowA 8 9 5 + yW_2356 6 * rowA 8 9 6 + yW_2356 7 * rowA 8 9 7 + yW_2356 8 * rowA 8 9 8 = (5 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 8 9 = (5 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_9_0 :
    yW_2356 0 * rowA 9 0 0 + yW_2356 1 * rowA 9 0 1 + yW_2356 2 * rowA 9 0 2 + yW_2356 3 * rowA 9 0 3 + yW_2356 4 * rowA 9 0 4 + yW_2356 5 * rowA 9 0 5 + yW_2356 6 * rowA 9 0 6 + yW_2356 7 * rowA 9 0 7 + yW_2356 8 * rowA 9 0 8 ≤ db_2356 9 0 := by
  have hleft : yW_2356 0 * rowA 9 0 0 + yW_2356 1 * rowA 9 0 1 + yW_2356 2 * rowA 9 0 2 + yW_2356 3 * rowA 9 0 3 + yW_2356 4 * rowA 9 0 4 + yW_2356 5 * rowA 9 0 5 + yW_2356 6 * rowA 9 0 6 + yW_2356 7 * rowA 9 0 7 + yW_2356 8 * rowA 9 0 8 = (-1 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 9 0 = (-1 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_9_1 :
    yW_2356 0 * rowA 9 1 0 + yW_2356 1 * rowA 9 1 1 + yW_2356 2 * rowA 9 1 2 + yW_2356 3 * rowA 9 1 3 + yW_2356 4 * rowA 9 1 4 + yW_2356 5 * rowA 9 1 5 + yW_2356 6 * rowA 9 1 6 + yW_2356 7 * rowA 9 1 7 + yW_2356 8 * rowA 9 1 8 ≤ db_2356 9 1 := by
  have hleft : yW_2356 0 * rowA 9 1 0 + yW_2356 1 * rowA 9 1 1 + yW_2356 2 * rowA 9 1 2 + yW_2356 3 * rowA 9 1 3 + yW_2356 4 * rowA 9 1 4 + yW_2356 5 * rowA 9 1 5 + yW_2356 6 * rowA 9 1 6 + yW_2356 7 * rowA 9 1 7 + yW_2356 8 * rowA 9 1 8 = (-1 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 9 1 = (-7 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_9_2 :
    yW_2356 0 * rowA 9 2 0 + yW_2356 1 * rowA 9 2 1 + yW_2356 2 * rowA 9 2 2 + yW_2356 3 * rowA 9 2 3 + yW_2356 4 * rowA 9 2 4 + yW_2356 5 * rowA 9 2 5 + yW_2356 6 * rowA 9 2 6 + yW_2356 7 * rowA 9 2 7 + yW_2356 8 * rowA 9 2 8 ≤ db_2356 9 2 := by
  have hleft : yW_2356 0 * rowA 9 2 0 + yW_2356 1 * rowA 9 2 1 + yW_2356 2 * rowA 9 2 2 + yW_2356 3 * rowA 9 2 3 + yW_2356 4 * rowA 9 2 4 + yW_2356 5 * rowA 9 2 5 + yW_2356 6 * rowA 9 2 6 + yW_2356 7 * rowA 9 2 7 + yW_2356 8 * rowA 9 2 8 = (-15 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 9 2 = (-7 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_9_3 :
    yW_2356 0 * rowA 9 3 0 + yW_2356 1 * rowA 9 3 1 + yW_2356 2 * rowA 9 3 2 + yW_2356 3 * rowA 9 3 3 + yW_2356 4 * rowA 9 3 4 + yW_2356 5 * rowA 9 3 5 + yW_2356 6 * rowA 9 3 6 + yW_2356 7 * rowA 9 3 7 + yW_2356 8 * rowA 9 3 8 ≤ db_2356 9 3 := by
  have hleft : yW_2356 0 * rowA 9 3 0 + yW_2356 1 * rowA 9 3 1 + yW_2356 2 * rowA 9 3 2 + yW_2356 3 * rowA 9 3 3 + yW_2356 4 * rowA 9 3 4 + yW_2356 5 * rowA 9 3 5 + yW_2356 6 * rowA 9 3 6 + yW_2356 7 * rowA 9 3 7 + yW_2356 8 * rowA 9 3 8 = (-15 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 9 3 = (-7 : ℚ) / 8 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_9_4 :
    yW_2356 0 * rowA 9 4 0 + yW_2356 1 * rowA 9 4 1 + yW_2356 2 * rowA 9 4 2 + yW_2356 3 * rowA 9 4 3 + yW_2356 4 * rowA 9 4 4 + yW_2356 5 * rowA 9 4 5 + yW_2356 6 * rowA 9 4 6 + yW_2356 7 * rowA 9 4 7 + yW_2356 8 * rowA 9 4 8 ≤ db_2356 9 4 := by
  have hleft : yW_2356 0 * rowA 9 4 0 + yW_2356 1 * rowA 9 4 1 + yW_2356 2 * rowA 9 4 2 + yW_2356 3 * rowA 9 4 3 + yW_2356 4 * rowA 9 4 4 + yW_2356 5 * rowA 9 4 5 + yW_2356 6 * rowA 9 4 6 + yW_2356 7 * rowA 9 4 7 + yW_2356 8 * rowA 9 4 8 = (-11 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 9 4 = (-11 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_9_5 :
    yW_2356 0 * rowA 9 5 0 + yW_2356 1 * rowA 9 5 1 + yW_2356 2 * rowA 9 5 2 + yW_2356 3 * rowA 9 5 3 + yW_2356 4 * rowA 9 5 4 + yW_2356 5 * rowA 9 5 5 + yW_2356 6 * rowA 9 5 6 + yW_2356 7 * rowA 9 5 7 + yW_2356 8 * rowA 9 5 8 ≤ db_2356 9 5 := by
  have hleft : yW_2356 0 * rowA 9 5 0 + yW_2356 1 * rowA 9 5 1 + yW_2356 2 * rowA 9 5 2 + yW_2356 3 * rowA 9 5 3 + yW_2356 4 * rowA 9 5 4 + yW_2356 5 * rowA 9 5 5 + yW_2356 6 * rowA 9 5 6 + yW_2356 7 * rowA 9 5 7 + yW_2356 8 * rowA 9 5 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 9 5 = (-1 : ℚ) / 2 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_9_6 :
    yW_2356 0 * rowA 9 6 0 + yW_2356 1 * rowA 9 6 1 + yW_2356 2 * rowA 9 6 2 + yW_2356 3 * rowA 9 6 3 + yW_2356 4 * rowA 9 6 4 + yW_2356 5 * rowA 9 6 5 + yW_2356 6 * rowA 9 6 6 + yW_2356 7 * rowA 9 6 7 + yW_2356 8 * rowA 9 6 8 ≤ db_2356 9 6 := by
  have hleft : yW_2356 0 * rowA 9 6 0 + yW_2356 1 * rowA 9 6 1 + yW_2356 2 * rowA 9 6 2 + yW_2356 3 * rowA 9 6 3 + yW_2356 4 * rowA 9 6 4 + yW_2356 5 * rowA 9 6 5 + yW_2356 6 * rowA 9 6 6 + yW_2356 7 * rowA 9 6 7 + yW_2356 8 * rowA 9 6 8 = (-7 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 9 6 = (-7 : ℚ) / 16 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_9_7 :
    yW_2356 0 * rowA 9 7 0 + yW_2356 1 * rowA 9 7 1 + yW_2356 2 * rowA 9 7 2 + yW_2356 3 * rowA 9 7 3 + yW_2356 4 * rowA 9 7 4 + yW_2356 5 * rowA 9 7 5 + yW_2356 6 * rowA 9 7 6 + yW_2356 7 * rowA 9 7 7 + yW_2356 8 * rowA 9 7 8 ≤ db_2356 9 7 := by
  have hleft : yW_2356 0 * rowA 9 7 0 + yW_2356 1 * rowA 9 7 1 + yW_2356 2 * rowA 9 7 2 + yW_2356 3 * rowA 9 7 3 + yW_2356 4 * rowA 9 7 4 + yW_2356 5 * rowA 9 7 5 + yW_2356 6 * rowA 9 7 6 + yW_2356 7 * rowA 9 7 7 + yW_2356 8 * rowA 9 7 8 = (-7 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 9 7 = (-1 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_9_8 :
    yW_2356 0 * rowA 9 8 0 + yW_2356 1 * rowA 9 8 1 + yW_2356 2 * rowA 9 8 2 + yW_2356 3 * rowA 9 8 3 + yW_2356 4 * rowA 9 8 4 + yW_2356 5 * rowA 9 8 5 + yW_2356 6 * rowA 9 8 6 + yW_2356 7 * rowA 9 8 7 + yW_2356 8 * rowA 9 8 8 ≤ db_2356 9 8 := by
  have hleft : yW_2356 0 * rowA 9 8 0 + yW_2356 1 * rowA 9 8 1 + yW_2356 2 * rowA 9 8 2 + yW_2356 3 * rowA 9 8 3 + yW_2356 4 * rowA 9 8 4 + yW_2356 5 * rowA 9 8 5 + yW_2356 6 * rowA 9 8 6 + yW_2356 7 * rowA 9 8 7 + yW_2356 8 * rowA 9 8 8 = (-5 : ℚ) / 16 := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 9 8 = (-1 : ℚ) / 4 := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_9_9 :
    yW_2356 0 * rowA 9 9 0 + yW_2356 1 * rowA 9 9 1 + yW_2356 2 * rowA 9 9 2 + yW_2356 3 * rowA 9 9 3 + yW_2356 4 * rowA 9 9 4 + yW_2356 5 * rowA 9 9 5 + yW_2356 6 * rowA 9 9 6 + yW_2356 7 * rowA 9 9 7 + yW_2356 8 * rowA 9 9 8 ≤ db_2356 9 9 := by
  have hleft : yW_2356 0 * rowA 9 9 0 + yW_2356 1 * rowA 9 9 1 + yW_2356 2 * rowA 9 9 2 + yW_2356 3 * rowA 9 9 3 + yW_2356 4 * rowA 9 9 4 + yW_2356 5 * rowA 9 9 5 + yW_2356 6 * rowA 9 9 6 + yW_2356 7 * rowA 9 9 7 + yW_2356 8 * rowA 9 9 8 = (0 : ℚ) := by
    norm_num [yW_2356, rowA]
  have hright : db_2356 9 9 = (0 : ℚ) := by
    norm_num [db_2356, dbmVal_2356]
  rw [hleft, hright]
  norm_num

theorem row_cap_2356_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 0 j q) ≤ db_2356 0 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_0_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_0_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_0_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_0_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_0_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_0_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_0_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_0_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_0_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_0_9

theorem row_cap_2356_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 1 j q) ≤ db_2356 1 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_1_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_1_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_1_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_1_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_1_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_1_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_1_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_1_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_1_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_1_9

theorem row_cap_2356_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 2 j q) ≤ db_2356 2 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_2_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_2_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_2_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_2_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_2_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_2_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_2_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_2_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_2_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_2_9

theorem row_cap_2356_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 3 j q) ≤ db_2356 3 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_3_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_3_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_3_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_3_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_3_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_3_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_3_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_3_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_3_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_3_9

theorem row_cap_2356_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 4 j q) ≤ db_2356 4 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_4_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_4_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_4_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_4_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_4_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_4_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_4_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_4_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_4_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_4_9

theorem row_cap_2356_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 5 j q) ≤ db_2356 5 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_5_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_5_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_5_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_5_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_5_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_5_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_5_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_5_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_5_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_5_9

theorem row_cap_2356_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 6 j q) ≤ db_2356 6 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_6_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_6_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_6_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_6_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_6_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_6_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_6_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_6_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_6_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_6_9

theorem row_cap_2356_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 7 j q) ≤ db_2356 7 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_7_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_7_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_7_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_7_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_7_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_7_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_7_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_7_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_7_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_7_9

theorem row_cap_2356_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 8 j q) ≤ db_2356 8 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_8_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_8_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_8_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_8_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_8_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_8_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_8_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_8_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_8_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_8_9

theorem row_cap_2356_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 9 j q) ≤ db_2356 9 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_9_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_9_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_9_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_9_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_9_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_9_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_9_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_9_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_9_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2356_9_9

theorem row_cap_2356 (i j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA i j q) ≤ db_2356 i j := by
  fin_cases i
  · exact row_cap_2356_0 j
  · exact row_cap_2356_1 j
  · exact row_cap_2356_2 j
  · exact row_cap_2356_3 j
  · exact row_cap_2356_4 j
  · exact row_cap_2356_5 j
  · exact row_cap_2356_6 j
  · exact row_cap_2356_7 j
  · exact row_cap_2356_8 j
  · exact row_cap_2356_9 j

def dbmVal_2360 : Fin 10 → Fin 10 → ℤ
  | i, j => ![
      ![0, 512, 512, 512, 1536, 2048, 3072, 3072, 3072, 4096],
      ![0, 0, 512, 512, 1536, 2048, 3072, 3072, 3072, 4096],
      ![0, 0, 0, 512, 1536, 2048, 3072, 3072, 3072, 4096],
      ![-256, 0, 0, 0, 1280, 1792, 2560, 2560, 2816, 3840],
      ![-1280, -768, -768, -768, 0, 768, 1792, 1792, 1792, 2816],
      ![-1792, -1536, -1536, -1536, -512, 0, 1024, 1024, 1024, 2304],
      ![-1792, -1536, -1536, -1536, -512, 0, 0, 1024, 1024, 2304],
      ![-2304, -2048, -2048, -2048, -1024, -256, 0, 0, 768, 1792],
      ![-2816, -2560, -2560, -2560, -1536, -768, 0, 0, 0, 1280],
      ![-4096, -3584, -3584, -3584, -2560, -2048, -1024, -1024, -1024, 0]
    ] i j

def db_2360 (i j : Fin 10) : ℚ := (dbmVal_2360 i j : ℚ) / 4096

theorem row_cap_2360_0_0 :
    yW_2360 0 * rowA 0 0 0 + yW_2360 1 * rowA 0 0 1 + yW_2360 2 * rowA 0 0 2 + yW_2360 3 * rowA 0 0 3 + yW_2360 4 * rowA 0 0 4 + yW_2360 5 * rowA 0 0 5 + yW_2360 6 * rowA 0 0 6 + yW_2360 7 * rowA 0 0 7 + yW_2360 8 * rowA 0 0 8 ≤ db_2360 0 0 := by
  have hleft : yW_2360 0 * rowA 0 0 0 + yW_2360 1 * rowA 0 0 1 + yW_2360 2 * rowA 0 0 2 + yW_2360 3 * rowA 0 0 3 + yW_2360 4 * rowA 0 0 4 + yW_2360 5 * rowA 0 0 5 + yW_2360 6 * rowA 0 0 6 + yW_2360 7 * rowA 0 0 7 + yW_2360 8 * rowA 0 0 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 0 0 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_0_1 :
    yW_2360 0 * rowA 0 1 0 + yW_2360 1 * rowA 0 1 1 + yW_2360 2 * rowA 0 1 2 + yW_2360 3 * rowA 0 1 3 + yW_2360 4 * rowA 0 1 4 + yW_2360 5 * rowA 0 1 5 + yW_2360 6 * rowA 0 1 6 + yW_2360 7 * rowA 0 1 7 + yW_2360 8 * rowA 0 1 8 ≤ db_2360 0 1 := by
  have hleft : yW_2360 0 * rowA 0 1 0 + yW_2360 1 * rowA 0 1 1 + yW_2360 2 * rowA 0 1 2 + yW_2360 3 * rowA 0 1 3 + yW_2360 4 * rowA 0 1 4 + yW_2360 5 * rowA 0 1 5 + yW_2360 6 * rowA 0 1 6 + yW_2360 7 * rowA 0 1 7 + yW_2360 8 * rowA 0 1 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 0 1 = (1 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_0_2 :
    yW_2360 0 * rowA 0 2 0 + yW_2360 1 * rowA 0 2 1 + yW_2360 2 * rowA 0 2 2 + yW_2360 3 * rowA 0 2 3 + yW_2360 4 * rowA 0 2 4 + yW_2360 5 * rowA 0 2 5 + yW_2360 6 * rowA 0 2 6 + yW_2360 7 * rowA 0 2 7 + yW_2360 8 * rowA 0 2 8 ≤ db_2360 0 2 := by
  have hleft : yW_2360 0 * rowA 0 2 0 + yW_2360 1 * rowA 0 2 1 + yW_2360 2 * rowA 0 2 2 + yW_2360 3 * rowA 0 2 3 + yW_2360 4 * rowA 0 2 4 + yW_2360 5 * rowA 0 2 5 + yW_2360 6 * rowA 0 2 6 + yW_2360 7 * rowA 0 2 7 + yW_2360 8 * rowA 0 2 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 0 2 = (1 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_0_3 :
    yW_2360 0 * rowA 0 3 0 + yW_2360 1 * rowA 0 3 1 + yW_2360 2 * rowA 0 3 2 + yW_2360 3 * rowA 0 3 3 + yW_2360 4 * rowA 0 3 4 + yW_2360 5 * rowA 0 3 5 + yW_2360 6 * rowA 0 3 6 + yW_2360 7 * rowA 0 3 7 + yW_2360 8 * rowA 0 3 8 ≤ db_2360 0 3 := by
  have hleft : yW_2360 0 * rowA 0 3 0 + yW_2360 1 * rowA 0 3 1 + yW_2360 2 * rowA 0 3 2 + yW_2360 3 * rowA 0 3 3 + yW_2360 4 * rowA 0 3 4 + yW_2360 5 * rowA 0 3 5 + yW_2360 6 * rowA 0 3 6 + yW_2360 7 * rowA 0 3 7 + yW_2360 8 * rowA 0 3 8 = (1 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 0 3 = (1 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_0_4 :
    yW_2360 0 * rowA 0 4 0 + yW_2360 1 * rowA 0 4 1 + yW_2360 2 * rowA 0 4 2 + yW_2360 3 * rowA 0 4 3 + yW_2360 4 * rowA 0 4 4 + yW_2360 5 * rowA 0 4 5 + yW_2360 6 * rowA 0 4 6 + yW_2360 7 * rowA 0 4 7 + yW_2360 8 * rowA 0 4 8 ≤ db_2360 0 4 := by
  have hleft : yW_2360 0 * rowA 0 4 0 + yW_2360 1 * rowA 0 4 1 + yW_2360 2 * rowA 0 4 2 + yW_2360 3 * rowA 0 4 3 + yW_2360 4 * rowA 0 4 4 + yW_2360 5 * rowA 0 4 5 + yW_2360 6 * rowA 0 4 6 + yW_2360 7 * rowA 0 4 7 + yW_2360 8 * rowA 0 4 8 = (5 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 0 4 = (3 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_0_5 :
    yW_2360 0 * rowA 0 5 0 + yW_2360 1 * rowA 0 5 1 + yW_2360 2 * rowA 0 5 2 + yW_2360 3 * rowA 0 5 3 + yW_2360 4 * rowA 0 5 4 + yW_2360 5 * rowA 0 5 5 + yW_2360 6 * rowA 0 5 6 + yW_2360 7 * rowA 0 5 7 + yW_2360 8 * rowA 0 5 8 ≤ db_2360 0 5 := by
  have hleft : yW_2360 0 * rowA 0 5 0 + yW_2360 1 * rowA 0 5 1 + yW_2360 2 * rowA 0 5 2 + yW_2360 3 * rowA 0 5 3 + yW_2360 4 * rowA 0 5 4 + yW_2360 5 * rowA 0 5 5 + yW_2360 6 * rowA 0 5 6 + yW_2360 7 * rowA 0 5 7 + yW_2360 8 * rowA 0 5 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 0 5 = (1 : ℚ) / 2 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_0_6 :
    yW_2360 0 * rowA 0 6 0 + yW_2360 1 * rowA 0 6 1 + yW_2360 2 * rowA 0 6 2 + yW_2360 3 * rowA 0 6 3 + yW_2360 4 * rowA 0 6 4 + yW_2360 5 * rowA 0 6 5 + yW_2360 6 * rowA 0 6 6 + yW_2360 7 * rowA 0 6 7 + yW_2360 8 * rowA 0 6 8 ≤ db_2360 0 6 := by
  have hleft : yW_2360 0 * rowA 0 6 0 + yW_2360 1 * rowA 0 6 1 + yW_2360 2 * rowA 0 6 2 + yW_2360 3 * rowA 0 6 3 + yW_2360 4 * rowA 0 6 4 + yW_2360 5 * rowA 0 6 5 + yW_2360 6 * rowA 0 6 6 + yW_2360 7 * rowA 0 6 7 + yW_2360 8 * rowA 0 6 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 0 6 = (3 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_0_7 :
    yW_2360 0 * rowA 0 7 0 + yW_2360 1 * rowA 0 7 1 + yW_2360 2 * rowA 0 7 2 + yW_2360 3 * rowA 0 7 3 + yW_2360 4 * rowA 0 7 4 + yW_2360 5 * rowA 0 7 5 + yW_2360 6 * rowA 0 7 6 + yW_2360 7 * rowA 0 7 7 + yW_2360 8 * rowA 0 7 8 ≤ db_2360 0 7 := by
  have hleft : yW_2360 0 * rowA 0 7 0 + yW_2360 1 * rowA 0 7 1 + yW_2360 2 * rowA 0 7 2 + yW_2360 3 * rowA 0 7 3 + yW_2360 4 * rowA 0 7 4 + yW_2360 5 * rowA 0 7 5 + yW_2360 6 * rowA 0 7 6 + yW_2360 7 * rowA 0 7 7 + yW_2360 8 * rowA 0 7 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 0 7 = (3 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_0_8 :
    yW_2360 0 * rowA 0 8 0 + yW_2360 1 * rowA 0 8 1 + yW_2360 2 * rowA 0 8 2 + yW_2360 3 * rowA 0 8 3 + yW_2360 4 * rowA 0 8 4 + yW_2360 5 * rowA 0 8 5 + yW_2360 6 * rowA 0 8 6 + yW_2360 7 * rowA 0 8 7 + yW_2360 8 * rowA 0 8 8 ≤ db_2360 0 8 := by
  have hleft : yW_2360 0 * rowA 0 8 0 + yW_2360 1 * rowA 0 8 1 + yW_2360 2 * rowA 0 8 2 + yW_2360 3 * rowA 0 8 3 + yW_2360 4 * rowA 0 8 4 + yW_2360 5 * rowA 0 8 5 + yW_2360 6 * rowA 0 8 6 + yW_2360 7 * rowA 0 8 7 + yW_2360 8 * rowA 0 8 8 = (3 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 0 8 = (3 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_0_9 :
    yW_2360 0 * rowA 0 9 0 + yW_2360 1 * rowA 0 9 1 + yW_2360 2 * rowA 0 9 2 + yW_2360 3 * rowA 0 9 3 + yW_2360 4 * rowA 0 9 4 + yW_2360 5 * rowA 0 9 5 + yW_2360 6 * rowA 0 9 6 + yW_2360 7 * rowA 0 9 7 + yW_2360 8 * rowA 0 9 8 ≤ db_2360 0 9 := by
  have hleft : yW_2360 0 * rowA 0 9 0 + yW_2360 1 * rowA 0 9 1 + yW_2360 2 * rowA 0 9 2 + yW_2360 3 * rowA 0 9 3 + yW_2360 4 * rowA 0 9 4 + yW_2360 5 * rowA 0 9 5 + yW_2360 6 * rowA 0 9 6 + yW_2360 7 * rowA 0 9 7 + yW_2360 8 * rowA 0 9 8 = (1 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 0 9 = (1 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_1_0 :
    yW_2360 0 * rowA 1 0 0 + yW_2360 1 * rowA 1 0 1 + yW_2360 2 * rowA 1 0 2 + yW_2360 3 * rowA 1 0 3 + yW_2360 4 * rowA 1 0 4 + yW_2360 5 * rowA 1 0 5 + yW_2360 6 * rowA 1 0 6 + yW_2360 7 * rowA 1 0 7 + yW_2360 8 * rowA 1 0 8 ≤ db_2360 1 0 := by
  have hleft : yW_2360 0 * rowA 1 0 0 + yW_2360 1 * rowA 1 0 1 + yW_2360 2 * rowA 1 0 2 + yW_2360 3 * rowA 1 0 3 + yW_2360 4 * rowA 1 0 4 + yW_2360 5 * rowA 1 0 5 + yW_2360 6 * rowA 1 0 6 + yW_2360 7 * rowA 1 0 7 + yW_2360 8 * rowA 1 0 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 1 0 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_1_1 :
    yW_2360 0 * rowA 1 1 0 + yW_2360 1 * rowA 1 1 1 + yW_2360 2 * rowA 1 1 2 + yW_2360 3 * rowA 1 1 3 + yW_2360 4 * rowA 1 1 4 + yW_2360 5 * rowA 1 1 5 + yW_2360 6 * rowA 1 1 6 + yW_2360 7 * rowA 1 1 7 + yW_2360 8 * rowA 1 1 8 ≤ db_2360 1 1 := by
  have hleft : yW_2360 0 * rowA 1 1 0 + yW_2360 1 * rowA 1 1 1 + yW_2360 2 * rowA 1 1 2 + yW_2360 3 * rowA 1 1 3 + yW_2360 4 * rowA 1 1 4 + yW_2360 5 * rowA 1 1 5 + yW_2360 6 * rowA 1 1 6 + yW_2360 7 * rowA 1 1 7 + yW_2360 8 * rowA 1 1 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 1 1 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_1_2 :
    yW_2360 0 * rowA 1 2 0 + yW_2360 1 * rowA 1 2 1 + yW_2360 2 * rowA 1 2 2 + yW_2360 3 * rowA 1 2 3 + yW_2360 4 * rowA 1 2 4 + yW_2360 5 * rowA 1 2 5 + yW_2360 6 * rowA 1 2 6 + yW_2360 7 * rowA 1 2 7 + yW_2360 8 * rowA 1 2 8 ≤ db_2360 1 2 := by
  have hleft : yW_2360 0 * rowA 1 2 0 + yW_2360 1 * rowA 1 2 1 + yW_2360 2 * rowA 1 2 2 + yW_2360 3 * rowA 1 2 3 + yW_2360 4 * rowA 1 2 4 + yW_2360 5 * rowA 1 2 5 + yW_2360 6 * rowA 1 2 6 + yW_2360 7 * rowA 1 2 7 + yW_2360 8 * rowA 1 2 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 1 2 = (1 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_1_3 :
    yW_2360 0 * rowA 1 3 0 + yW_2360 1 * rowA 1 3 1 + yW_2360 2 * rowA 1 3 2 + yW_2360 3 * rowA 1 3 3 + yW_2360 4 * rowA 1 3 4 + yW_2360 5 * rowA 1 3 5 + yW_2360 6 * rowA 1 3 6 + yW_2360 7 * rowA 1 3 7 + yW_2360 8 * rowA 1 3 8 ≤ db_2360 1 3 := by
  have hleft : yW_2360 0 * rowA 1 3 0 + yW_2360 1 * rowA 1 3 1 + yW_2360 2 * rowA 1 3 2 + yW_2360 3 * rowA 1 3 3 + yW_2360 4 * rowA 1 3 4 + yW_2360 5 * rowA 1 3 5 + yW_2360 6 * rowA 1 3 6 + yW_2360 7 * rowA 1 3 7 + yW_2360 8 * rowA 1 3 8 = (1 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 1 3 = (1 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_1_4 :
    yW_2360 0 * rowA 1 4 0 + yW_2360 1 * rowA 1 4 1 + yW_2360 2 * rowA 1 4 2 + yW_2360 3 * rowA 1 4 3 + yW_2360 4 * rowA 1 4 4 + yW_2360 5 * rowA 1 4 5 + yW_2360 6 * rowA 1 4 6 + yW_2360 7 * rowA 1 4 7 + yW_2360 8 * rowA 1 4 8 ≤ db_2360 1 4 := by
  have hleft : yW_2360 0 * rowA 1 4 0 + yW_2360 1 * rowA 1 4 1 + yW_2360 2 * rowA 1 4 2 + yW_2360 3 * rowA 1 4 3 + yW_2360 4 * rowA 1 4 4 + yW_2360 5 * rowA 1 4 5 + yW_2360 6 * rowA 1 4 6 + yW_2360 7 * rowA 1 4 7 + yW_2360 8 * rowA 1 4 8 = (5 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 1 4 = (3 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_1_5 :
    yW_2360 0 * rowA 1 5 0 + yW_2360 1 * rowA 1 5 1 + yW_2360 2 * rowA 1 5 2 + yW_2360 3 * rowA 1 5 3 + yW_2360 4 * rowA 1 5 4 + yW_2360 5 * rowA 1 5 5 + yW_2360 6 * rowA 1 5 6 + yW_2360 7 * rowA 1 5 7 + yW_2360 8 * rowA 1 5 8 ≤ db_2360 1 5 := by
  have hleft : yW_2360 0 * rowA 1 5 0 + yW_2360 1 * rowA 1 5 1 + yW_2360 2 * rowA 1 5 2 + yW_2360 3 * rowA 1 5 3 + yW_2360 4 * rowA 1 5 4 + yW_2360 5 * rowA 1 5 5 + yW_2360 6 * rowA 1 5 6 + yW_2360 7 * rowA 1 5 7 + yW_2360 8 * rowA 1 5 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 1 5 = (1 : ℚ) / 2 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_1_6 :
    yW_2360 0 * rowA 1 6 0 + yW_2360 1 * rowA 1 6 1 + yW_2360 2 * rowA 1 6 2 + yW_2360 3 * rowA 1 6 3 + yW_2360 4 * rowA 1 6 4 + yW_2360 5 * rowA 1 6 5 + yW_2360 6 * rowA 1 6 6 + yW_2360 7 * rowA 1 6 7 + yW_2360 8 * rowA 1 6 8 ≤ db_2360 1 6 := by
  have hleft : yW_2360 0 * rowA 1 6 0 + yW_2360 1 * rowA 1 6 1 + yW_2360 2 * rowA 1 6 2 + yW_2360 3 * rowA 1 6 3 + yW_2360 4 * rowA 1 6 4 + yW_2360 5 * rowA 1 6 5 + yW_2360 6 * rowA 1 6 6 + yW_2360 7 * rowA 1 6 7 + yW_2360 8 * rowA 1 6 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 1 6 = (3 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_1_7 :
    yW_2360 0 * rowA 1 7 0 + yW_2360 1 * rowA 1 7 1 + yW_2360 2 * rowA 1 7 2 + yW_2360 3 * rowA 1 7 3 + yW_2360 4 * rowA 1 7 4 + yW_2360 5 * rowA 1 7 5 + yW_2360 6 * rowA 1 7 6 + yW_2360 7 * rowA 1 7 7 + yW_2360 8 * rowA 1 7 8 ≤ db_2360 1 7 := by
  have hleft : yW_2360 0 * rowA 1 7 0 + yW_2360 1 * rowA 1 7 1 + yW_2360 2 * rowA 1 7 2 + yW_2360 3 * rowA 1 7 3 + yW_2360 4 * rowA 1 7 4 + yW_2360 5 * rowA 1 7 5 + yW_2360 6 * rowA 1 7 6 + yW_2360 7 * rowA 1 7 7 + yW_2360 8 * rowA 1 7 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 1 7 = (3 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_1_8 :
    yW_2360 0 * rowA 1 8 0 + yW_2360 1 * rowA 1 8 1 + yW_2360 2 * rowA 1 8 2 + yW_2360 3 * rowA 1 8 3 + yW_2360 4 * rowA 1 8 4 + yW_2360 5 * rowA 1 8 5 + yW_2360 6 * rowA 1 8 6 + yW_2360 7 * rowA 1 8 7 + yW_2360 8 * rowA 1 8 8 ≤ db_2360 1 8 := by
  have hleft : yW_2360 0 * rowA 1 8 0 + yW_2360 1 * rowA 1 8 1 + yW_2360 2 * rowA 1 8 2 + yW_2360 3 * rowA 1 8 3 + yW_2360 4 * rowA 1 8 4 + yW_2360 5 * rowA 1 8 5 + yW_2360 6 * rowA 1 8 6 + yW_2360 7 * rowA 1 8 7 + yW_2360 8 * rowA 1 8 8 = (3 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 1 8 = (3 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_1_9 :
    yW_2360 0 * rowA 1 9 0 + yW_2360 1 * rowA 1 9 1 + yW_2360 2 * rowA 1 9 2 + yW_2360 3 * rowA 1 9 3 + yW_2360 4 * rowA 1 9 4 + yW_2360 5 * rowA 1 9 5 + yW_2360 6 * rowA 1 9 6 + yW_2360 7 * rowA 1 9 7 + yW_2360 8 * rowA 1 9 8 ≤ db_2360 1 9 := by
  have hleft : yW_2360 0 * rowA 1 9 0 + yW_2360 1 * rowA 1 9 1 + yW_2360 2 * rowA 1 9 2 + yW_2360 3 * rowA 1 9 3 + yW_2360 4 * rowA 1 9 4 + yW_2360 5 * rowA 1 9 5 + yW_2360 6 * rowA 1 9 6 + yW_2360 7 * rowA 1 9 7 + yW_2360 8 * rowA 1 9 8 = (1 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 1 9 = (1 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_2_0 :
    yW_2360 0 * rowA 2 0 0 + yW_2360 1 * rowA 2 0 1 + yW_2360 2 * rowA 2 0 2 + yW_2360 3 * rowA 2 0 3 + yW_2360 4 * rowA 2 0 4 + yW_2360 5 * rowA 2 0 5 + yW_2360 6 * rowA 2 0 6 + yW_2360 7 * rowA 2 0 7 + yW_2360 8 * rowA 2 0 8 ≤ db_2360 2 0 := by
  have hleft : yW_2360 0 * rowA 2 0 0 + yW_2360 1 * rowA 2 0 1 + yW_2360 2 * rowA 2 0 2 + yW_2360 3 * rowA 2 0 3 + yW_2360 4 * rowA 2 0 4 + yW_2360 5 * rowA 2 0 5 + yW_2360 6 * rowA 2 0 6 + yW_2360 7 * rowA 2 0 7 + yW_2360 8 * rowA 2 0 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 2 0 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_2_1 :
    yW_2360 0 * rowA 2 1 0 + yW_2360 1 * rowA 2 1 1 + yW_2360 2 * rowA 2 1 2 + yW_2360 3 * rowA 2 1 3 + yW_2360 4 * rowA 2 1 4 + yW_2360 5 * rowA 2 1 5 + yW_2360 6 * rowA 2 1 6 + yW_2360 7 * rowA 2 1 7 + yW_2360 8 * rowA 2 1 8 ≤ db_2360 2 1 := by
  have hleft : yW_2360 0 * rowA 2 1 0 + yW_2360 1 * rowA 2 1 1 + yW_2360 2 * rowA 2 1 2 + yW_2360 3 * rowA 2 1 3 + yW_2360 4 * rowA 2 1 4 + yW_2360 5 * rowA 2 1 5 + yW_2360 6 * rowA 2 1 6 + yW_2360 7 * rowA 2 1 7 + yW_2360 8 * rowA 2 1 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 2 1 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_2_2 :
    yW_2360 0 * rowA 2 2 0 + yW_2360 1 * rowA 2 2 1 + yW_2360 2 * rowA 2 2 2 + yW_2360 3 * rowA 2 2 3 + yW_2360 4 * rowA 2 2 4 + yW_2360 5 * rowA 2 2 5 + yW_2360 6 * rowA 2 2 6 + yW_2360 7 * rowA 2 2 7 + yW_2360 8 * rowA 2 2 8 ≤ db_2360 2 2 := by
  have hleft : yW_2360 0 * rowA 2 2 0 + yW_2360 1 * rowA 2 2 1 + yW_2360 2 * rowA 2 2 2 + yW_2360 3 * rowA 2 2 3 + yW_2360 4 * rowA 2 2 4 + yW_2360 5 * rowA 2 2 5 + yW_2360 6 * rowA 2 2 6 + yW_2360 7 * rowA 2 2 7 + yW_2360 8 * rowA 2 2 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 2 2 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_2_3 :
    yW_2360 0 * rowA 2 3 0 + yW_2360 1 * rowA 2 3 1 + yW_2360 2 * rowA 2 3 2 + yW_2360 3 * rowA 2 3 3 + yW_2360 4 * rowA 2 3 4 + yW_2360 5 * rowA 2 3 5 + yW_2360 6 * rowA 2 3 6 + yW_2360 7 * rowA 2 3 7 + yW_2360 8 * rowA 2 3 8 ≤ db_2360 2 3 := by
  have hleft : yW_2360 0 * rowA 2 3 0 + yW_2360 1 * rowA 2 3 1 + yW_2360 2 * rowA 2 3 2 + yW_2360 3 * rowA 2 3 3 + yW_2360 4 * rowA 2 3 4 + yW_2360 5 * rowA 2 3 5 + yW_2360 6 * rowA 2 3 6 + yW_2360 7 * rowA 2 3 7 + yW_2360 8 * rowA 2 3 8 = (1 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 2 3 = (1 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_2_4 :
    yW_2360 0 * rowA 2 4 0 + yW_2360 1 * rowA 2 4 1 + yW_2360 2 * rowA 2 4 2 + yW_2360 3 * rowA 2 4 3 + yW_2360 4 * rowA 2 4 4 + yW_2360 5 * rowA 2 4 5 + yW_2360 6 * rowA 2 4 6 + yW_2360 7 * rowA 2 4 7 + yW_2360 8 * rowA 2 4 8 ≤ db_2360 2 4 := by
  have hleft : yW_2360 0 * rowA 2 4 0 + yW_2360 1 * rowA 2 4 1 + yW_2360 2 * rowA 2 4 2 + yW_2360 3 * rowA 2 4 3 + yW_2360 4 * rowA 2 4 4 + yW_2360 5 * rowA 2 4 5 + yW_2360 6 * rowA 2 4 6 + yW_2360 7 * rowA 2 4 7 + yW_2360 8 * rowA 2 4 8 = (5 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 2 4 = (3 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_2_5 :
    yW_2360 0 * rowA 2 5 0 + yW_2360 1 * rowA 2 5 1 + yW_2360 2 * rowA 2 5 2 + yW_2360 3 * rowA 2 5 3 + yW_2360 4 * rowA 2 5 4 + yW_2360 5 * rowA 2 5 5 + yW_2360 6 * rowA 2 5 6 + yW_2360 7 * rowA 2 5 7 + yW_2360 8 * rowA 2 5 8 ≤ db_2360 2 5 := by
  have hleft : yW_2360 0 * rowA 2 5 0 + yW_2360 1 * rowA 2 5 1 + yW_2360 2 * rowA 2 5 2 + yW_2360 3 * rowA 2 5 3 + yW_2360 4 * rowA 2 5 4 + yW_2360 5 * rowA 2 5 5 + yW_2360 6 * rowA 2 5 6 + yW_2360 7 * rowA 2 5 7 + yW_2360 8 * rowA 2 5 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 2 5 = (1 : ℚ) / 2 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_2_6 :
    yW_2360 0 * rowA 2 6 0 + yW_2360 1 * rowA 2 6 1 + yW_2360 2 * rowA 2 6 2 + yW_2360 3 * rowA 2 6 3 + yW_2360 4 * rowA 2 6 4 + yW_2360 5 * rowA 2 6 5 + yW_2360 6 * rowA 2 6 6 + yW_2360 7 * rowA 2 6 7 + yW_2360 8 * rowA 2 6 8 ≤ db_2360 2 6 := by
  have hleft : yW_2360 0 * rowA 2 6 0 + yW_2360 1 * rowA 2 6 1 + yW_2360 2 * rowA 2 6 2 + yW_2360 3 * rowA 2 6 3 + yW_2360 4 * rowA 2 6 4 + yW_2360 5 * rowA 2 6 5 + yW_2360 6 * rowA 2 6 6 + yW_2360 7 * rowA 2 6 7 + yW_2360 8 * rowA 2 6 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 2 6 = (3 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_2_7 :
    yW_2360 0 * rowA 2 7 0 + yW_2360 1 * rowA 2 7 1 + yW_2360 2 * rowA 2 7 2 + yW_2360 3 * rowA 2 7 3 + yW_2360 4 * rowA 2 7 4 + yW_2360 5 * rowA 2 7 5 + yW_2360 6 * rowA 2 7 6 + yW_2360 7 * rowA 2 7 7 + yW_2360 8 * rowA 2 7 8 ≤ db_2360 2 7 := by
  have hleft : yW_2360 0 * rowA 2 7 0 + yW_2360 1 * rowA 2 7 1 + yW_2360 2 * rowA 2 7 2 + yW_2360 3 * rowA 2 7 3 + yW_2360 4 * rowA 2 7 4 + yW_2360 5 * rowA 2 7 5 + yW_2360 6 * rowA 2 7 6 + yW_2360 7 * rowA 2 7 7 + yW_2360 8 * rowA 2 7 8 = (9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 2 7 = (3 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_2_8 :
    yW_2360 0 * rowA 2 8 0 + yW_2360 1 * rowA 2 8 1 + yW_2360 2 * rowA 2 8 2 + yW_2360 3 * rowA 2 8 3 + yW_2360 4 * rowA 2 8 4 + yW_2360 5 * rowA 2 8 5 + yW_2360 6 * rowA 2 8 6 + yW_2360 7 * rowA 2 8 7 + yW_2360 8 * rowA 2 8 8 ≤ db_2360 2 8 := by
  have hleft : yW_2360 0 * rowA 2 8 0 + yW_2360 1 * rowA 2 8 1 + yW_2360 2 * rowA 2 8 2 + yW_2360 3 * rowA 2 8 3 + yW_2360 4 * rowA 2 8 4 + yW_2360 5 * rowA 2 8 5 + yW_2360 6 * rowA 2 8 6 + yW_2360 7 * rowA 2 8 7 + yW_2360 8 * rowA 2 8 8 = (3 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 2 8 = (3 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_2_9 :
    yW_2360 0 * rowA 2 9 0 + yW_2360 1 * rowA 2 9 1 + yW_2360 2 * rowA 2 9 2 + yW_2360 3 * rowA 2 9 3 + yW_2360 4 * rowA 2 9 4 + yW_2360 5 * rowA 2 9 5 + yW_2360 6 * rowA 2 9 6 + yW_2360 7 * rowA 2 9 7 + yW_2360 8 * rowA 2 9 8 ≤ db_2360 2 9 := by
  have hleft : yW_2360 0 * rowA 2 9 0 + yW_2360 1 * rowA 2 9 1 + yW_2360 2 * rowA 2 9 2 + yW_2360 3 * rowA 2 9 3 + yW_2360 4 * rowA 2 9 4 + yW_2360 5 * rowA 2 9 5 + yW_2360 6 * rowA 2 9 6 + yW_2360 7 * rowA 2 9 7 + yW_2360 8 * rowA 2 9 8 = (1 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 2 9 = (1 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_3_0 :
    yW_2360 0 * rowA 3 0 0 + yW_2360 1 * rowA 3 0 1 + yW_2360 2 * rowA 3 0 2 + yW_2360 3 * rowA 3 0 3 + yW_2360 4 * rowA 3 0 4 + yW_2360 5 * rowA 3 0 5 + yW_2360 6 * rowA 3 0 6 + yW_2360 7 * rowA 3 0 7 + yW_2360 8 * rowA 3 0 8 ≤ db_2360 3 0 := by
  have hleft : yW_2360 0 * rowA 3 0 0 + yW_2360 1 * rowA 3 0 1 + yW_2360 2 * rowA 3 0 2 + yW_2360 3 * rowA 3 0 3 + yW_2360 4 * rowA 3 0 4 + yW_2360 5 * rowA 3 0 5 + yW_2360 6 * rowA 3 0 6 + yW_2360 7 * rowA 3 0 7 + yW_2360 8 * rowA 3 0 8 = (-1 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 3 0 = (-1 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_3_1 :
    yW_2360 0 * rowA 3 1 0 + yW_2360 1 * rowA 3 1 1 + yW_2360 2 * rowA 3 1 2 + yW_2360 3 * rowA 3 1 3 + yW_2360 4 * rowA 3 1 4 + yW_2360 5 * rowA 3 1 5 + yW_2360 6 * rowA 3 1 6 + yW_2360 7 * rowA 3 1 7 + yW_2360 8 * rowA 3 1 8 ≤ db_2360 3 1 := by
  have hleft : yW_2360 0 * rowA 3 1 0 + yW_2360 1 * rowA 3 1 1 + yW_2360 2 * rowA 3 1 2 + yW_2360 3 * rowA 3 1 3 + yW_2360 4 * rowA 3 1 4 + yW_2360 5 * rowA 3 1 5 + yW_2360 6 * rowA 3 1 6 + yW_2360 7 * rowA 3 1 7 + yW_2360 8 * rowA 3 1 8 = (-1 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 3 1 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_3_2 :
    yW_2360 0 * rowA 3 2 0 + yW_2360 1 * rowA 3 2 1 + yW_2360 2 * rowA 3 2 2 + yW_2360 3 * rowA 3 2 3 + yW_2360 4 * rowA 3 2 4 + yW_2360 5 * rowA 3 2 5 + yW_2360 6 * rowA 3 2 6 + yW_2360 7 * rowA 3 2 7 + yW_2360 8 * rowA 3 2 8 ≤ db_2360 3 2 := by
  have hleft : yW_2360 0 * rowA 3 2 0 + yW_2360 1 * rowA 3 2 1 + yW_2360 2 * rowA 3 2 2 + yW_2360 3 * rowA 3 2 3 + yW_2360 4 * rowA 3 2 4 + yW_2360 5 * rowA 3 2 5 + yW_2360 6 * rowA 3 2 6 + yW_2360 7 * rowA 3 2 7 + yW_2360 8 * rowA 3 2 8 = (-1 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 3 2 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_3_3 :
    yW_2360 0 * rowA 3 3 0 + yW_2360 1 * rowA 3 3 1 + yW_2360 2 * rowA 3 3 2 + yW_2360 3 * rowA 3 3 3 + yW_2360 4 * rowA 3 3 4 + yW_2360 5 * rowA 3 3 5 + yW_2360 6 * rowA 3 3 6 + yW_2360 7 * rowA 3 3 7 + yW_2360 8 * rowA 3 3 8 ≤ db_2360 3 3 := by
  have hleft : yW_2360 0 * rowA 3 3 0 + yW_2360 1 * rowA 3 3 1 + yW_2360 2 * rowA 3 3 2 + yW_2360 3 * rowA 3 3 3 + yW_2360 4 * rowA 3 3 4 + yW_2360 5 * rowA 3 3 5 + yW_2360 6 * rowA 3 3 6 + yW_2360 7 * rowA 3 3 7 + yW_2360 8 * rowA 3 3 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 3 3 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_3_4 :
    yW_2360 0 * rowA 3 4 0 + yW_2360 1 * rowA 3 4 1 + yW_2360 2 * rowA 3 4 2 + yW_2360 3 * rowA 3 4 3 + yW_2360 4 * rowA 3 4 4 + yW_2360 5 * rowA 3 4 5 + yW_2360 6 * rowA 3 4 6 + yW_2360 7 * rowA 3 4 7 + yW_2360 8 * rowA 3 4 8 ≤ db_2360 3 4 := by
  have hleft : yW_2360 0 * rowA 3 4 0 + yW_2360 1 * rowA 3 4 1 + yW_2360 2 * rowA 3 4 2 + yW_2360 3 * rowA 3 4 3 + yW_2360 4 * rowA 3 4 4 + yW_2360 5 * rowA 3 4 5 + yW_2360 6 * rowA 3 4 6 + yW_2360 7 * rowA 3 4 7 + yW_2360 8 * rowA 3 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 3 4 = (5 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_3_5 :
    yW_2360 0 * rowA 3 5 0 + yW_2360 1 * rowA 3 5 1 + yW_2360 2 * rowA 3 5 2 + yW_2360 3 * rowA 3 5 3 + yW_2360 4 * rowA 3 5 4 + yW_2360 5 * rowA 3 5 5 + yW_2360 6 * rowA 3 5 6 + yW_2360 7 * rowA 3 5 7 + yW_2360 8 * rowA 3 5 8 ≤ db_2360 3 5 := by
  have hleft : yW_2360 0 * rowA 3 5 0 + yW_2360 1 * rowA 3 5 1 + yW_2360 2 * rowA 3 5 2 + yW_2360 3 * rowA 3 5 3 + yW_2360 4 * rowA 3 5 4 + yW_2360 5 * rowA 3 5 5 + yW_2360 6 * rowA 3 5 6 + yW_2360 7 * rowA 3 5 7 + yW_2360 8 * rowA 3 5 8 = (7 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 3 5 = (7 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_3_6 :
    yW_2360 0 * rowA 3 6 0 + yW_2360 1 * rowA 3 6 1 + yW_2360 2 * rowA 3 6 2 + yW_2360 3 * rowA 3 6 3 + yW_2360 4 * rowA 3 6 4 + yW_2360 5 * rowA 3 6 5 + yW_2360 6 * rowA 3 6 6 + yW_2360 7 * rowA 3 6 7 + yW_2360 8 * rowA 3 6 8 ≤ db_2360 3 6 := by
  have hleft : yW_2360 0 * rowA 3 6 0 + yW_2360 1 * rowA 3 6 1 + yW_2360 2 * rowA 3 6 2 + yW_2360 3 * rowA 3 6 3 + yW_2360 4 * rowA 3 6 4 + yW_2360 5 * rowA 3 6 5 + yW_2360 6 * rowA 3 6 6 + yW_2360 7 * rowA 3 6 7 + yW_2360 8 * rowA 3 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 3 6 = (5 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_3_7 :
    yW_2360 0 * rowA 3 7 0 + yW_2360 1 * rowA 3 7 1 + yW_2360 2 * rowA 3 7 2 + yW_2360 3 * rowA 3 7 3 + yW_2360 4 * rowA 3 7 4 + yW_2360 5 * rowA 3 7 5 + yW_2360 6 * rowA 3 7 6 + yW_2360 7 * rowA 3 7 7 + yW_2360 8 * rowA 3 7 8 ≤ db_2360 3 7 := by
  have hleft : yW_2360 0 * rowA 3 7 0 + yW_2360 1 * rowA 3 7 1 + yW_2360 2 * rowA 3 7 2 + yW_2360 3 * rowA 3 7 3 + yW_2360 4 * rowA 3 7 4 + yW_2360 5 * rowA 3 7 5 + yW_2360 6 * rowA 3 7 6 + yW_2360 7 * rowA 3 7 7 + yW_2360 8 * rowA 3 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 3 7 = (5 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_3_8 :
    yW_2360 0 * rowA 3 8 0 + yW_2360 1 * rowA 3 8 1 + yW_2360 2 * rowA 3 8 2 + yW_2360 3 * rowA 3 8 3 + yW_2360 4 * rowA 3 8 4 + yW_2360 5 * rowA 3 8 5 + yW_2360 6 * rowA 3 8 6 + yW_2360 7 * rowA 3 8 7 + yW_2360 8 * rowA 3 8 8 ≤ db_2360 3 8 := by
  have hleft : yW_2360 0 * rowA 3 8 0 + yW_2360 1 * rowA 3 8 1 + yW_2360 2 * rowA 3 8 2 + yW_2360 3 * rowA 3 8 3 + yW_2360 4 * rowA 3 8 4 + yW_2360 5 * rowA 3 8 5 + yW_2360 6 * rowA 3 8 6 + yW_2360 7 * rowA 3 8 7 + yW_2360 8 * rowA 3 8 8 = (11 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 3 8 = (11 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_3_9 :
    yW_2360 0 * rowA 3 9 0 + yW_2360 1 * rowA 3 9 1 + yW_2360 2 * rowA 3 9 2 + yW_2360 3 * rowA 3 9 3 + yW_2360 4 * rowA 3 9 4 + yW_2360 5 * rowA 3 9 5 + yW_2360 6 * rowA 3 9 6 + yW_2360 7 * rowA 3 9 7 + yW_2360 8 * rowA 3 9 8 ≤ db_2360 3 9 := by
  have hleft : yW_2360 0 * rowA 3 9 0 + yW_2360 1 * rowA 3 9 1 + yW_2360 2 * rowA 3 9 2 + yW_2360 3 * rowA 3 9 3 + yW_2360 4 * rowA 3 9 4 + yW_2360 5 * rowA 3 9 5 + yW_2360 6 * rowA 3 9 6 + yW_2360 7 * rowA 3 9 7 + yW_2360 8 * rowA 3 9 8 = (15 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 3 9 = (15 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_4_0 :
    yW_2360 0 * rowA 4 0 0 + yW_2360 1 * rowA 4 0 1 + yW_2360 2 * rowA 4 0 2 + yW_2360 3 * rowA 4 0 3 + yW_2360 4 * rowA 4 0 4 + yW_2360 5 * rowA 4 0 5 + yW_2360 6 * rowA 4 0 6 + yW_2360 7 * rowA 4 0 7 + yW_2360 8 * rowA 4 0 8 ≤ db_2360 4 0 := by
  have hleft : yW_2360 0 * rowA 4 0 0 + yW_2360 1 * rowA 4 0 1 + yW_2360 2 * rowA 4 0 2 + yW_2360 3 * rowA 4 0 3 + yW_2360 4 * rowA 4 0 4 + yW_2360 5 * rowA 4 0 5 + yW_2360 6 * rowA 4 0 6 + yW_2360 7 * rowA 4 0 7 + yW_2360 8 * rowA 4 0 8 = (-5 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 4 0 = (-5 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_4_1 :
    yW_2360 0 * rowA 4 1 0 + yW_2360 1 * rowA 4 1 1 + yW_2360 2 * rowA 4 1 2 + yW_2360 3 * rowA 4 1 3 + yW_2360 4 * rowA 4 1 4 + yW_2360 5 * rowA 4 1 5 + yW_2360 6 * rowA 4 1 6 + yW_2360 7 * rowA 4 1 7 + yW_2360 8 * rowA 4 1 8 ≤ db_2360 4 1 := by
  have hleft : yW_2360 0 * rowA 4 1 0 + yW_2360 1 * rowA 4 1 1 + yW_2360 2 * rowA 4 1 2 + yW_2360 3 * rowA 4 1 3 + yW_2360 4 * rowA 4 1 4 + yW_2360 5 * rowA 4 1 5 + yW_2360 6 * rowA 4 1 6 + yW_2360 7 * rowA 4 1 7 + yW_2360 8 * rowA 4 1 8 = (-5 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 4 1 = (-3 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_4_2 :
    yW_2360 0 * rowA 4 2 0 + yW_2360 1 * rowA 4 2 1 + yW_2360 2 * rowA 4 2 2 + yW_2360 3 * rowA 4 2 3 + yW_2360 4 * rowA 4 2 4 + yW_2360 5 * rowA 4 2 5 + yW_2360 6 * rowA 4 2 6 + yW_2360 7 * rowA 4 2 7 + yW_2360 8 * rowA 4 2 8 ≤ db_2360 4 2 := by
  have hleft : yW_2360 0 * rowA 4 2 0 + yW_2360 1 * rowA 4 2 1 + yW_2360 2 * rowA 4 2 2 + yW_2360 3 * rowA 4 2 3 + yW_2360 4 * rowA 4 2 4 + yW_2360 5 * rowA 4 2 5 + yW_2360 6 * rowA 4 2 6 + yW_2360 7 * rowA 4 2 7 + yW_2360 8 * rowA 4 2 8 = (-5 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 4 2 = (-3 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_4_3 :
    yW_2360 0 * rowA 4 3 0 + yW_2360 1 * rowA 4 3 1 + yW_2360 2 * rowA 4 3 2 + yW_2360 3 * rowA 4 3 3 + yW_2360 4 * rowA 4 3 4 + yW_2360 5 * rowA 4 3 5 + yW_2360 6 * rowA 4 3 6 + yW_2360 7 * rowA 4 3 7 + yW_2360 8 * rowA 4 3 8 ≤ db_2360 4 3 := by
  have hleft : yW_2360 0 * rowA 4 3 0 + yW_2360 1 * rowA 4 3 1 + yW_2360 2 * rowA 4 3 2 + yW_2360 3 * rowA 4 3 3 + yW_2360 4 * rowA 4 3 4 + yW_2360 5 * rowA 4 3 5 + yW_2360 6 * rowA 4 3 6 + yW_2360 7 * rowA 4 3 7 + yW_2360 8 * rowA 4 3 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 4 3 = (-3 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_4_4 :
    yW_2360 0 * rowA 4 4 0 + yW_2360 1 * rowA 4 4 1 + yW_2360 2 * rowA 4 4 2 + yW_2360 3 * rowA 4 4 3 + yW_2360 4 * rowA 4 4 4 + yW_2360 5 * rowA 4 4 5 + yW_2360 6 * rowA 4 4 6 + yW_2360 7 * rowA 4 4 7 + yW_2360 8 * rowA 4 4 8 ≤ db_2360 4 4 := by
  have hleft : yW_2360 0 * rowA 4 4 0 + yW_2360 1 * rowA 4 4 1 + yW_2360 2 * rowA 4 4 2 + yW_2360 3 * rowA 4 4 3 + yW_2360 4 * rowA 4 4 4 + yW_2360 5 * rowA 4 4 5 + yW_2360 6 * rowA 4 4 6 + yW_2360 7 * rowA 4 4 7 + yW_2360 8 * rowA 4 4 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 4 4 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_4_5 :
    yW_2360 0 * rowA 4 5 0 + yW_2360 1 * rowA 4 5 1 + yW_2360 2 * rowA 4 5 2 + yW_2360 3 * rowA 4 5 3 + yW_2360 4 * rowA 4 5 4 + yW_2360 5 * rowA 4 5 5 + yW_2360 6 * rowA 4 5 6 + yW_2360 7 * rowA 4 5 7 + yW_2360 8 * rowA 4 5 8 ≤ db_2360 4 5 := by
  have hleft : yW_2360 0 * rowA 4 5 0 + yW_2360 1 * rowA 4 5 1 + yW_2360 2 * rowA 4 5 2 + yW_2360 3 * rowA 4 5 3 + yW_2360 4 * rowA 4 5 4 + yW_2360 5 * rowA 4 5 5 + yW_2360 6 * rowA 4 5 6 + yW_2360 7 * rowA 4 5 7 + yW_2360 8 * rowA 4 5 8 = (3 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 4 5 = (3 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_4_6 :
    yW_2360 0 * rowA 4 6 0 + yW_2360 1 * rowA 4 6 1 + yW_2360 2 * rowA 4 6 2 + yW_2360 3 * rowA 4 6 3 + yW_2360 4 * rowA 4 6 4 + yW_2360 5 * rowA 4 6 5 + yW_2360 6 * rowA 4 6 6 + yW_2360 7 * rowA 4 6 7 + yW_2360 8 * rowA 4 6 8 ≤ db_2360 4 6 := by
  have hleft : yW_2360 0 * rowA 4 6 0 + yW_2360 1 * rowA 4 6 1 + yW_2360 2 * rowA 4 6 2 + yW_2360 3 * rowA 4 6 3 + yW_2360 4 * rowA 4 6 4 + yW_2360 5 * rowA 4 6 5 + yW_2360 6 * rowA 4 6 6 + yW_2360 7 * rowA 4 6 7 + yW_2360 8 * rowA 4 6 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 4 6 = (7 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_4_7 :
    yW_2360 0 * rowA 4 7 0 + yW_2360 1 * rowA 4 7 1 + yW_2360 2 * rowA 4 7 2 + yW_2360 3 * rowA 4 7 3 + yW_2360 4 * rowA 4 7 4 + yW_2360 5 * rowA 4 7 5 + yW_2360 6 * rowA 4 7 6 + yW_2360 7 * rowA 4 7 7 + yW_2360 8 * rowA 4 7 8 ≤ db_2360 4 7 := by
  have hleft : yW_2360 0 * rowA 4 7 0 + yW_2360 1 * rowA 4 7 1 + yW_2360 2 * rowA 4 7 2 + yW_2360 3 * rowA 4 7 3 + yW_2360 4 * rowA 4 7 4 + yW_2360 5 * rowA 4 7 5 + yW_2360 6 * rowA 4 7 6 + yW_2360 7 * rowA 4 7 7 + yW_2360 8 * rowA 4 7 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 4 7 = (7 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_4_8 :
    yW_2360 0 * rowA 4 8 0 + yW_2360 1 * rowA 4 8 1 + yW_2360 2 * rowA 4 8 2 + yW_2360 3 * rowA 4 8 3 + yW_2360 4 * rowA 4 8 4 + yW_2360 5 * rowA 4 8 5 + yW_2360 6 * rowA 4 8 6 + yW_2360 7 * rowA 4 8 7 + yW_2360 8 * rowA 4 8 8 ≤ db_2360 4 8 := by
  have hleft : yW_2360 0 * rowA 4 8 0 + yW_2360 1 * rowA 4 8 1 + yW_2360 2 * rowA 4 8 2 + yW_2360 3 * rowA 4 8 3 + yW_2360 4 * rowA 4 8 4 + yW_2360 5 * rowA 4 8 5 + yW_2360 6 * rowA 4 8 6 + yW_2360 7 * rowA 4 8 7 + yW_2360 8 * rowA 4 8 8 = (7 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 4 8 = (7 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_4_9 :
    yW_2360 0 * rowA 4 9 0 + yW_2360 1 * rowA 4 9 1 + yW_2360 2 * rowA 4 9 2 + yW_2360 3 * rowA 4 9 3 + yW_2360 4 * rowA 4 9 4 + yW_2360 5 * rowA 4 9 5 + yW_2360 6 * rowA 4 9 6 + yW_2360 7 * rowA 4 9 7 + yW_2360 8 * rowA 4 9 8 ≤ db_2360 4 9 := by
  have hleft : yW_2360 0 * rowA 4 9 0 + yW_2360 1 * rowA 4 9 1 + yW_2360 2 * rowA 4 9 2 + yW_2360 3 * rowA 4 9 3 + yW_2360 4 * rowA 4 9 4 + yW_2360 5 * rowA 4 9 5 + yW_2360 6 * rowA 4 9 6 + yW_2360 7 * rowA 4 9 7 + yW_2360 8 * rowA 4 9 8 = (11 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 4 9 = (11 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_5_0 :
    yW_2360 0 * rowA 5 0 0 + yW_2360 1 * rowA 5 0 1 + yW_2360 2 * rowA 5 0 2 + yW_2360 3 * rowA 5 0 3 + yW_2360 4 * rowA 5 0 4 + yW_2360 5 * rowA 5 0 5 + yW_2360 6 * rowA 5 0 6 + yW_2360 7 * rowA 5 0 7 + yW_2360 8 * rowA 5 0 8 ≤ db_2360 5 0 := by
  have hleft : yW_2360 0 * rowA 5 0 0 + yW_2360 1 * rowA 5 0 1 + yW_2360 2 * rowA 5 0 2 + yW_2360 3 * rowA 5 0 3 + yW_2360 4 * rowA 5 0 4 + yW_2360 5 * rowA 5 0 5 + yW_2360 6 * rowA 5 0 6 + yW_2360 7 * rowA 5 0 7 + yW_2360 8 * rowA 5 0 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 5 0 = (-7 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_5_1 :
    yW_2360 0 * rowA 5 1 0 + yW_2360 1 * rowA 5 1 1 + yW_2360 2 * rowA 5 1 2 + yW_2360 3 * rowA 5 1 3 + yW_2360 4 * rowA 5 1 4 + yW_2360 5 * rowA 5 1 5 + yW_2360 6 * rowA 5 1 6 + yW_2360 7 * rowA 5 1 7 + yW_2360 8 * rowA 5 1 8 ≤ db_2360 5 1 := by
  have hleft : yW_2360 0 * rowA 5 1 0 + yW_2360 1 * rowA 5 1 1 + yW_2360 2 * rowA 5 1 2 + yW_2360 3 * rowA 5 1 3 + yW_2360 4 * rowA 5 1 4 + yW_2360 5 * rowA 5 1 5 + yW_2360 6 * rowA 5 1 6 + yW_2360 7 * rowA 5 1 7 + yW_2360 8 * rowA 5 1 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 5 1 = (-3 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_5_2 :
    yW_2360 0 * rowA 5 2 0 + yW_2360 1 * rowA 5 2 1 + yW_2360 2 * rowA 5 2 2 + yW_2360 3 * rowA 5 2 3 + yW_2360 4 * rowA 5 2 4 + yW_2360 5 * rowA 5 2 5 + yW_2360 6 * rowA 5 2 6 + yW_2360 7 * rowA 5 2 7 + yW_2360 8 * rowA 5 2 8 ≤ db_2360 5 2 := by
  have hleft : yW_2360 0 * rowA 5 2 0 + yW_2360 1 * rowA 5 2 1 + yW_2360 2 * rowA 5 2 2 + yW_2360 3 * rowA 5 2 3 + yW_2360 4 * rowA 5 2 4 + yW_2360 5 * rowA 5 2 5 + yW_2360 6 * rowA 5 2 6 + yW_2360 7 * rowA 5 2 7 + yW_2360 8 * rowA 5 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 5 2 = (-3 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_5_3 :
    yW_2360 0 * rowA 5 3 0 + yW_2360 1 * rowA 5 3 1 + yW_2360 2 * rowA 5 3 2 + yW_2360 3 * rowA 5 3 3 + yW_2360 4 * rowA 5 3 4 + yW_2360 5 * rowA 5 3 5 + yW_2360 6 * rowA 5 3 6 + yW_2360 7 * rowA 5 3 7 + yW_2360 8 * rowA 5 3 8 ≤ db_2360 5 3 := by
  have hleft : yW_2360 0 * rowA 5 3 0 + yW_2360 1 * rowA 5 3 1 + yW_2360 2 * rowA 5 3 2 + yW_2360 3 * rowA 5 3 3 + yW_2360 4 * rowA 5 3 4 + yW_2360 5 * rowA 5 3 5 + yW_2360 6 * rowA 5 3 6 + yW_2360 7 * rowA 5 3 7 + yW_2360 8 * rowA 5 3 8 = (-7 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 5 3 = (-3 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_5_4 :
    yW_2360 0 * rowA 5 4 0 + yW_2360 1 * rowA 5 4 1 + yW_2360 2 * rowA 5 4 2 + yW_2360 3 * rowA 5 4 3 + yW_2360 4 * rowA 5 4 4 + yW_2360 5 * rowA 5 4 5 + yW_2360 6 * rowA 5 4 6 + yW_2360 7 * rowA 5 4 7 + yW_2360 8 * rowA 5 4 8 ≤ db_2360 5 4 := by
  have hleft : yW_2360 0 * rowA 5 4 0 + yW_2360 1 * rowA 5 4 1 + yW_2360 2 * rowA 5 4 2 + yW_2360 3 * rowA 5 4 3 + yW_2360 4 * rowA 5 4 4 + yW_2360 5 * rowA 5 4 5 + yW_2360 6 * rowA 5 4 6 + yW_2360 7 * rowA 5 4 7 + yW_2360 8 * rowA 5 4 8 = (-3 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 5 4 = (-1 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_5_5 :
    yW_2360 0 * rowA 5 5 0 + yW_2360 1 * rowA 5 5 1 + yW_2360 2 * rowA 5 5 2 + yW_2360 3 * rowA 5 5 3 + yW_2360 4 * rowA 5 5 4 + yW_2360 5 * rowA 5 5 5 + yW_2360 6 * rowA 5 5 6 + yW_2360 7 * rowA 5 5 7 + yW_2360 8 * rowA 5 5 8 ≤ db_2360 5 5 := by
  have hleft : yW_2360 0 * rowA 5 5 0 + yW_2360 1 * rowA 5 5 1 + yW_2360 2 * rowA 5 5 2 + yW_2360 3 * rowA 5 5 3 + yW_2360 4 * rowA 5 5 4 + yW_2360 5 * rowA 5 5 5 + yW_2360 6 * rowA 5 5 6 + yW_2360 7 * rowA 5 5 7 + yW_2360 8 * rowA 5 5 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 5 5 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_5_6 :
    yW_2360 0 * rowA 5 6 0 + yW_2360 1 * rowA 5 6 1 + yW_2360 2 * rowA 5 6 2 + yW_2360 3 * rowA 5 6 3 + yW_2360 4 * rowA 5 6 4 + yW_2360 5 * rowA 5 6 5 + yW_2360 6 * rowA 5 6 6 + yW_2360 7 * rowA 5 6 7 + yW_2360 8 * rowA 5 6 8 ≤ db_2360 5 6 := by
  have hleft : yW_2360 0 * rowA 5 6 0 + yW_2360 1 * rowA 5 6 1 + yW_2360 2 * rowA 5 6 2 + yW_2360 3 * rowA 5 6 3 + yW_2360 4 * rowA 5 6 4 + yW_2360 5 * rowA 5 6 5 + yW_2360 6 * rowA 5 6 6 + yW_2360 7 * rowA 5 6 7 + yW_2360 8 * rowA 5 6 8 = (1 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 5 6 = (1 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_5_7 :
    yW_2360 0 * rowA 5 7 0 + yW_2360 1 * rowA 5 7 1 + yW_2360 2 * rowA 5 7 2 + yW_2360 3 * rowA 5 7 3 + yW_2360 4 * rowA 5 7 4 + yW_2360 5 * rowA 5 7 5 + yW_2360 6 * rowA 5 7 6 + yW_2360 7 * rowA 5 7 7 + yW_2360 8 * rowA 5 7 8 ≤ db_2360 5 7 := by
  have hleft : yW_2360 0 * rowA 5 7 0 + yW_2360 1 * rowA 5 7 1 + yW_2360 2 * rowA 5 7 2 + yW_2360 3 * rowA 5 7 3 + yW_2360 4 * rowA 5 7 4 + yW_2360 5 * rowA 5 7 5 + yW_2360 6 * rowA 5 7 6 + yW_2360 7 * rowA 5 7 7 + yW_2360 8 * rowA 5 7 8 = (1 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 5 7 = (1 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_5_8 :
    yW_2360 0 * rowA 5 8 0 + yW_2360 1 * rowA 5 8 1 + yW_2360 2 * rowA 5 8 2 + yW_2360 3 * rowA 5 8 3 + yW_2360 4 * rowA 5 8 4 + yW_2360 5 * rowA 5 8 5 + yW_2360 6 * rowA 5 8 6 + yW_2360 7 * rowA 5 8 7 + yW_2360 8 * rowA 5 8 8 ≤ db_2360 5 8 := by
  have hleft : yW_2360 0 * rowA 5 8 0 + yW_2360 1 * rowA 5 8 1 + yW_2360 2 * rowA 5 8 2 + yW_2360 3 * rowA 5 8 3 + yW_2360 4 * rowA 5 8 4 + yW_2360 5 * rowA 5 8 5 + yW_2360 6 * rowA 5 8 6 + yW_2360 7 * rowA 5 8 7 + yW_2360 8 * rowA 5 8 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 5 8 = (1 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_5_9 :
    yW_2360 0 * rowA 5 9 0 + yW_2360 1 * rowA 5 9 1 + yW_2360 2 * rowA 5 9 2 + yW_2360 3 * rowA 5 9 3 + yW_2360 4 * rowA 5 9 4 + yW_2360 5 * rowA 5 9 5 + yW_2360 6 * rowA 5 9 6 + yW_2360 7 * rowA 5 9 7 + yW_2360 8 * rowA 5 9 8 ≤ db_2360 5 9 := by
  have hleft : yW_2360 0 * rowA 5 9 0 + yW_2360 1 * rowA 5 9 1 + yW_2360 2 * rowA 5 9 2 + yW_2360 3 * rowA 5 9 3 + yW_2360 4 * rowA 5 9 4 + yW_2360 5 * rowA 5 9 5 + yW_2360 6 * rowA 5 9 6 + yW_2360 7 * rowA 5 9 7 + yW_2360 8 * rowA 5 9 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 5 9 = (9 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_6_0 :
    yW_2360 0 * rowA 6 0 0 + yW_2360 1 * rowA 6 0 1 + yW_2360 2 * rowA 6 0 2 + yW_2360 3 * rowA 6 0 3 + yW_2360 4 * rowA 6 0 4 + yW_2360 5 * rowA 6 0 5 + yW_2360 6 * rowA 6 0 6 + yW_2360 7 * rowA 6 0 7 + yW_2360 8 * rowA 6 0 8 ≤ db_2360 6 0 := by
  have hleft : yW_2360 0 * rowA 6 0 0 + yW_2360 1 * rowA 6 0 1 + yW_2360 2 * rowA 6 0 2 + yW_2360 3 * rowA 6 0 3 + yW_2360 4 * rowA 6 0 4 + yW_2360 5 * rowA 6 0 5 + yW_2360 6 * rowA 6 0 6 + yW_2360 7 * rowA 6 0 7 + yW_2360 8 * rowA 6 0 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 6 0 = (-7 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_6_1 :
    yW_2360 0 * rowA 6 1 0 + yW_2360 1 * rowA 6 1 1 + yW_2360 2 * rowA 6 1 2 + yW_2360 3 * rowA 6 1 3 + yW_2360 4 * rowA 6 1 4 + yW_2360 5 * rowA 6 1 5 + yW_2360 6 * rowA 6 1 6 + yW_2360 7 * rowA 6 1 7 + yW_2360 8 * rowA 6 1 8 ≤ db_2360 6 1 := by
  have hleft : yW_2360 0 * rowA 6 1 0 + yW_2360 1 * rowA 6 1 1 + yW_2360 2 * rowA 6 1 2 + yW_2360 3 * rowA 6 1 3 + yW_2360 4 * rowA 6 1 4 + yW_2360 5 * rowA 6 1 5 + yW_2360 6 * rowA 6 1 6 + yW_2360 7 * rowA 6 1 7 + yW_2360 8 * rowA 6 1 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 6 1 = (-3 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_6_2 :
    yW_2360 0 * rowA 6 2 0 + yW_2360 1 * rowA 6 2 1 + yW_2360 2 * rowA 6 2 2 + yW_2360 3 * rowA 6 2 3 + yW_2360 4 * rowA 6 2 4 + yW_2360 5 * rowA 6 2 5 + yW_2360 6 * rowA 6 2 6 + yW_2360 7 * rowA 6 2 7 + yW_2360 8 * rowA 6 2 8 ≤ db_2360 6 2 := by
  have hleft : yW_2360 0 * rowA 6 2 0 + yW_2360 1 * rowA 6 2 1 + yW_2360 2 * rowA 6 2 2 + yW_2360 3 * rowA 6 2 3 + yW_2360 4 * rowA 6 2 4 + yW_2360 5 * rowA 6 2 5 + yW_2360 6 * rowA 6 2 6 + yW_2360 7 * rowA 6 2 7 + yW_2360 8 * rowA 6 2 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 6 2 = (-3 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_6_3 :
    yW_2360 0 * rowA 6 3 0 + yW_2360 1 * rowA 6 3 1 + yW_2360 2 * rowA 6 3 2 + yW_2360 3 * rowA 6 3 3 + yW_2360 4 * rowA 6 3 4 + yW_2360 5 * rowA 6 3 5 + yW_2360 6 * rowA 6 3 6 + yW_2360 7 * rowA 6 3 7 + yW_2360 8 * rowA 6 3 8 ≤ db_2360 6 3 := by
  have hleft : yW_2360 0 * rowA 6 3 0 + yW_2360 1 * rowA 6 3 1 + yW_2360 2 * rowA 6 3 2 + yW_2360 3 * rowA 6 3 3 + yW_2360 4 * rowA 6 3 4 + yW_2360 5 * rowA 6 3 5 + yW_2360 6 * rowA 6 3 6 + yW_2360 7 * rowA 6 3 7 + yW_2360 8 * rowA 6 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 6 3 = (-3 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_6_4 :
    yW_2360 0 * rowA 6 4 0 + yW_2360 1 * rowA 6 4 1 + yW_2360 2 * rowA 6 4 2 + yW_2360 3 * rowA 6 4 3 + yW_2360 4 * rowA 6 4 4 + yW_2360 5 * rowA 6 4 5 + yW_2360 6 * rowA 6 4 6 + yW_2360 7 * rowA 6 4 7 + yW_2360 8 * rowA 6 4 8 ≤ db_2360 6 4 := by
  have hleft : yW_2360 0 * rowA 6 4 0 + yW_2360 1 * rowA 6 4 1 + yW_2360 2 * rowA 6 4 2 + yW_2360 3 * rowA 6 4 3 + yW_2360 4 * rowA 6 4 4 + yW_2360 5 * rowA 6 4 5 + yW_2360 6 * rowA 6 4 6 + yW_2360 7 * rowA 6 4 7 + yW_2360 8 * rowA 6 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 6 4 = (-1 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_6_5 :
    yW_2360 0 * rowA 6 5 0 + yW_2360 1 * rowA 6 5 1 + yW_2360 2 * rowA 6 5 2 + yW_2360 3 * rowA 6 5 3 + yW_2360 4 * rowA 6 5 4 + yW_2360 5 * rowA 6 5 5 + yW_2360 6 * rowA 6 5 6 + yW_2360 7 * rowA 6 5 7 + yW_2360 8 * rowA 6 5 8 ≤ db_2360 6 5 := by
  have hleft : yW_2360 0 * rowA 6 5 0 + yW_2360 1 * rowA 6 5 1 + yW_2360 2 * rowA 6 5 2 + yW_2360 3 * rowA 6 5 3 + yW_2360 4 * rowA 6 5 4 + yW_2360 5 * rowA 6 5 5 + yW_2360 6 * rowA 6 5 6 + yW_2360 7 * rowA 6 5 7 + yW_2360 8 * rowA 6 5 8 = (-1 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 6 5 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_6_6 :
    yW_2360 0 * rowA 6 6 0 + yW_2360 1 * rowA 6 6 1 + yW_2360 2 * rowA 6 6 2 + yW_2360 3 * rowA 6 6 3 + yW_2360 4 * rowA 6 6 4 + yW_2360 5 * rowA 6 6 5 + yW_2360 6 * rowA 6 6 6 + yW_2360 7 * rowA 6 6 7 + yW_2360 8 * rowA 6 6 8 ≤ db_2360 6 6 := by
  have hleft : yW_2360 0 * rowA 6 6 0 + yW_2360 1 * rowA 6 6 1 + yW_2360 2 * rowA 6 6 2 + yW_2360 3 * rowA 6 6 3 + yW_2360 4 * rowA 6 6 4 + yW_2360 5 * rowA 6 6 5 + yW_2360 6 * rowA 6 6 6 + yW_2360 7 * rowA 6 6 7 + yW_2360 8 * rowA 6 6 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 6 6 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_6_7 :
    yW_2360 0 * rowA 6 7 0 + yW_2360 1 * rowA 6 7 1 + yW_2360 2 * rowA 6 7 2 + yW_2360 3 * rowA 6 7 3 + yW_2360 4 * rowA 6 7 4 + yW_2360 5 * rowA 6 7 5 + yW_2360 6 * rowA 6 7 6 + yW_2360 7 * rowA 6 7 7 + yW_2360 8 * rowA 6 7 8 ≤ db_2360 6 7 := by
  have hleft : yW_2360 0 * rowA 6 7 0 + yW_2360 1 * rowA 6 7 1 + yW_2360 2 * rowA 6 7 2 + yW_2360 3 * rowA 6 7 3 + yW_2360 4 * rowA 6 7 4 + yW_2360 5 * rowA 6 7 5 + yW_2360 6 * rowA 6 7 6 + yW_2360 7 * rowA 6 7 7 + yW_2360 8 * rowA 6 7 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 6 7 = (1 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_6_8 :
    yW_2360 0 * rowA 6 8 0 + yW_2360 1 * rowA 6 8 1 + yW_2360 2 * rowA 6 8 2 + yW_2360 3 * rowA 6 8 3 + yW_2360 4 * rowA 6 8 4 + yW_2360 5 * rowA 6 8 5 + yW_2360 6 * rowA 6 8 6 + yW_2360 7 * rowA 6 8 7 + yW_2360 8 * rowA 6 8 8 ≤ db_2360 6 8 := by
  have hleft : yW_2360 0 * rowA 6 8 0 + yW_2360 1 * rowA 6 8 1 + yW_2360 2 * rowA 6 8 2 + yW_2360 3 * rowA 6 8 3 + yW_2360 4 * rowA 6 8 4 + yW_2360 5 * rowA 6 8 5 + yW_2360 6 * rowA 6 8 6 + yW_2360 7 * rowA 6 8 7 + yW_2360 8 * rowA 6 8 8 = (3 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 6 8 = (1 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_6_9 :
    yW_2360 0 * rowA 6 9 0 + yW_2360 1 * rowA 6 9 1 + yW_2360 2 * rowA 6 9 2 + yW_2360 3 * rowA 6 9 3 + yW_2360 4 * rowA 6 9 4 + yW_2360 5 * rowA 6 9 5 + yW_2360 6 * rowA 6 9 6 + yW_2360 7 * rowA 6 9 7 + yW_2360 8 * rowA 6 9 8 ≤ db_2360 6 9 := by
  have hleft : yW_2360 0 * rowA 6 9 0 + yW_2360 1 * rowA 6 9 1 + yW_2360 2 * rowA 6 9 2 + yW_2360 3 * rowA 6 9 3 + yW_2360 4 * rowA 6 9 4 + yW_2360 5 * rowA 6 9 5 + yW_2360 6 * rowA 6 9 6 + yW_2360 7 * rowA 6 9 7 + yW_2360 8 * rowA 6 9 8 = (7 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 6 9 = (9 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_7_0 :
    yW_2360 0 * rowA 7 0 0 + yW_2360 1 * rowA 7 0 1 + yW_2360 2 * rowA 7 0 2 + yW_2360 3 * rowA 7 0 3 + yW_2360 4 * rowA 7 0 4 + yW_2360 5 * rowA 7 0 5 + yW_2360 6 * rowA 7 0 6 + yW_2360 7 * rowA 7 0 7 + yW_2360 8 * rowA 7 0 8 ≤ db_2360 7 0 := by
  have hleft : yW_2360 0 * rowA 7 0 0 + yW_2360 1 * rowA 7 0 1 + yW_2360 2 * rowA 7 0 2 + yW_2360 3 * rowA 7 0 3 + yW_2360 4 * rowA 7 0 4 + yW_2360 5 * rowA 7 0 5 + yW_2360 6 * rowA 7 0 6 + yW_2360 7 * rowA 7 0 7 + yW_2360 8 * rowA 7 0 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 7 0 = (-9 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_7_1 :
    yW_2360 0 * rowA 7 1 0 + yW_2360 1 * rowA 7 1 1 + yW_2360 2 * rowA 7 1 2 + yW_2360 3 * rowA 7 1 3 + yW_2360 4 * rowA 7 1 4 + yW_2360 5 * rowA 7 1 5 + yW_2360 6 * rowA 7 1 6 + yW_2360 7 * rowA 7 1 7 + yW_2360 8 * rowA 7 1 8 ≤ db_2360 7 1 := by
  have hleft : yW_2360 0 * rowA 7 1 0 + yW_2360 1 * rowA 7 1 1 + yW_2360 2 * rowA 7 1 2 + yW_2360 3 * rowA 7 1 3 + yW_2360 4 * rowA 7 1 4 + yW_2360 5 * rowA 7 1 5 + yW_2360 6 * rowA 7 1 6 + yW_2360 7 * rowA 7 1 7 + yW_2360 8 * rowA 7 1 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 7 1 = (-1 : ℚ) / 2 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_7_2 :
    yW_2360 0 * rowA 7 2 0 + yW_2360 1 * rowA 7 2 1 + yW_2360 2 * rowA 7 2 2 + yW_2360 3 * rowA 7 2 3 + yW_2360 4 * rowA 7 2 4 + yW_2360 5 * rowA 7 2 5 + yW_2360 6 * rowA 7 2 6 + yW_2360 7 * rowA 7 2 7 + yW_2360 8 * rowA 7 2 8 ≤ db_2360 7 2 := by
  have hleft : yW_2360 0 * rowA 7 2 0 + yW_2360 1 * rowA 7 2 1 + yW_2360 2 * rowA 7 2 2 + yW_2360 3 * rowA 7 2 3 + yW_2360 4 * rowA 7 2 4 + yW_2360 5 * rowA 7 2 5 + yW_2360 6 * rowA 7 2 6 + yW_2360 7 * rowA 7 2 7 + yW_2360 8 * rowA 7 2 8 = (-9 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 7 2 = (-1 : ℚ) / 2 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_7_3 :
    yW_2360 0 * rowA 7 3 0 + yW_2360 1 * rowA 7 3 1 + yW_2360 2 * rowA 7 3 2 + yW_2360 3 * rowA 7 3 3 + yW_2360 4 * rowA 7 3 4 + yW_2360 5 * rowA 7 3 5 + yW_2360 6 * rowA 7 3 6 + yW_2360 7 * rowA 7 3 7 + yW_2360 8 * rowA 7 3 8 ≤ db_2360 7 3 := by
  have hleft : yW_2360 0 * rowA 7 3 0 + yW_2360 1 * rowA 7 3 1 + yW_2360 2 * rowA 7 3 2 + yW_2360 3 * rowA 7 3 3 + yW_2360 4 * rowA 7 3 4 + yW_2360 5 * rowA 7 3 5 + yW_2360 6 * rowA 7 3 6 + yW_2360 7 * rowA 7 3 7 + yW_2360 8 * rowA 7 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 7 3 = (-1 : ℚ) / 2 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_7_4 :
    yW_2360 0 * rowA 7 4 0 + yW_2360 1 * rowA 7 4 1 + yW_2360 2 * rowA 7 4 2 + yW_2360 3 * rowA 7 4 3 + yW_2360 4 * rowA 7 4 4 + yW_2360 5 * rowA 7 4 5 + yW_2360 6 * rowA 7 4 6 + yW_2360 7 * rowA 7 4 7 + yW_2360 8 * rowA 7 4 8 ≤ db_2360 7 4 := by
  have hleft : yW_2360 0 * rowA 7 4 0 + yW_2360 1 * rowA 7 4 1 + yW_2360 2 * rowA 7 4 2 + yW_2360 3 * rowA 7 4 3 + yW_2360 4 * rowA 7 4 4 + yW_2360 5 * rowA 7 4 5 + yW_2360 6 * rowA 7 4 6 + yW_2360 7 * rowA 7 4 7 + yW_2360 8 * rowA 7 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 7 4 = (-1 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_7_5 :
    yW_2360 0 * rowA 7 5 0 + yW_2360 1 * rowA 7 5 1 + yW_2360 2 * rowA 7 5 2 + yW_2360 3 * rowA 7 5 3 + yW_2360 4 * rowA 7 5 4 + yW_2360 5 * rowA 7 5 5 + yW_2360 6 * rowA 7 5 6 + yW_2360 7 * rowA 7 5 7 + yW_2360 8 * rowA 7 5 8 ≤ db_2360 7 5 := by
  have hleft : yW_2360 0 * rowA 7 5 0 + yW_2360 1 * rowA 7 5 1 + yW_2360 2 * rowA 7 5 2 + yW_2360 3 * rowA 7 5 3 + yW_2360 4 * rowA 7 5 4 + yW_2360 5 * rowA 7 5 5 + yW_2360 6 * rowA 7 5 6 + yW_2360 7 * rowA 7 5 7 + yW_2360 8 * rowA 7 5 8 = (-1 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 7 5 = (-1 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_7_6 :
    yW_2360 0 * rowA 7 6 0 + yW_2360 1 * rowA 7 6 1 + yW_2360 2 * rowA 7 6 2 + yW_2360 3 * rowA 7 6 3 + yW_2360 4 * rowA 7 6 4 + yW_2360 5 * rowA 7 6 5 + yW_2360 6 * rowA 7 6 6 + yW_2360 7 * rowA 7 6 7 + yW_2360 8 * rowA 7 6 8 ≤ db_2360 7 6 := by
  have hleft : yW_2360 0 * rowA 7 6 0 + yW_2360 1 * rowA 7 6 1 + yW_2360 2 * rowA 7 6 2 + yW_2360 3 * rowA 7 6 3 + yW_2360 4 * rowA 7 6 4 + yW_2360 5 * rowA 7 6 5 + yW_2360 6 * rowA 7 6 6 + yW_2360 7 * rowA 7 6 7 + yW_2360 8 * rowA 7 6 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 7 6 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_7_7 :
    yW_2360 0 * rowA 7 7 0 + yW_2360 1 * rowA 7 7 1 + yW_2360 2 * rowA 7 7 2 + yW_2360 3 * rowA 7 7 3 + yW_2360 4 * rowA 7 7 4 + yW_2360 5 * rowA 7 7 5 + yW_2360 6 * rowA 7 7 6 + yW_2360 7 * rowA 7 7 7 + yW_2360 8 * rowA 7 7 8 ≤ db_2360 7 7 := by
  have hleft : yW_2360 0 * rowA 7 7 0 + yW_2360 1 * rowA 7 7 1 + yW_2360 2 * rowA 7 7 2 + yW_2360 3 * rowA 7 7 3 + yW_2360 4 * rowA 7 7 4 + yW_2360 5 * rowA 7 7 5 + yW_2360 6 * rowA 7 7 6 + yW_2360 7 * rowA 7 7 7 + yW_2360 8 * rowA 7 7 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 7 7 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_7_8 :
    yW_2360 0 * rowA 7 8 0 + yW_2360 1 * rowA 7 8 1 + yW_2360 2 * rowA 7 8 2 + yW_2360 3 * rowA 7 8 3 + yW_2360 4 * rowA 7 8 4 + yW_2360 5 * rowA 7 8 5 + yW_2360 6 * rowA 7 8 6 + yW_2360 7 * rowA 7 8 7 + yW_2360 8 * rowA 7 8 8 ≤ db_2360 7 8 := by
  have hleft : yW_2360 0 * rowA 7 8 0 + yW_2360 1 * rowA 7 8 1 + yW_2360 2 * rowA 7 8 2 + yW_2360 3 * rowA 7 8 3 + yW_2360 4 * rowA 7 8 4 + yW_2360 5 * rowA 7 8 5 + yW_2360 6 * rowA 7 8 6 + yW_2360 7 * rowA 7 8 7 + yW_2360 8 * rowA 7 8 8 = (3 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 7 8 = (3 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_7_9 :
    yW_2360 0 * rowA 7 9 0 + yW_2360 1 * rowA 7 9 1 + yW_2360 2 * rowA 7 9 2 + yW_2360 3 * rowA 7 9 3 + yW_2360 4 * rowA 7 9 4 + yW_2360 5 * rowA 7 9 5 + yW_2360 6 * rowA 7 9 6 + yW_2360 7 * rowA 7 9 7 + yW_2360 8 * rowA 7 9 8 ≤ db_2360 7 9 := by
  have hleft : yW_2360 0 * rowA 7 9 0 + yW_2360 1 * rowA 7 9 1 + yW_2360 2 * rowA 7 9 2 + yW_2360 3 * rowA 7 9 3 + yW_2360 4 * rowA 7 9 4 + yW_2360 5 * rowA 7 9 5 + yW_2360 6 * rowA 7 9 6 + yW_2360 7 * rowA 7 9 7 + yW_2360 8 * rowA 7 9 8 = (7 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 7 9 = (7 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_8_0 :
    yW_2360 0 * rowA 8 0 0 + yW_2360 1 * rowA 8 0 1 + yW_2360 2 * rowA 8 0 2 + yW_2360 3 * rowA 8 0 3 + yW_2360 4 * rowA 8 0 4 + yW_2360 5 * rowA 8 0 5 + yW_2360 6 * rowA 8 0 6 + yW_2360 7 * rowA 8 0 7 + yW_2360 8 * rowA 8 0 8 ≤ db_2360 8 0 := by
  have hleft : yW_2360 0 * rowA 8 0 0 + yW_2360 1 * rowA 8 0 1 + yW_2360 2 * rowA 8 0 2 + yW_2360 3 * rowA 8 0 3 + yW_2360 4 * rowA 8 0 4 + yW_2360 5 * rowA 8 0 5 + yW_2360 6 * rowA 8 0 6 + yW_2360 7 * rowA 8 0 7 + yW_2360 8 * rowA 8 0 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 8 0 = (-11 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_8_1 :
    yW_2360 0 * rowA 8 1 0 + yW_2360 1 * rowA 8 1 1 + yW_2360 2 * rowA 8 1 2 + yW_2360 3 * rowA 8 1 3 + yW_2360 4 * rowA 8 1 4 + yW_2360 5 * rowA 8 1 5 + yW_2360 6 * rowA 8 1 6 + yW_2360 7 * rowA 8 1 7 + yW_2360 8 * rowA 8 1 8 ≤ db_2360 8 1 := by
  have hleft : yW_2360 0 * rowA 8 1 0 + yW_2360 1 * rowA 8 1 1 + yW_2360 2 * rowA 8 1 2 + yW_2360 3 * rowA 8 1 3 + yW_2360 4 * rowA 8 1 4 + yW_2360 5 * rowA 8 1 5 + yW_2360 6 * rowA 8 1 6 + yW_2360 7 * rowA 8 1 7 + yW_2360 8 * rowA 8 1 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 8 1 = (-5 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_8_2 :
    yW_2360 0 * rowA 8 2 0 + yW_2360 1 * rowA 8 2 1 + yW_2360 2 * rowA 8 2 2 + yW_2360 3 * rowA 8 2 3 + yW_2360 4 * rowA 8 2 4 + yW_2360 5 * rowA 8 2 5 + yW_2360 6 * rowA 8 2 6 + yW_2360 7 * rowA 8 2 7 + yW_2360 8 * rowA 8 2 8 ≤ db_2360 8 2 := by
  have hleft : yW_2360 0 * rowA 8 2 0 + yW_2360 1 * rowA 8 2 1 + yW_2360 2 * rowA 8 2 2 + yW_2360 3 * rowA 8 2 3 + yW_2360 4 * rowA 8 2 4 + yW_2360 5 * rowA 8 2 5 + yW_2360 6 * rowA 8 2 6 + yW_2360 7 * rowA 8 2 7 + yW_2360 8 * rowA 8 2 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 8 2 = (-5 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_8_3 :
    yW_2360 0 * rowA 8 3 0 + yW_2360 1 * rowA 8 3 1 + yW_2360 2 * rowA 8 3 2 + yW_2360 3 * rowA 8 3 3 + yW_2360 4 * rowA 8 3 4 + yW_2360 5 * rowA 8 3 5 + yW_2360 6 * rowA 8 3 6 + yW_2360 7 * rowA 8 3 7 + yW_2360 8 * rowA 8 3 8 ≤ db_2360 8 3 := by
  have hleft : yW_2360 0 * rowA 8 3 0 + yW_2360 1 * rowA 8 3 1 + yW_2360 2 * rowA 8 3 2 + yW_2360 3 * rowA 8 3 3 + yW_2360 4 * rowA 8 3 4 + yW_2360 5 * rowA 8 3 5 + yW_2360 6 * rowA 8 3 6 + yW_2360 7 * rowA 8 3 7 + yW_2360 8 * rowA 8 3 8 = (-11 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 8 3 = (-5 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_8_4 :
    yW_2360 0 * rowA 8 4 0 + yW_2360 1 * rowA 8 4 1 + yW_2360 2 * rowA 8 4 2 + yW_2360 3 * rowA 8 4 3 + yW_2360 4 * rowA 8 4 4 + yW_2360 5 * rowA 8 4 5 + yW_2360 6 * rowA 8 4 6 + yW_2360 7 * rowA 8 4 7 + yW_2360 8 * rowA 8 4 8 ≤ db_2360 8 4 := by
  have hleft : yW_2360 0 * rowA 8 4 0 + yW_2360 1 * rowA 8 4 1 + yW_2360 2 * rowA 8 4 2 + yW_2360 3 * rowA 8 4 3 + yW_2360 4 * rowA 8 4 4 + yW_2360 5 * rowA 8 4 5 + yW_2360 6 * rowA 8 4 6 + yW_2360 7 * rowA 8 4 7 + yW_2360 8 * rowA 8 4 8 = (-7 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 8 4 = (-3 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_8_5 :
    yW_2360 0 * rowA 8 5 0 + yW_2360 1 * rowA 8 5 1 + yW_2360 2 * rowA 8 5 2 + yW_2360 3 * rowA 8 5 3 + yW_2360 4 * rowA 8 5 4 + yW_2360 5 * rowA 8 5 5 + yW_2360 6 * rowA 8 5 6 + yW_2360 7 * rowA 8 5 7 + yW_2360 8 * rowA 8 5 8 ≤ db_2360 8 5 := by
  have hleft : yW_2360 0 * rowA 8 5 0 + yW_2360 1 * rowA 8 5 1 + yW_2360 2 * rowA 8 5 2 + yW_2360 3 * rowA 8 5 3 + yW_2360 4 * rowA 8 5 4 + yW_2360 5 * rowA 8 5 5 + yW_2360 6 * rowA 8 5 6 + yW_2360 7 * rowA 8 5 7 + yW_2360 8 * rowA 8 5 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 8 5 = (-3 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_8_6 :
    yW_2360 0 * rowA 8 6 0 + yW_2360 1 * rowA 8 6 1 + yW_2360 2 * rowA 8 6 2 + yW_2360 3 * rowA 8 6 3 + yW_2360 4 * rowA 8 6 4 + yW_2360 5 * rowA 8 6 5 + yW_2360 6 * rowA 8 6 6 + yW_2360 7 * rowA 8 6 7 + yW_2360 8 * rowA 8 6 8 ≤ db_2360 8 6 := by
  have hleft : yW_2360 0 * rowA 8 6 0 + yW_2360 1 * rowA 8 6 1 + yW_2360 2 * rowA 8 6 2 + yW_2360 3 * rowA 8 6 3 + yW_2360 4 * rowA 8 6 4 + yW_2360 5 * rowA 8 6 5 + yW_2360 6 * rowA 8 6 6 + yW_2360 7 * rowA 8 6 7 + yW_2360 8 * rowA 8 6 8 = (-3 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 8 6 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_8_7 :
    yW_2360 0 * rowA 8 7 0 + yW_2360 1 * rowA 8 7 1 + yW_2360 2 * rowA 8 7 2 + yW_2360 3 * rowA 8 7 3 + yW_2360 4 * rowA 8 7 4 + yW_2360 5 * rowA 8 7 5 + yW_2360 6 * rowA 8 7 6 + yW_2360 7 * rowA 8 7 7 + yW_2360 8 * rowA 8 7 8 ≤ db_2360 8 7 := by
  have hleft : yW_2360 0 * rowA 8 7 0 + yW_2360 1 * rowA 8 7 1 + yW_2360 2 * rowA 8 7 2 + yW_2360 3 * rowA 8 7 3 + yW_2360 4 * rowA 8 7 4 + yW_2360 5 * rowA 8 7 5 + yW_2360 6 * rowA 8 7 6 + yW_2360 7 * rowA 8 7 7 + yW_2360 8 * rowA 8 7 8 = (-3 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 8 7 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_8_8 :
    yW_2360 0 * rowA 8 8 0 + yW_2360 1 * rowA 8 8 1 + yW_2360 2 * rowA 8 8 2 + yW_2360 3 * rowA 8 8 3 + yW_2360 4 * rowA 8 8 4 + yW_2360 5 * rowA 8 8 5 + yW_2360 6 * rowA 8 8 6 + yW_2360 7 * rowA 8 8 7 + yW_2360 8 * rowA 8 8 8 ≤ db_2360 8 8 := by
  have hleft : yW_2360 0 * rowA 8 8 0 + yW_2360 1 * rowA 8 8 1 + yW_2360 2 * rowA 8 8 2 + yW_2360 3 * rowA 8 8 3 + yW_2360 4 * rowA 8 8 4 + yW_2360 5 * rowA 8 8 5 + yW_2360 6 * rowA 8 8 6 + yW_2360 7 * rowA 8 8 7 + yW_2360 8 * rowA 8 8 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 8 8 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_8_9 :
    yW_2360 0 * rowA 8 9 0 + yW_2360 1 * rowA 8 9 1 + yW_2360 2 * rowA 8 9 2 + yW_2360 3 * rowA 8 9 3 + yW_2360 4 * rowA 8 9 4 + yW_2360 5 * rowA 8 9 5 + yW_2360 6 * rowA 8 9 6 + yW_2360 7 * rowA 8 9 7 + yW_2360 8 * rowA 8 9 8 ≤ db_2360 8 9 := by
  have hleft : yW_2360 0 * rowA 8 9 0 + yW_2360 1 * rowA 8 9 1 + yW_2360 2 * rowA 8 9 2 + yW_2360 3 * rowA 8 9 3 + yW_2360 4 * rowA 8 9 4 + yW_2360 5 * rowA 8 9 5 + yW_2360 6 * rowA 8 9 6 + yW_2360 7 * rowA 8 9 7 + yW_2360 8 * rowA 8 9 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 8 9 = (5 : ℚ) / 16 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_9_0 :
    yW_2360 0 * rowA 9 0 0 + yW_2360 1 * rowA 9 0 1 + yW_2360 2 * rowA 9 0 2 + yW_2360 3 * rowA 9 0 3 + yW_2360 4 * rowA 9 0 4 + yW_2360 5 * rowA 9 0 5 + yW_2360 6 * rowA 9 0 6 + yW_2360 7 * rowA 9 0 7 + yW_2360 8 * rowA 9 0 8 ≤ db_2360 9 0 := by
  have hleft : yW_2360 0 * rowA 9 0 0 + yW_2360 1 * rowA 9 0 1 + yW_2360 2 * rowA 9 0 2 + yW_2360 3 * rowA 9 0 3 + yW_2360 4 * rowA 9 0 4 + yW_2360 5 * rowA 9 0 5 + yW_2360 6 * rowA 9 0 6 + yW_2360 7 * rowA 9 0 7 + yW_2360 8 * rowA 9 0 8 = (-1 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 9 0 = (-1 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_9_1 :
    yW_2360 0 * rowA 9 1 0 + yW_2360 1 * rowA 9 1 1 + yW_2360 2 * rowA 9 1 2 + yW_2360 3 * rowA 9 1 3 + yW_2360 4 * rowA 9 1 4 + yW_2360 5 * rowA 9 1 5 + yW_2360 6 * rowA 9 1 6 + yW_2360 7 * rowA 9 1 7 + yW_2360 8 * rowA 9 1 8 ≤ db_2360 9 1 := by
  have hleft : yW_2360 0 * rowA 9 1 0 + yW_2360 1 * rowA 9 1 1 + yW_2360 2 * rowA 9 1 2 + yW_2360 3 * rowA 9 1 3 + yW_2360 4 * rowA 9 1 4 + yW_2360 5 * rowA 9 1 5 + yW_2360 6 * rowA 9 1 6 + yW_2360 7 * rowA 9 1 7 + yW_2360 8 * rowA 9 1 8 = (-1 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 9 1 = (-7 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_9_2 :
    yW_2360 0 * rowA 9 2 0 + yW_2360 1 * rowA 9 2 1 + yW_2360 2 * rowA 9 2 2 + yW_2360 3 * rowA 9 2 3 + yW_2360 4 * rowA 9 2 4 + yW_2360 5 * rowA 9 2 5 + yW_2360 6 * rowA 9 2 6 + yW_2360 7 * rowA 9 2 7 + yW_2360 8 * rowA 9 2 8 ≤ db_2360 9 2 := by
  have hleft : yW_2360 0 * rowA 9 2 0 + yW_2360 1 * rowA 9 2 1 + yW_2360 2 * rowA 9 2 2 + yW_2360 3 * rowA 9 2 3 + yW_2360 4 * rowA 9 2 4 + yW_2360 5 * rowA 9 2 5 + yW_2360 6 * rowA 9 2 6 + yW_2360 7 * rowA 9 2 7 + yW_2360 8 * rowA 9 2 8 = (-1 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 9 2 = (-7 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_9_3 :
    yW_2360 0 * rowA 9 3 0 + yW_2360 1 * rowA 9 3 1 + yW_2360 2 * rowA 9 3 2 + yW_2360 3 * rowA 9 3 3 + yW_2360 4 * rowA 9 3 4 + yW_2360 5 * rowA 9 3 5 + yW_2360 6 * rowA 9 3 6 + yW_2360 7 * rowA 9 3 7 + yW_2360 8 * rowA 9 3 8 ≤ db_2360 9 3 := by
  have hleft : yW_2360 0 * rowA 9 3 0 + yW_2360 1 * rowA 9 3 1 + yW_2360 2 * rowA 9 3 2 + yW_2360 3 * rowA 9 3 3 + yW_2360 4 * rowA 9 3 4 + yW_2360 5 * rowA 9 3 5 + yW_2360 6 * rowA 9 3 6 + yW_2360 7 * rowA 9 3 7 + yW_2360 8 * rowA 9 3 8 = (-15 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 9 3 = (-7 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_9_4 :
    yW_2360 0 * rowA 9 4 0 + yW_2360 1 * rowA 9 4 1 + yW_2360 2 * rowA 9 4 2 + yW_2360 3 * rowA 9 4 3 + yW_2360 4 * rowA 9 4 4 + yW_2360 5 * rowA 9 4 5 + yW_2360 6 * rowA 9 4 6 + yW_2360 7 * rowA 9 4 7 + yW_2360 8 * rowA 9 4 8 ≤ db_2360 9 4 := by
  have hleft : yW_2360 0 * rowA 9 4 0 + yW_2360 1 * rowA 9 4 1 + yW_2360 2 * rowA 9 4 2 + yW_2360 3 * rowA 9 4 3 + yW_2360 4 * rowA 9 4 4 + yW_2360 5 * rowA 9 4 5 + yW_2360 6 * rowA 9 4 6 + yW_2360 7 * rowA 9 4 7 + yW_2360 8 * rowA 9 4 8 = (-11 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 9 4 = (-5 : ℚ) / 8 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_9_5 :
    yW_2360 0 * rowA 9 5 0 + yW_2360 1 * rowA 9 5 1 + yW_2360 2 * rowA 9 5 2 + yW_2360 3 * rowA 9 5 3 + yW_2360 4 * rowA 9 5 4 + yW_2360 5 * rowA 9 5 5 + yW_2360 6 * rowA 9 5 6 + yW_2360 7 * rowA 9 5 7 + yW_2360 8 * rowA 9 5 8 ≤ db_2360 9 5 := by
  have hleft : yW_2360 0 * rowA 9 5 0 + yW_2360 1 * rowA 9 5 1 + yW_2360 2 * rowA 9 5 2 + yW_2360 3 * rowA 9 5 3 + yW_2360 4 * rowA 9 5 4 + yW_2360 5 * rowA 9 5 5 + yW_2360 6 * rowA 9 5 6 + yW_2360 7 * rowA 9 5 7 + yW_2360 8 * rowA 9 5 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 9 5 = (-1 : ℚ) / 2 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_9_6 :
    yW_2360 0 * rowA 9 6 0 + yW_2360 1 * rowA 9 6 1 + yW_2360 2 * rowA 9 6 2 + yW_2360 3 * rowA 9 6 3 + yW_2360 4 * rowA 9 6 4 + yW_2360 5 * rowA 9 6 5 + yW_2360 6 * rowA 9 6 6 + yW_2360 7 * rowA 9 6 7 + yW_2360 8 * rowA 9 6 8 ≤ db_2360 9 6 := by
  have hleft : yW_2360 0 * rowA 9 6 0 + yW_2360 1 * rowA 9 6 1 + yW_2360 2 * rowA 9 6 2 + yW_2360 3 * rowA 9 6 3 + yW_2360 4 * rowA 9 6 4 + yW_2360 5 * rowA 9 6 5 + yW_2360 6 * rowA 9 6 6 + yW_2360 7 * rowA 9 6 7 + yW_2360 8 * rowA 9 6 8 = (-7 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 9 6 = (-1 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_9_7 :
    yW_2360 0 * rowA 9 7 0 + yW_2360 1 * rowA 9 7 1 + yW_2360 2 * rowA 9 7 2 + yW_2360 3 * rowA 9 7 3 + yW_2360 4 * rowA 9 7 4 + yW_2360 5 * rowA 9 7 5 + yW_2360 6 * rowA 9 7 6 + yW_2360 7 * rowA 9 7 7 + yW_2360 8 * rowA 9 7 8 ≤ db_2360 9 7 := by
  have hleft : yW_2360 0 * rowA 9 7 0 + yW_2360 1 * rowA 9 7 1 + yW_2360 2 * rowA 9 7 2 + yW_2360 3 * rowA 9 7 3 + yW_2360 4 * rowA 9 7 4 + yW_2360 5 * rowA 9 7 5 + yW_2360 6 * rowA 9 7 6 + yW_2360 7 * rowA 9 7 7 + yW_2360 8 * rowA 9 7 8 = (-7 : ℚ) / 16 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 9 7 = (-1 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_9_8 :
    yW_2360 0 * rowA 9 8 0 + yW_2360 1 * rowA 9 8 1 + yW_2360 2 * rowA 9 8 2 + yW_2360 3 * rowA 9 8 3 + yW_2360 4 * rowA 9 8 4 + yW_2360 5 * rowA 9 8 5 + yW_2360 6 * rowA 9 8 6 + yW_2360 7 * rowA 9 8 7 + yW_2360 8 * rowA 9 8 8 ≤ db_2360 9 8 := by
  have hleft : yW_2360 0 * rowA 9 8 0 + yW_2360 1 * rowA 9 8 1 + yW_2360 2 * rowA 9 8 2 + yW_2360 3 * rowA 9 8 3 + yW_2360 4 * rowA 9 8 4 + yW_2360 5 * rowA 9 8 5 + yW_2360 6 * rowA 9 8 6 + yW_2360 7 * rowA 9 8 7 + yW_2360 8 * rowA 9 8 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 9 8 = (-1 : ℚ) / 4 := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_9_9 :
    yW_2360 0 * rowA 9 9 0 + yW_2360 1 * rowA 9 9 1 + yW_2360 2 * rowA 9 9 2 + yW_2360 3 * rowA 9 9 3 + yW_2360 4 * rowA 9 9 4 + yW_2360 5 * rowA 9 9 5 + yW_2360 6 * rowA 9 9 6 + yW_2360 7 * rowA 9 9 7 + yW_2360 8 * rowA 9 9 8 ≤ db_2360 9 9 := by
  have hleft : yW_2360 0 * rowA 9 9 0 + yW_2360 1 * rowA 9 9 1 + yW_2360 2 * rowA 9 9 2 + yW_2360 3 * rowA 9 9 3 + yW_2360 4 * rowA 9 9 4 + yW_2360 5 * rowA 9 9 5 + yW_2360 6 * rowA 9 9 6 + yW_2360 7 * rowA 9 9 7 + yW_2360 8 * rowA 9 9 8 = (0 : ℚ) := by
    norm_num [yW_2360, rowA]
  have hright : db_2360 9 9 = (0 : ℚ) := by
    norm_num [db_2360, dbmVal_2360]
  rw [hleft, hright]
  norm_num

theorem row_cap_2360_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 0 j q) ≤ db_2360 0 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_0_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_0_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_0_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_0_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_0_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_0_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_0_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_0_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_0_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_0_9

theorem row_cap_2360_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 1 j q) ≤ db_2360 1 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_1_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_1_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_1_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_1_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_1_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_1_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_1_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_1_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_1_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_1_9

theorem row_cap_2360_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 2 j q) ≤ db_2360 2 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_2_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_2_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_2_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_2_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_2_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_2_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_2_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_2_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_2_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_2_9

theorem row_cap_2360_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 3 j q) ≤ db_2360 3 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_3_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_3_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_3_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_3_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_3_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_3_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_3_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_3_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_3_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_3_9

theorem row_cap_2360_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 4 j q) ≤ db_2360 4 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_4_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_4_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_4_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_4_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_4_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_4_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_4_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_4_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_4_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_4_9

theorem row_cap_2360_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 5 j q) ≤ db_2360 5 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_5_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_5_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_5_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_5_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_5_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_5_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_5_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_5_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_5_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_5_9

theorem row_cap_2360_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 6 j q) ≤ db_2360 6 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_6_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_6_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_6_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_6_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_6_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_6_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_6_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_6_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_6_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_6_9

theorem row_cap_2360_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 7 j q) ≤ db_2360 7 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_7_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_7_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_7_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_7_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_7_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_7_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_7_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_7_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_7_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_7_9

theorem row_cap_2360_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 8 j q) ≤ db_2360 8 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_8_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_8_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_8_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_8_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_8_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_8_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_8_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_8_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_8_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_8_9

theorem row_cap_2360_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 9 j q) ≤ db_2360 9 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_9_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_9_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_9_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_9_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_9_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_9_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_9_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_9_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_9_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2360_9_9

theorem row_cap_2360 (i j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA i j q) ≤ db_2360 i j := by
  fin_cases i
  · exact row_cap_2360_0 j
  · exact row_cap_2360_1 j
  · exact row_cap_2360_2 j
  · exact row_cap_2360_3 j
  · exact row_cap_2360_4 j
  · exact row_cap_2360_5 j
  · exact row_cap_2360_6 j
  · exact row_cap_2360_7 j
  · exact row_cap_2360_8 j
  · exact row_cap_2360_9 j

def dbmVal_2368 : Fin 10 → Fin 10 → ℤ
  | i, j => ![
      ![0, 512, 512, 512, 1536, 2048, 2560, 3072, 3072, 4096],
      ![0, 0, 512, 512, 1536, 2048, 2560, 3072, 3072, 4096],
      ![0, 0, 0, 512, 1536, 2048, 2560, 3072, 3072, 4096],
      ![0, 0, 0, 0, 1536, 2048, 2560, 3072, 3072, 4096],
      ![-1024, -1024, -1024, -1024, 0, 512, 1536, 1536, 1536, 3072],
      ![-1536, -1024, -1024, -1024, 0, 0, 1024, 1536, 1536, 2560],
      ![-1536, -1024, -1024, -1024, 0, 0, 0, 1536, 1536, 2560],
      ![-2048, -2048, -2048, -2048, -1024, -512, 0, 0, 512, 2048],
      ![-2560, -2560, -2560, -2560, -1024, -1024, 0, 0, 0, 1536],
      ![-4096, -3584, -3584, -3584, -2560, -2048, -1536, -1024, -1024, 0]
    ] i j

def db_2368 (i j : Fin 10) : ℚ := (dbmVal_2368 i j : ℚ) / 4096

theorem row_cap_2368_0_0 :
    yW_2368 0 * rowA 0 0 0 + yW_2368 1 * rowA 0 0 1 + yW_2368 2 * rowA 0 0 2 + yW_2368 3 * rowA 0 0 3 + yW_2368 4 * rowA 0 0 4 + yW_2368 5 * rowA 0 0 5 + yW_2368 6 * rowA 0 0 6 + yW_2368 7 * rowA 0 0 7 + yW_2368 8 * rowA 0 0 8 ≤ db_2368 0 0 := by
  have hleft : yW_2368 0 * rowA 0 0 0 + yW_2368 1 * rowA 0 0 1 + yW_2368 2 * rowA 0 0 2 + yW_2368 3 * rowA 0 0 3 + yW_2368 4 * rowA 0 0 4 + yW_2368 5 * rowA 0 0 5 + yW_2368 6 * rowA 0 0 6 + yW_2368 7 * rowA 0 0 7 + yW_2368 8 * rowA 0 0 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 0 0 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_0_1 :
    yW_2368 0 * rowA 0 1 0 + yW_2368 1 * rowA 0 1 1 + yW_2368 2 * rowA 0 1 2 + yW_2368 3 * rowA 0 1 3 + yW_2368 4 * rowA 0 1 4 + yW_2368 5 * rowA 0 1 5 + yW_2368 6 * rowA 0 1 6 + yW_2368 7 * rowA 0 1 7 + yW_2368 8 * rowA 0 1 8 ≤ db_2368 0 1 := by
  have hleft : yW_2368 0 * rowA 0 1 0 + yW_2368 1 * rowA 0 1 1 + yW_2368 2 * rowA 0 1 2 + yW_2368 3 * rowA 0 1 3 + yW_2368 4 * rowA 0 1 4 + yW_2368 5 * rowA 0 1 5 + yW_2368 6 * rowA 0 1 6 + yW_2368 7 * rowA 0 1 7 + yW_2368 8 * rowA 0 1 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 0 1 = (1 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_0_2 :
    yW_2368 0 * rowA 0 2 0 + yW_2368 1 * rowA 0 2 1 + yW_2368 2 * rowA 0 2 2 + yW_2368 3 * rowA 0 2 3 + yW_2368 4 * rowA 0 2 4 + yW_2368 5 * rowA 0 2 5 + yW_2368 6 * rowA 0 2 6 + yW_2368 7 * rowA 0 2 7 + yW_2368 8 * rowA 0 2 8 ≤ db_2368 0 2 := by
  have hleft : yW_2368 0 * rowA 0 2 0 + yW_2368 1 * rowA 0 2 1 + yW_2368 2 * rowA 0 2 2 + yW_2368 3 * rowA 0 2 3 + yW_2368 4 * rowA 0 2 4 + yW_2368 5 * rowA 0 2 5 + yW_2368 6 * rowA 0 2 6 + yW_2368 7 * rowA 0 2 7 + yW_2368 8 * rowA 0 2 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 0 2 = (1 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_0_3 :
    yW_2368 0 * rowA 0 3 0 + yW_2368 1 * rowA 0 3 1 + yW_2368 2 * rowA 0 3 2 + yW_2368 3 * rowA 0 3 3 + yW_2368 4 * rowA 0 3 4 + yW_2368 5 * rowA 0 3 5 + yW_2368 6 * rowA 0 3 6 + yW_2368 7 * rowA 0 3 7 + yW_2368 8 * rowA 0 3 8 ≤ db_2368 0 3 := by
  have hleft : yW_2368 0 * rowA 0 3 0 + yW_2368 1 * rowA 0 3 1 + yW_2368 2 * rowA 0 3 2 + yW_2368 3 * rowA 0 3 3 + yW_2368 4 * rowA 0 3 4 + yW_2368 5 * rowA 0 3 5 + yW_2368 6 * rowA 0 3 6 + yW_2368 7 * rowA 0 3 7 + yW_2368 8 * rowA 0 3 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 0 3 = (1 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_0_4 :
    yW_2368 0 * rowA 0 4 0 + yW_2368 1 * rowA 0 4 1 + yW_2368 2 * rowA 0 4 2 + yW_2368 3 * rowA 0 4 3 + yW_2368 4 * rowA 0 4 4 + yW_2368 5 * rowA 0 4 5 + yW_2368 6 * rowA 0 4 6 + yW_2368 7 * rowA 0 4 7 + yW_2368 8 * rowA 0 4 8 ≤ db_2368 0 4 := by
  have hleft : yW_2368 0 * rowA 0 4 0 + yW_2368 1 * rowA 0 4 1 + yW_2368 2 * rowA 0 4 2 + yW_2368 3 * rowA 0 4 3 + yW_2368 4 * rowA 0 4 4 + yW_2368 5 * rowA 0 4 5 + yW_2368 6 * rowA 0 4 6 + yW_2368 7 * rowA 0 4 7 + yW_2368 8 * rowA 0 4 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 0 4 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_0_5 :
    yW_2368 0 * rowA 0 5 0 + yW_2368 1 * rowA 0 5 1 + yW_2368 2 * rowA 0 5 2 + yW_2368 3 * rowA 0 5 3 + yW_2368 4 * rowA 0 5 4 + yW_2368 5 * rowA 0 5 5 + yW_2368 6 * rowA 0 5 6 + yW_2368 7 * rowA 0 5 7 + yW_2368 8 * rowA 0 5 8 ≤ db_2368 0 5 := by
  have hleft : yW_2368 0 * rowA 0 5 0 + yW_2368 1 * rowA 0 5 1 + yW_2368 2 * rowA 0 5 2 + yW_2368 3 * rowA 0 5 3 + yW_2368 4 * rowA 0 5 4 + yW_2368 5 * rowA 0 5 5 + yW_2368 6 * rowA 0 5 6 + yW_2368 7 * rowA 0 5 7 + yW_2368 8 * rowA 0 5 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 0 5 = (1 : ℚ) / 2 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_0_6 :
    yW_2368 0 * rowA 0 6 0 + yW_2368 1 * rowA 0 6 1 + yW_2368 2 * rowA 0 6 2 + yW_2368 3 * rowA 0 6 3 + yW_2368 4 * rowA 0 6 4 + yW_2368 5 * rowA 0 6 5 + yW_2368 6 * rowA 0 6 6 + yW_2368 7 * rowA 0 6 7 + yW_2368 8 * rowA 0 6 8 ≤ db_2368 0 6 := by
  have hleft : yW_2368 0 * rowA 0 6 0 + yW_2368 1 * rowA 0 6 1 + yW_2368 2 * rowA 0 6 2 + yW_2368 3 * rowA 0 6 3 + yW_2368 4 * rowA 0 6 4 + yW_2368 5 * rowA 0 6 5 + yW_2368 6 * rowA 0 6 6 + yW_2368 7 * rowA 0 6 7 + yW_2368 8 * rowA 0 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 0 6 = (5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_0_7 :
    yW_2368 0 * rowA 0 7 0 + yW_2368 1 * rowA 0 7 1 + yW_2368 2 * rowA 0 7 2 + yW_2368 3 * rowA 0 7 3 + yW_2368 4 * rowA 0 7 4 + yW_2368 5 * rowA 0 7 5 + yW_2368 6 * rowA 0 7 6 + yW_2368 7 * rowA 0 7 7 + yW_2368 8 * rowA 0 7 8 ≤ db_2368 0 7 := by
  have hleft : yW_2368 0 * rowA 0 7 0 + yW_2368 1 * rowA 0 7 1 + yW_2368 2 * rowA 0 7 2 + yW_2368 3 * rowA 0 7 3 + yW_2368 4 * rowA 0 7 4 + yW_2368 5 * rowA 0 7 5 + yW_2368 6 * rowA 0 7 6 + yW_2368 7 * rowA 0 7 7 + yW_2368 8 * rowA 0 7 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 0 7 = (3 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_0_8 :
    yW_2368 0 * rowA 0 8 0 + yW_2368 1 * rowA 0 8 1 + yW_2368 2 * rowA 0 8 2 + yW_2368 3 * rowA 0 8 3 + yW_2368 4 * rowA 0 8 4 + yW_2368 5 * rowA 0 8 5 + yW_2368 6 * rowA 0 8 6 + yW_2368 7 * rowA 0 8 7 + yW_2368 8 * rowA 0 8 8 ≤ db_2368 0 8 := by
  have hleft : yW_2368 0 * rowA 0 8 0 + yW_2368 1 * rowA 0 8 1 + yW_2368 2 * rowA 0 8 2 + yW_2368 3 * rowA 0 8 3 + yW_2368 4 * rowA 0 8 4 + yW_2368 5 * rowA 0 8 5 + yW_2368 6 * rowA 0 8 6 + yW_2368 7 * rowA 0 8 7 + yW_2368 8 * rowA 0 8 8 = (3 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 0 8 = (3 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_0_9 :
    yW_2368 0 * rowA 0 9 0 + yW_2368 1 * rowA 0 9 1 + yW_2368 2 * rowA 0 9 2 + yW_2368 3 * rowA 0 9 3 + yW_2368 4 * rowA 0 9 4 + yW_2368 5 * rowA 0 9 5 + yW_2368 6 * rowA 0 9 6 + yW_2368 7 * rowA 0 9 7 + yW_2368 8 * rowA 0 9 8 ≤ db_2368 0 9 := by
  have hleft : yW_2368 0 * rowA 0 9 0 + yW_2368 1 * rowA 0 9 1 + yW_2368 2 * rowA 0 9 2 + yW_2368 3 * rowA 0 9 3 + yW_2368 4 * rowA 0 9 4 + yW_2368 5 * rowA 0 9 5 + yW_2368 6 * rowA 0 9 6 + yW_2368 7 * rowA 0 9 7 + yW_2368 8 * rowA 0 9 8 = (1 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 0 9 = (1 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_1_0 :
    yW_2368 0 * rowA 1 0 0 + yW_2368 1 * rowA 1 0 1 + yW_2368 2 * rowA 1 0 2 + yW_2368 3 * rowA 1 0 3 + yW_2368 4 * rowA 1 0 4 + yW_2368 5 * rowA 1 0 5 + yW_2368 6 * rowA 1 0 6 + yW_2368 7 * rowA 1 0 7 + yW_2368 8 * rowA 1 0 8 ≤ db_2368 1 0 := by
  have hleft : yW_2368 0 * rowA 1 0 0 + yW_2368 1 * rowA 1 0 1 + yW_2368 2 * rowA 1 0 2 + yW_2368 3 * rowA 1 0 3 + yW_2368 4 * rowA 1 0 4 + yW_2368 5 * rowA 1 0 5 + yW_2368 6 * rowA 1 0 6 + yW_2368 7 * rowA 1 0 7 + yW_2368 8 * rowA 1 0 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 1 0 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_1_1 :
    yW_2368 0 * rowA 1 1 0 + yW_2368 1 * rowA 1 1 1 + yW_2368 2 * rowA 1 1 2 + yW_2368 3 * rowA 1 1 3 + yW_2368 4 * rowA 1 1 4 + yW_2368 5 * rowA 1 1 5 + yW_2368 6 * rowA 1 1 6 + yW_2368 7 * rowA 1 1 7 + yW_2368 8 * rowA 1 1 8 ≤ db_2368 1 1 := by
  have hleft : yW_2368 0 * rowA 1 1 0 + yW_2368 1 * rowA 1 1 1 + yW_2368 2 * rowA 1 1 2 + yW_2368 3 * rowA 1 1 3 + yW_2368 4 * rowA 1 1 4 + yW_2368 5 * rowA 1 1 5 + yW_2368 6 * rowA 1 1 6 + yW_2368 7 * rowA 1 1 7 + yW_2368 8 * rowA 1 1 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 1 1 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_1_2 :
    yW_2368 0 * rowA 1 2 0 + yW_2368 1 * rowA 1 2 1 + yW_2368 2 * rowA 1 2 2 + yW_2368 3 * rowA 1 2 3 + yW_2368 4 * rowA 1 2 4 + yW_2368 5 * rowA 1 2 5 + yW_2368 6 * rowA 1 2 6 + yW_2368 7 * rowA 1 2 7 + yW_2368 8 * rowA 1 2 8 ≤ db_2368 1 2 := by
  have hleft : yW_2368 0 * rowA 1 2 0 + yW_2368 1 * rowA 1 2 1 + yW_2368 2 * rowA 1 2 2 + yW_2368 3 * rowA 1 2 3 + yW_2368 4 * rowA 1 2 4 + yW_2368 5 * rowA 1 2 5 + yW_2368 6 * rowA 1 2 6 + yW_2368 7 * rowA 1 2 7 + yW_2368 8 * rowA 1 2 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 1 2 = (1 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_1_3 :
    yW_2368 0 * rowA 1 3 0 + yW_2368 1 * rowA 1 3 1 + yW_2368 2 * rowA 1 3 2 + yW_2368 3 * rowA 1 3 3 + yW_2368 4 * rowA 1 3 4 + yW_2368 5 * rowA 1 3 5 + yW_2368 6 * rowA 1 3 6 + yW_2368 7 * rowA 1 3 7 + yW_2368 8 * rowA 1 3 8 ≤ db_2368 1 3 := by
  have hleft : yW_2368 0 * rowA 1 3 0 + yW_2368 1 * rowA 1 3 1 + yW_2368 2 * rowA 1 3 2 + yW_2368 3 * rowA 1 3 3 + yW_2368 4 * rowA 1 3 4 + yW_2368 5 * rowA 1 3 5 + yW_2368 6 * rowA 1 3 6 + yW_2368 7 * rowA 1 3 7 + yW_2368 8 * rowA 1 3 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 1 3 = (1 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_1_4 :
    yW_2368 0 * rowA 1 4 0 + yW_2368 1 * rowA 1 4 1 + yW_2368 2 * rowA 1 4 2 + yW_2368 3 * rowA 1 4 3 + yW_2368 4 * rowA 1 4 4 + yW_2368 5 * rowA 1 4 5 + yW_2368 6 * rowA 1 4 6 + yW_2368 7 * rowA 1 4 7 + yW_2368 8 * rowA 1 4 8 ≤ db_2368 1 4 := by
  have hleft : yW_2368 0 * rowA 1 4 0 + yW_2368 1 * rowA 1 4 1 + yW_2368 2 * rowA 1 4 2 + yW_2368 3 * rowA 1 4 3 + yW_2368 4 * rowA 1 4 4 + yW_2368 5 * rowA 1 4 5 + yW_2368 6 * rowA 1 4 6 + yW_2368 7 * rowA 1 4 7 + yW_2368 8 * rowA 1 4 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 1 4 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_1_5 :
    yW_2368 0 * rowA 1 5 0 + yW_2368 1 * rowA 1 5 1 + yW_2368 2 * rowA 1 5 2 + yW_2368 3 * rowA 1 5 3 + yW_2368 4 * rowA 1 5 4 + yW_2368 5 * rowA 1 5 5 + yW_2368 6 * rowA 1 5 6 + yW_2368 7 * rowA 1 5 7 + yW_2368 8 * rowA 1 5 8 ≤ db_2368 1 5 := by
  have hleft : yW_2368 0 * rowA 1 5 0 + yW_2368 1 * rowA 1 5 1 + yW_2368 2 * rowA 1 5 2 + yW_2368 3 * rowA 1 5 3 + yW_2368 4 * rowA 1 5 4 + yW_2368 5 * rowA 1 5 5 + yW_2368 6 * rowA 1 5 6 + yW_2368 7 * rowA 1 5 7 + yW_2368 8 * rowA 1 5 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 1 5 = (1 : ℚ) / 2 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_1_6 :
    yW_2368 0 * rowA 1 6 0 + yW_2368 1 * rowA 1 6 1 + yW_2368 2 * rowA 1 6 2 + yW_2368 3 * rowA 1 6 3 + yW_2368 4 * rowA 1 6 4 + yW_2368 5 * rowA 1 6 5 + yW_2368 6 * rowA 1 6 6 + yW_2368 7 * rowA 1 6 7 + yW_2368 8 * rowA 1 6 8 ≤ db_2368 1 6 := by
  have hleft : yW_2368 0 * rowA 1 6 0 + yW_2368 1 * rowA 1 6 1 + yW_2368 2 * rowA 1 6 2 + yW_2368 3 * rowA 1 6 3 + yW_2368 4 * rowA 1 6 4 + yW_2368 5 * rowA 1 6 5 + yW_2368 6 * rowA 1 6 6 + yW_2368 7 * rowA 1 6 7 + yW_2368 8 * rowA 1 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 1 6 = (5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_1_7 :
    yW_2368 0 * rowA 1 7 0 + yW_2368 1 * rowA 1 7 1 + yW_2368 2 * rowA 1 7 2 + yW_2368 3 * rowA 1 7 3 + yW_2368 4 * rowA 1 7 4 + yW_2368 5 * rowA 1 7 5 + yW_2368 6 * rowA 1 7 6 + yW_2368 7 * rowA 1 7 7 + yW_2368 8 * rowA 1 7 8 ≤ db_2368 1 7 := by
  have hleft : yW_2368 0 * rowA 1 7 0 + yW_2368 1 * rowA 1 7 1 + yW_2368 2 * rowA 1 7 2 + yW_2368 3 * rowA 1 7 3 + yW_2368 4 * rowA 1 7 4 + yW_2368 5 * rowA 1 7 5 + yW_2368 6 * rowA 1 7 6 + yW_2368 7 * rowA 1 7 7 + yW_2368 8 * rowA 1 7 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 1 7 = (3 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_1_8 :
    yW_2368 0 * rowA 1 8 0 + yW_2368 1 * rowA 1 8 1 + yW_2368 2 * rowA 1 8 2 + yW_2368 3 * rowA 1 8 3 + yW_2368 4 * rowA 1 8 4 + yW_2368 5 * rowA 1 8 5 + yW_2368 6 * rowA 1 8 6 + yW_2368 7 * rowA 1 8 7 + yW_2368 8 * rowA 1 8 8 ≤ db_2368 1 8 := by
  have hleft : yW_2368 0 * rowA 1 8 0 + yW_2368 1 * rowA 1 8 1 + yW_2368 2 * rowA 1 8 2 + yW_2368 3 * rowA 1 8 3 + yW_2368 4 * rowA 1 8 4 + yW_2368 5 * rowA 1 8 5 + yW_2368 6 * rowA 1 8 6 + yW_2368 7 * rowA 1 8 7 + yW_2368 8 * rowA 1 8 8 = (3 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 1 8 = (3 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_1_9 :
    yW_2368 0 * rowA 1 9 0 + yW_2368 1 * rowA 1 9 1 + yW_2368 2 * rowA 1 9 2 + yW_2368 3 * rowA 1 9 3 + yW_2368 4 * rowA 1 9 4 + yW_2368 5 * rowA 1 9 5 + yW_2368 6 * rowA 1 9 6 + yW_2368 7 * rowA 1 9 7 + yW_2368 8 * rowA 1 9 8 ≤ db_2368 1 9 := by
  have hleft : yW_2368 0 * rowA 1 9 0 + yW_2368 1 * rowA 1 9 1 + yW_2368 2 * rowA 1 9 2 + yW_2368 3 * rowA 1 9 3 + yW_2368 4 * rowA 1 9 4 + yW_2368 5 * rowA 1 9 5 + yW_2368 6 * rowA 1 9 6 + yW_2368 7 * rowA 1 9 7 + yW_2368 8 * rowA 1 9 8 = (1 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 1 9 = (1 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_2_0 :
    yW_2368 0 * rowA 2 0 0 + yW_2368 1 * rowA 2 0 1 + yW_2368 2 * rowA 2 0 2 + yW_2368 3 * rowA 2 0 3 + yW_2368 4 * rowA 2 0 4 + yW_2368 5 * rowA 2 0 5 + yW_2368 6 * rowA 2 0 6 + yW_2368 7 * rowA 2 0 7 + yW_2368 8 * rowA 2 0 8 ≤ db_2368 2 0 := by
  have hleft : yW_2368 0 * rowA 2 0 0 + yW_2368 1 * rowA 2 0 1 + yW_2368 2 * rowA 2 0 2 + yW_2368 3 * rowA 2 0 3 + yW_2368 4 * rowA 2 0 4 + yW_2368 5 * rowA 2 0 5 + yW_2368 6 * rowA 2 0 6 + yW_2368 7 * rowA 2 0 7 + yW_2368 8 * rowA 2 0 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 2 0 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_2_1 :
    yW_2368 0 * rowA 2 1 0 + yW_2368 1 * rowA 2 1 1 + yW_2368 2 * rowA 2 1 2 + yW_2368 3 * rowA 2 1 3 + yW_2368 4 * rowA 2 1 4 + yW_2368 5 * rowA 2 1 5 + yW_2368 6 * rowA 2 1 6 + yW_2368 7 * rowA 2 1 7 + yW_2368 8 * rowA 2 1 8 ≤ db_2368 2 1 := by
  have hleft : yW_2368 0 * rowA 2 1 0 + yW_2368 1 * rowA 2 1 1 + yW_2368 2 * rowA 2 1 2 + yW_2368 3 * rowA 2 1 3 + yW_2368 4 * rowA 2 1 4 + yW_2368 5 * rowA 2 1 5 + yW_2368 6 * rowA 2 1 6 + yW_2368 7 * rowA 2 1 7 + yW_2368 8 * rowA 2 1 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 2 1 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_2_2 :
    yW_2368 0 * rowA 2 2 0 + yW_2368 1 * rowA 2 2 1 + yW_2368 2 * rowA 2 2 2 + yW_2368 3 * rowA 2 2 3 + yW_2368 4 * rowA 2 2 4 + yW_2368 5 * rowA 2 2 5 + yW_2368 6 * rowA 2 2 6 + yW_2368 7 * rowA 2 2 7 + yW_2368 8 * rowA 2 2 8 ≤ db_2368 2 2 := by
  have hleft : yW_2368 0 * rowA 2 2 0 + yW_2368 1 * rowA 2 2 1 + yW_2368 2 * rowA 2 2 2 + yW_2368 3 * rowA 2 2 3 + yW_2368 4 * rowA 2 2 4 + yW_2368 5 * rowA 2 2 5 + yW_2368 6 * rowA 2 2 6 + yW_2368 7 * rowA 2 2 7 + yW_2368 8 * rowA 2 2 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 2 2 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_2_3 :
    yW_2368 0 * rowA 2 3 0 + yW_2368 1 * rowA 2 3 1 + yW_2368 2 * rowA 2 3 2 + yW_2368 3 * rowA 2 3 3 + yW_2368 4 * rowA 2 3 4 + yW_2368 5 * rowA 2 3 5 + yW_2368 6 * rowA 2 3 6 + yW_2368 7 * rowA 2 3 7 + yW_2368 8 * rowA 2 3 8 ≤ db_2368 2 3 := by
  have hleft : yW_2368 0 * rowA 2 3 0 + yW_2368 1 * rowA 2 3 1 + yW_2368 2 * rowA 2 3 2 + yW_2368 3 * rowA 2 3 3 + yW_2368 4 * rowA 2 3 4 + yW_2368 5 * rowA 2 3 5 + yW_2368 6 * rowA 2 3 6 + yW_2368 7 * rowA 2 3 7 + yW_2368 8 * rowA 2 3 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 2 3 = (1 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_2_4 :
    yW_2368 0 * rowA 2 4 0 + yW_2368 1 * rowA 2 4 1 + yW_2368 2 * rowA 2 4 2 + yW_2368 3 * rowA 2 4 3 + yW_2368 4 * rowA 2 4 4 + yW_2368 5 * rowA 2 4 5 + yW_2368 6 * rowA 2 4 6 + yW_2368 7 * rowA 2 4 7 + yW_2368 8 * rowA 2 4 8 ≤ db_2368 2 4 := by
  have hleft : yW_2368 0 * rowA 2 4 0 + yW_2368 1 * rowA 2 4 1 + yW_2368 2 * rowA 2 4 2 + yW_2368 3 * rowA 2 4 3 + yW_2368 4 * rowA 2 4 4 + yW_2368 5 * rowA 2 4 5 + yW_2368 6 * rowA 2 4 6 + yW_2368 7 * rowA 2 4 7 + yW_2368 8 * rowA 2 4 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 2 4 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_2_5 :
    yW_2368 0 * rowA 2 5 0 + yW_2368 1 * rowA 2 5 1 + yW_2368 2 * rowA 2 5 2 + yW_2368 3 * rowA 2 5 3 + yW_2368 4 * rowA 2 5 4 + yW_2368 5 * rowA 2 5 5 + yW_2368 6 * rowA 2 5 6 + yW_2368 7 * rowA 2 5 7 + yW_2368 8 * rowA 2 5 8 ≤ db_2368 2 5 := by
  have hleft : yW_2368 0 * rowA 2 5 0 + yW_2368 1 * rowA 2 5 1 + yW_2368 2 * rowA 2 5 2 + yW_2368 3 * rowA 2 5 3 + yW_2368 4 * rowA 2 5 4 + yW_2368 5 * rowA 2 5 5 + yW_2368 6 * rowA 2 5 6 + yW_2368 7 * rowA 2 5 7 + yW_2368 8 * rowA 2 5 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 2 5 = (1 : ℚ) / 2 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_2_6 :
    yW_2368 0 * rowA 2 6 0 + yW_2368 1 * rowA 2 6 1 + yW_2368 2 * rowA 2 6 2 + yW_2368 3 * rowA 2 6 3 + yW_2368 4 * rowA 2 6 4 + yW_2368 5 * rowA 2 6 5 + yW_2368 6 * rowA 2 6 6 + yW_2368 7 * rowA 2 6 7 + yW_2368 8 * rowA 2 6 8 ≤ db_2368 2 6 := by
  have hleft : yW_2368 0 * rowA 2 6 0 + yW_2368 1 * rowA 2 6 1 + yW_2368 2 * rowA 2 6 2 + yW_2368 3 * rowA 2 6 3 + yW_2368 4 * rowA 2 6 4 + yW_2368 5 * rowA 2 6 5 + yW_2368 6 * rowA 2 6 6 + yW_2368 7 * rowA 2 6 7 + yW_2368 8 * rowA 2 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 2 6 = (5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_2_7 :
    yW_2368 0 * rowA 2 7 0 + yW_2368 1 * rowA 2 7 1 + yW_2368 2 * rowA 2 7 2 + yW_2368 3 * rowA 2 7 3 + yW_2368 4 * rowA 2 7 4 + yW_2368 5 * rowA 2 7 5 + yW_2368 6 * rowA 2 7 6 + yW_2368 7 * rowA 2 7 7 + yW_2368 8 * rowA 2 7 8 ≤ db_2368 2 7 := by
  have hleft : yW_2368 0 * rowA 2 7 0 + yW_2368 1 * rowA 2 7 1 + yW_2368 2 * rowA 2 7 2 + yW_2368 3 * rowA 2 7 3 + yW_2368 4 * rowA 2 7 4 + yW_2368 5 * rowA 2 7 5 + yW_2368 6 * rowA 2 7 6 + yW_2368 7 * rowA 2 7 7 + yW_2368 8 * rowA 2 7 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 2 7 = (3 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_2_8 :
    yW_2368 0 * rowA 2 8 0 + yW_2368 1 * rowA 2 8 1 + yW_2368 2 * rowA 2 8 2 + yW_2368 3 * rowA 2 8 3 + yW_2368 4 * rowA 2 8 4 + yW_2368 5 * rowA 2 8 5 + yW_2368 6 * rowA 2 8 6 + yW_2368 7 * rowA 2 8 7 + yW_2368 8 * rowA 2 8 8 ≤ db_2368 2 8 := by
  have hleft : yW_2368 0 * rowA 2 8 0 + yW_2368 1 * rowA 2 8 1 + yW_2368 2 * rowA 2 8 2 + yW_2368 3 * rowA 2 8 3 + yW_2368 4 * rowA 2 8 4 + yW_2368 5 * rowA 2 8 5 + yW_2368 6 * rowA 2 8 6 + yW_2368 7 * rowA 2 8 7 + yW_2368 8 * rowA 2 8 8 = (3 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 2 8 = (3 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_2_9 :
    yW_2368 0 * rowA 2 9 0 + yW_2368 1 * rowA 2 9 1 + yW_2368 2 * rowA 2 9 2 + yW_2368 3 * rowA 2 9 3 + yW_2368 4 * rowA 2 9 4 + yW_2368 5 * rowA 2 9 5 + yW_2368 6 * rowA 2 9 6 + yW_2368 7 * rowA 2 9 7 + yW_2368 8 * rowA 2 9 8 ≤ db_2368 2 9 := by
  have hleft : yW_2368 0 * rowA 2 9 0 + yW_2368 1 * rowA 2 9 1 + yW_2368 2 * rowA 2 9 2 + yW_2368 3 * rowA 2 9 3 + yW_2368 4 * rowA 2 9 4 + yW_2368 5 * rowA 2 9 5 + yW_2368 6 * rowA 2 9 6 + yW_2368 7 * rowA 2 9 7 + yW_2368 8 * rowA 2 9 8 = (1 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 2 9 = (1 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_3_0 :
    yW_2368 0 * rowA 3 0 0 + yW_2368 1 * rowA 3 0 1 + yW_2368 2 * rowA 3 0 2 + yW_2368 3 * rowA 3 0 3 + yW_2368 4 * rowA 3 0 4 + yW_2368 5 * rowA 3 0 5 + yW_2368 6 * rowA 3 0 6 + yW_2368 7 * rowA 3 0 7 + yW_2368 8 * rowA 3 0 8 ≤ db_2368 3 0 := by
  have hleft : yW_2368 0 * rowA 3 0 0 + yW_2368 1 * rowA 3 0 1 + yW_2368 2 * rowA 3 0 2 + yW_2368 3 * rowA 3 0 3 + yW_2368 4 * rowA 3 0 4 + yW_2368 5 * rowA 3 0 5 + yW_2368 6 * rowA 3 0 6 + yW_2368 7 * rowA 3 0 7 + yW_2368 8 * rowA 3 0 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 3 0 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_3_1 :
    yW_2368 0 * rowA 3 1 0 + yW_2368 1 * rowA 3 1 1 + yW_2368 2 * rowA 3 1 2 + yW_2368 3 * rowA 3 1 3 + yW_2368 4 * rowA 3 1 4 + yW_2368 5 * rowA 3 1 5 + yW_2368 6 * rowA 3 1 6 + yW_2368 7 * rowA 3 1 7 + yW_2368 8 * rowA 3 1 8 ≤ db_2368 3 1 := by
  have hleft : yW_2368 0 * rowA 3 1 0 + yW_2368 1 * rowA 3 1 1 + yW_2368 2 * rowA 3 1 2 + yW_2368 3 * rowA 3 1 3 + yW_2368 4 * rowA 3 1 4 + yW_2368 5 * rowA 3 1 5 + yW_2368 6 * rowA 3 1 6 + yW_2368 7 * rowA 3 1 7 + yW_2368 8 * rowA 3 1 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 3 1 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_3_2 :
    yW_2368 0 * rowA 3 2 0 + yW_2368 1 * rowA 3 2 1 + yW_2368 2 * rowA 3 2 2 + yW_2368 3 * rowA 3 2 3 + yW_2368 4 * rowA 3 2 4 + yW_2368 5 * rowA 3 2 5 + yW_2368 6 * rowA 3 2 6 + yW_2368 7 * rowA 3 2 7 + yW_2368 8 * rowA 3 2 8 ≤ db_2368 3 2 := by
  have hleft : yW_2368 0 * rowA 3 2 0 + yW_2368 1 * rowA 3 2 1 + yW_2368 2 * rowA 3 2 2 + yW_2368 3 * rowA 3 2 3 + yW_2368 4 * rowA 3 2 4 + yW_2368 5 * rowA 3 2 5 + yW_2368 6 * rowA 3 2 6 + yW_2368 7 * rowA 3 2 7 + yW_2368 8 * rowA 3 2 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 3 2 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_3_3 :
    yW_2368 0 * rowA 3 3 0 + yW_2368 1 * rowA 3 3 1 + yW_2368 2 * rowA 3 3 2 + yW_2368 3 * rowA 3 3 3 + yW_2368 4 * rowA 3 3 4 + yW_2368 5 * rowA 3 3 5 + yW_2368 6 * rowA 3 3 6 + yW_2368 7 * rowA 3 3 7 + yW_2368 8 * rowA 3 3 8 ≤ db_2368 3 3 := by
  have hleft : yW_2368 0 * rowA 3 3 0 + yW_2368 1 * rowA 3 3 1 + yW_2368 2 * rowA 3 3 2 + yW_2368 3 * rowA 3 3 3 + yW_2368 4 * rowA 3 3 4 + yW_2368 5 * rowA 3 3 5 + yW_2368 6 * rowA 3 3 6 + yW_2368 7 * rowA 3 3 7 + yW_2368 8 * rowA 3 3 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 3 3 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_3_4 :
    yW_2368 0 * rowA 3 4 0 + yW_2368 1 * rowA 3 4 1 + yW_2368 2 * rowA 3 4 2 + yW_2368 3 * rowA 3 4 3 + yW_2368 4 * rowA 3 4 4 + yW_2368 5 * rowA 3 4 5 + yW_2368 6 * rowA 3 4 6 + yW_2368 7 * rowA 3 4 7 + yW_2368 8 * rowA 3 4 8 ≤ db_2368 3 4 := by
  have hleft : yW_2368 0 * rowA 3 4 0 + yW_2368 1 * rowA 3 4 1 + yW_2368 2 * rowA 3 4 2 + yW_2368 3 * rowA 3 4 3 + yW_2368 4 * rowA 3 4 4 + yW_2368 5 * rowA 3 4 5 + yW_2368 6 * rowA 3 4 6 + yW_2368 7 * rowA 3 4 7 + yW_2368 8 * rowA 3 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 3 4 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_3_5 :
    yW_2368 0 * rowA 3 5 0 + yW_2368 1 * rowA 3 5 1 + yW_2368 2 * rowA 3 5 2 + yW_2368 3 * rowA 3 5 3 + yW_2368 4 * rowA 3 5 4 + yW_2368 5 * rowA 3 5 5 + yW_2368 6 * rowA 3 5 6 + yW_2368 7 * rowA 3 5 7 + yW_2368 8 * rowA 3 5 8 ≤ db_2368 3 5 := by
  have hleft : yW_2368 0 * rowA 3 5 0 + yW_2368 1 * rowA 3 5 1 + yW_2368 2 * rowA 3 5 2 + yW_2368 3 * rowA 3 5 3 + yW_2368 4 * rowA 3 5 4 + yW_2368 5 * rowA 3 5 5 + yW_2368 6 * rowA 3 5 6 + yW_2368 7 * rowA 3 5 7 + yW_2368 8 * rowA 3 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 3 5 = (1 : ℚ) / 2 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_3_6 :
    yW_2368 0 * rowA 3 6 0 + yW_2368 1 * rowA 3 6 1 + yW_2368 2 * rowA 3 6 2 + yW_2368 3 * rowA 3 6 3 + yW_2368 4 * rowA 3 6 4 + yW_2368 5 * rowA 3 6 5 + yW_2368 6 * rowA 3 6 6 + yW_2368 7 * rowA 3 6 7 + yW_2368 8 * rowA 3 6 8 ≤ db_2368 3 6 := by
  have hleft : yW_2368 0 * rowA 3 6 0 + yW_2368 1 * rowA 3 6 1 + yW_2368 2 * rowA 3 6 2 + yW_2368 3 * rowA 3 6 3 + yW_2368 4 * rowA 3 6 4 + yW_2368 5 * rowA 3 6 5 + yW_2368 6 * rowA 3 6 6 + yW_2368 7 * rowA 3 6 7 + yW_2368 8 * rowA 3 6 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 3 6 = (5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_3_7 :
    yW_2368 0 * rowA 3 7 0 + yW_2368 1 * rowA 3 7 1 + yW_2368 2 * rowA 3 7 2 + yW_2368 3 * rowA 3 7 3 + yW_2368 4 * rowA 3 7 4 + yW_2368 5 * rowA 3 7 5 + yW_2368 6 * rowA 3 7 6 + yW_2368 7 * rowA 3 7 7 + yW_2368 8 * rowA 3 7 8 ≤ db_2368 3 7 := by
  have hleft : yW_2368 0 * rowA 3 7 0 + yW_2368 1 * rowA 3 7 1 + yW_2368 2 * rowA 3 7 2 + yW_2368 3 * rowA 3 7 3 + yW_2368 4 * rowA 3 7 4 + yW_2368 5 * rowA 3 7 5 + yW_2368 6 * rowA 3 7 6 + yW_2368 7 * rowA 3 7 7 + yW_2368 8 * rowA 3 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 3 7 = (3 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_3_8 :
    yW_2368 0 * rowA 3 8 0 + yW_2368 1 * rowA 3 8 1 + yW_2368 2 * rowA 3 8 2 + yW_2368 3 * rowA 3 8 3 + yW_2368 4 * rowA 3 8 4 + yW_2368 5 * rowA 3 8 5 + yW_2368 6 * rowA 3 8 6 + yW_2368 7 * rowA 3 8 7 + yW_2368 8 * rowA 3 8 8 ≤ db_2368 3 8 := by
  have hleft : yW_2368 0 * rowA 3 8 0 + yW_2368 1 * rowA 3 8 1 + yW_2368 2 * rowA 3 8 2 + yW_2368 3 * rowA 3 8 3 + yW_2368 4 * rowA 3 8 4 + yW_2368 5 * rowA 3 8 5 + yW_2368 6 * rowA 3 8 6 + yW_2368 7 * rowA 3 8 7 + yW_2368 8 * rowA 3 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 3 8 = (3 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_3_9 :
    yW_2368 0 * rowA 3 9 0 + yW_2368 1 * rowA 3 9 1 + yW_2368 2 * rowA 3 9 2 + yW_2368 3 * rowA 3 9 3 + yW_2368 4 * rowA 3 9 4 + yW_2368 5 * rowA 3 9 5 + yW_2368 6 * rowA 3 9 6 + yW_2368 7 * rowA 3 9 7 + yW_2368 8 * rowA 3 9 8 ≤ db_2368 3 9 := by
  have hleft : yW_2368 0 * rowA 3 9 0 + yW_2368 1 * rowA 3 9 1 + yW_2368 2 * rowA 3 9 2 + yW_2368 3 * rowA 3 9 3 + yW_2368 4 * rowA 3 9 4 + yW_2368 5 * rowA 3 9 5 + yW_2368 6 * rowA 3 9 6 + yW_2368 7 * rowA 3 9 7 + yW_2368 8 * rowA 3 9 8 = (7 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 3 9 = (1 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_4_0 :
    yW_2368 0 * rowA 4 0 0 + yW_2368 1 * rowA 4 0 1 + yW_2368 2 * rowA 4 0 2 + yW_2368 3 * rowA 4 0 3 + yW_2368 4 * rowA 4 0 4 + yW_2368 5 * rowA 4 0 5 + yW_2368 6 * rowA 4 0 6 + yW_2368 7 * rowA 4 0 7 + yW_2368 8 * rowA 4 0 8 ≤ db_2368 4 0 := by
  have hleft : yW_2368 0 * rowA 4 0 0 + yW_2368 1 * rowA 4 0 1 + yW_2368 2 * rowA 4 0 2 + yW_2368 3 * rowA 4 0 3 + yW_2368 4 * rowA 4 0 4 + yW_2368 5 * rowA 4 0 5 + yW_2368 6 * rowA 4 0 6 + yW_2368 7 * rowA 4 0 7 + yW_2368 8 * rowA 4 0 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 4 0 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_4_1 :
    yW_2368 0 * rowA 4 1 0 + yW_2368 1 * rowA 4 1 1 + yW_2368 2 * rowA 4 1 2 + yW_2368 3 * rowA 4 1 3 + yW_2368 4 * rowA 4 1 4 + yW_2368 5 * rowA 4 1 5 + yW_2368 6 * rowA 4 1 6 + yW_2368 7 * rowA 4 1 7 + yW_2368 8 * rowA 4 1 8 ≤ db_2368 4 1 := by
  have hleft : yW_2368 0 * rowA 4 1 0 + yW_2368 1 * rowA 4 1 1 + yW_2368 2 * rowA 4 1 2 + yW_2368 3 * rowA 4 1 3 + yW_2368 4 * rowA 4 1 4 + yW_2368 5 * rowA 4 1 5 + yW_2368 6 * rowA 4 1 6 + yW_2368 7 * rowA 4 1 7 + yW_2368 8 * rowA 4 1 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 4 1 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_4_2 :
    yW_2368 0 * rowA 4 2 0 + yW_2368 1 * rowA 4 2 1 + yW_2368 2 * rowA 4 2 2 + yW_2368 3 * rowA 4 2 3 + yW_2368 4 * rowA 4 2 4 + yW_2368 5 * rowA 4 2 5 + yW_2368 6 * rowA 4 2 6 + yW_2368 7 * rowA 4 2 7 + yW_2368 8 * rowA 4 2 8 ≤ db_2368 4 2 := by
  have hleft : yW_2368 0 * rowA 4 2 0 + yW_2368 1 * rowA 4 2 1 + yW_2368 2 * rowA 4 2 2 + yW_2368 3 * rowA 4 2 3 + yW_2368 4 * rowA 4 2 4 + yW_2368 5 * rowA 4 2 5 + yW_2368 6 * rowA 4 2 6 + yW_2368 7 * rowA 4 2 7 + yW_2368 8 * rowA 4 2 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 4 2 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_4_3 :
    yW_2368 0 * rowA 4 3 0 + yW_2368 1 * rowA 4 3 1 + yW_2368 2 * rowA 4 3 2 + yW_2368 3 * rowA 4 3 3 + yW_2368 4 * rowA 4 3 4 + yW_2368 5 * rowA 4 3 5 + yW_2368 6 * rowA 4 3 6 + yW_2368 7 * rowA 4 3 7 + yW_2368 8 * rowA 4 3 8 ≤ db_2368 4 3 := by
  have hleft : yW_2368 0 * rowA 4 3 0 + yW_2368 1 * rowA 4 3 1 + yW_2368 2 * rowA 4 3 2 + yW_2368 3 * rowA 4 3 3 + yW_2368 4 * rowA 4 3 4 + yW_2368 5 * rowA 4 3 5 + yW_2368 6 * rowA 4 3 6 + yW_2368 7 * rowA 4 3 7 + yW_2368 8 * rowA 4 3 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 4 3 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_4_4 :
    yW_2368 0 * rowA 4 4 0 + yW_2368 1 * rowA 4 4 1 + yW_2368 2 * rowA 4 4 2 + yW_2368 3 * rowA 4 4 3 + yW_2368 4 * rowA 4 4 4 + yW_2368 5 * rowA 4 4 5 + yW_2368 6 * rowA 4 4 6 + yW_2368 7 * rowA 4 4 7 + yW_2368 8 * rowA 4 4 8 ≤ db_2368 4 4 := by
  have hleft : yW_2368 0 * rowA 4 4 0 + yW_2368 1 * rowA 4 4 1 + yW_2368 2 * rowA 4 4 2 + yW_2368 3 * rowA 4 4 3 + yW_2368 4 * rowA 4 4 4 + yW_2368 5 * rowA 4 4 5 + yW_2368 6 * rowA 4 4 6 + yW_2368 7 * rowA 4 4 7 + yW_2368 8 * rowA 4 4 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 4 4 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_4_5 :
    yW_2368 0 * rowA 4 5 0 + yW_2368 1 * rowA 4 5 1 + yW_2368 2 * rowA 4 5 2 + yW_2368 3 * rowA 4 5 3 + yW_2368 4 * rowA 4 5 4 + yW_2368 5 * rowA 4 5 5 + yW_2368 6 * rowA 4 5 6 + yW_2368 7 * rowA 4 5 7 + yW_2368 8 * rowA 4 5 8 ≤ db_2368 4 5 := by
  have hleft : yW_2368 0 * rowA 4 5 0 + yW_2368 1 * rowA 4 5 1 + yW_2368 2 * rowA 4 5 2 + yW_2368 3 * rowA 4 5 3 + yW_2368 4 * rowA 4 5 4 + yW_2368 5 * rowA 4 5 5 + yW_2368 6 * rowA 4 5 6 + yW_2368 7 * rowA 4 5 7 + yW_2368 8 * rowA 4 5 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 4 5 = (1 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_4_6 :
    yW_2368 0 * rowA 4 6 0 + yW_2368 1 * rowA 4 6 1 + yW_2368 2 * rowA 4 6 2 + yW_2368 3 * rowA 4 6 3 + yW_2368 4 * rowA 4 6 4 + yW_2368 5 * rowA 4 6 5 + yW_2368 6 * rowA 4 6 6 + yW_2368 7 * rowA 4 6 7 + yW_2368 8 * rowA 4 6 8 ≤ db_2368 4 6 := by
  have hleft : yW_2368 0 * rowA 4 6 0 + yW_2368 1 * rowA 4 6 1 + yW_2368 2 * rowA 4 6 2 + yW_2368 3 * rowA 4 6 3 + yW_2368 4 * rowA 4 6 4 + yW_2368 5 * rowA 4 6 5 + yW_2368 6 * rowA 4 6 6 + yW_2368 7 * rowA 4 6 7 + yW_2368 8 * rowA 4 6 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 4 6 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_4_7 :
    yW_2368 0 * rowA 4 7 0 + yW_2368 1 * rowA 4 7 1 + yW_2368 2 * rowA 4 7 2 + yW_2368 3 * rowA 4 7 3 + yW_2368 4 * rowA 4 7 4 + yW_2368 5 * rowA 4 7 5 + yW_2368 6 * rowA 4 7 6 + yW_2368 7 * rowA 4 7 7 + yW_2368 8 * rowA 4 7 8 ≤ db_2368 4 7 := by
  have hleft : yW_2368 0 * rowA 4 7 0 + yW_2368 1 * rowA 4 7 1 + yW_2368 2 * rowA 4 7 2 + yW_2368 3 * rowA 4 7 3 + yW_2368 4 * rowA 4 7 4 + yW_2368 5 * rowA 4 7 5 + yW_2368 6 * rowA 4 7 6 + yW_2368 7 * rowA 4 7 7 + yW_2368 8 * rowA 4 7 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 4 7 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_4_8 :
    yW_2368 0 * rowA 4 8 0 + yW_2368 1 * rowA 4 8 1 + yW_2368 2 * rowA 4 8 2 + yW_2368 3 * rowA 4 8 3 + yW_2368 4 * rowA 4 8 4 + yW_2368 5 * rowA 4 8 5 + yW_2368 6 * rowA 4 8 6 + yW_2368 7 * rowA 4 8 7 + yW_2368 8 * rowA 4 8 8 ≤ db_2368 4 8 := by
  have hleft : yW_2368 0 * rowA 4 8 0 + yW_2368 1 * rowA 4 8 1 + yW_2368 2 * rowA 4 8 2 + yW_2368 3 * rowA 4 8 3 + yW_2368 4 * rowA 4 8 4 + yW_2368 5 * rowA 4 8 5 + yW_2368 6 * rowA 4 8 6 + yW_2368 7 * rowA 4 8 7 + yW_2368 8 * rowA 4 8 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 4 8 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_4_9 :
    yW_2368 0 * rowA 4 9 0 + yW_2368 1 * rowA 4 9 1 + yW_2368 2 * rowA 4 9 2 + yW_2368 3 * rowA 4 9 3 + yW_2368 4 * rowA 4 9 4 + yW_2368 5 * rowA 4 9 5 + yW_2368 6 * rowA 4 9 6 + yW_2368 7 * rowA 4 9 7 + yW_2368 8 * rowA 4 9 8 ≤ db_2368 4 9 := by
  have hleft : yW_2368 0 * rowA 4 9 0 + yW_2368 1 * rowA 4 9 1 + yW_2368 2 * rowA 4 9 2 + yW_2368 3 * rowA 4 9 3 + yW_2368 4 * rowA 4 9 4 + yW_2368 5 * rowA 4 9 5 + yW_2368 6 * rowA 4 9 6 + yW_2368 7 * rowA 4 9 7 + yW_2368 8 * rowA 4 9 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 4 9 = (3 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_5_0 :
    yW_2368 0 * rowA 5 0 0 + yW_2368 1 * rowA 5 0 1 + yW_2368 2 * rowA 5 0 2 + yW_2368 3 * rowA 5 0 3 + yW_2368 4 * rowA 5 0 4 + yW_2368 5 * rowA 5 0 5 + yW_2368 6 * rowA 5 0 6 + yW_2368 7 * rowA 5 0 7 + yW_2368 8 * rowA 5 0 8 ≤ db_2368 5 0 := by
  have hleft : yW_2368 0 * rowA 5 0 0 + yW_2368 1 * rowA 5 0 1 + yW_2368 2 * rowA 5 0 2 + yW_2368 3 * rowA 5 0 3 + yW_2368 4 * rowA 5 0 4 + yW_2368 5 * rowA 5 0 5 + yW_2368 6 * rowA 5 0 6 + yW_2368 7 * rowA 5 0 7 + yW_2368 8 * rowA 5 0 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 5 0 = (-3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_5_1 :
    yW_2368 0 * rowA 5 1 0 + yW_2368 1 * rowA 5 1 1 + yW_2368 2 * rowA 5 1 2 + yW_2368 3 * rowA 5 1 3 + yW_2368 4 * rowA 5 1 4 + yW_2368 5 * rowA 5 1 5 + yW_2368 6 * rowA 5 1 6 + yW_2368 7 * rowA 5 1 7 + yW_2368 8 * rowA 5 1 8 ≤ db_2368 5 1 := by
  have hleft : yW_2368 0 * rowA 5 1 0 + yW_2368 1 * rowA 5 1 1 + yW_2368 2 * rowA 5 1 2 + yW_2368 3 * rowA 5 1 3 + yW_2368 4 * rowA 5 1 4 + yW_2368 5 * rowA 5 1 5 + yW_2368 6 * rowA 5 1 6 + yW_2368 7 * rowA 5 1 7 + yW_2368 8 * rowA 5 1 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 5 1 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_5_2 :
    yW_2368 0 * rowA 5 2 0 + yW_2368 1 * rowA 5 2 1 + yW_2368 2 * rowA 5 2 2 + yW_2368 3 * rowA 5 2 3 + yW_2368 4 * rowA 5 2 4 + yW_2368 5 * rowA 5 2 5 + yW_2368 6 * rowA 5 2 6 + yW_2368 7 * rowA 5 2 7 + yW_2368 8 * rowA 5 2 8 ≤ db_2368 5 2 := by
  have hleft : yW_2368 0 * rowA 5 2 0 + yW_2368 1 * rowA 5 2 1 + yW_2368 2 * rowA 5 2 2 + yW_2368 3 * rowA 5 2 3 + yW_2368 4 * rowA 5 2 4 + yW_2368 5 * rowA 5 2 5 + yW_2368 6 * rowA 5 2 6 + yW_2368 7 * rowA 5 2 7 + yW_2368 8 * rowA 5 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 5 2 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_5_3 :
    yW_2368 0 * rowA 5 3 0 + yW_2368 1 * rowA 5 3 1 + yW_2368 2 * rowA 5 3 2 + yW_2368 3 * rowA 5 3 3 + yW_2368 4 * rowA 5 3 4 + yW_2368 5 * rowA 5 3 5 + yW_2368 6 * rowA 5 3 6 + yW_2368 7 * rowA 5 3 7 + yW_2368 8 * rowA 5 3 8 ≤ db_2368 5 3 := by
  have hleft : yW_2368 0 * rowA 5 3 0 + yW_2368 1 * rowA 5 3 1 + yW_2368 2 * rowA 5 3 2 + yW_2368 3 * rowA 5 3 3 + yW_2368 4 * rowA 5 3 4 + yW_2368 5 * rowA 5 3 5 + yW_2368 6 * rowA 5 3 6 + yW_2368 7 * rowA 5 3 7 + yW_2368 8 * rowA 5 3 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 5 3 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_5_4 :
    yW_2368 0 * rowA 5 4 0 + yW_2368 1 * rowA 5 4 1 + yW_2368 2 * rowA 5 4 2 + yW_2368 3 * rowA 5 4 3 + yW_2368 4 * rowA 5 4 4 + yW_2368 5 * rowA 5 4 5 + yW_2368 6 * rowA 5 4 6 + yW_2368 7 * rowA 5 4 7 + yW_2368 8 * rowA 5 4 8 ≤ db_2368 5 4 := by
  have hleft : yW_2368 0 * rowA 5 4 0 + yW_2368 1 * rowA 5 4 1 + yW_2368 2 * rowA 5 4 2 + yW_2368 3 * rowA 5 4 3 + yW_2368 4 * rowA 5 4 4 + yW_2368 5 * rowA 5 4 5 + yW_2368 6 * rowA 5 4 6 + yW_2368 7 * rowA 5 4 7 + yW_2368 8 * rowA 5 4 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 5 4 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_5_5 :
    yW_2368 0 * rowA 5 5 0 + yW_2368 1 * rowA 5 5 1 + yW_2368 2 * rowA 5 5 2 + yW_2368 3 * rowA 5 5 3 + yW_2368 4 * rowA 5 5 4 + yW_2368 5 * rowA 5 5 5 + yW_2368 6 * rowA 5 5 6 + yW_2368 7 * rowA 5 5 7 + yW_2368 8 * rowA 5 5 8 ≤ db_2368 5 5 := by
  have hleft : yW_2368 0 * rowA 5 5 0 + yW_2368 1 * rowA 5 5 1 + yW_2368 2 * rowA 5 5 2 + yW_2368 3 * rowA 5 5 3 + yW_2368 4 * rowA 5 5 4 + yW_2368 5 * rowA 5 5 5 + yW_2368 6 * rowA 5 5 6 + yW_2368 7 * rowA 5 5 7 + yW_2368 8 * rowA 5 5 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 5 5 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_5_6 :
    yW_2368 0 * rowA 5 6 0 + yW_2368 1 * rowA 5 6 1 + yW_2368 2 * rowA 5 6 2 + yW_2368 3 * rowA 5 6 3 + yW_2368 4 * rowA 5 6 4 + yW_2368 5 * rowA 5 6 5 + yW_2368 6 * rowA 5 6 6 + yW_2368 7 * rowA 5 6 7 + yW_2368 8 * rowA 5 6 8 ≤ db_2368 5 6 := by
  have hleft : yW_2368 0 * rowA 5 6 0 + yW_2368 1 * rowA 5 6 1 + yW_2368 2 * rowA 5 6 2 + yW_2368 3 * rowA 5 6 3 + yW_2368 4 * rowA 5 6 4 + yW_2368 5 * rowA 5 6 5 + yW_2368 6 * rowA 5 6 6 + yW_2368 7 * rowA 5 6 7 + yW_2368 8 * rowA 5 6 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 5 6 = (1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_5_7 :
    yW_2368 0 * rowA 5 7 0 + yW_2368 1 * rowA 5 7 1 + yW_2368 2 * rowA 5 7 2 + yW_2368 3 * rowA 5 7 3 + yW_2368 4 * rowA 5 7 4 + yW_2368 5 * rowA 5 7 5 + yW_2368 6 * rowA 5 7 6 + yW_2368 7 * rowA 5 7 7 + yW_2368 8 * rowA 5 7 8 ≤ db_2368 5 7 := by
  have hleft : yW_2368 0 * rowA 5 7 0 + yW_2368 1 * rowA 5 7 1 + yW_2368 2 * rowA 5 7 2 + yW_2368 3 * rowA 5 7 3 + yW_2368 4 * rowA 5 7 4 + yW_2368 5 * rowA 5 7 5 + yW_2368 6 * rowA 5 7 6 + yW_2368 7 * rowA 5 7 7 + yW_2368 8 * rowA 5 7 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 5 7 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_5_8 :
    yW_2368 0 * rowA 5 8 0 + yW_2368 1 * rowA 5 8 1 + yW_2368 2 * rowA 5 8 2 + yW_2368 3 * rowA 5 8 3 + yW_2368 4 * rowA 5 8 4 + yW_2368 5 * rowA 5 8 5 + yW_2368 6 * rowA 5 8 6 + yW_2368 7 * rowA 5 8 7 + yW_2368 8 * rowA 5 8 8 ≤ db_2368 5 8 := by
  have hleft : yW_2368 0 * rowA 5 8 0 + yW_2368 1 * rowA 5 8 1 + yW_2368 2 * rowA 5 8 2 + yW_2368 3 * rowA 5 8 3 + yW_2368 4 * rowA 5 8 4 + yW_2368 5 * rowA 5 8 5 + yW_2368 6 * rowA 5 8 6 + yW_2368 7 * rowA 5 8 7 + yW_2368 8 * rowA 5 8 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 5 8 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_5_9 :
    yW_2368 0 * rowA 5 9 0 + yW_2368 1 * rowA 5 9 1 + yW_2368 2 * rowA 5 9 2 + yW_2368 3 * rowA 5 9 3 + yW_2368 4 * rowA 5 9 4 + yW_2368 5 * rowA 5 9 5 + yW_2368 6 * rowA 5 9 6 + yW_2368 7 * rowA 5 9 7 + yW_2368 8 * rowA 5 9 8 ≤ db_2368 5 9 := by
  have hleft : yW_2368 0 * rowA 5 9 0 + yW_2368 1 * rowA 5 9 1 + yW_2368 2 * rowA 5 9 2 + yW_2368 3 * rowA 5 9 3 + yW_2368 4 * rowA 5 9 4 + yW_2368 5 * rowA 5 9 5 + yW_2368 6 * rowA 5 9 6 + yW_2368 7 * rowA 5 9 7 + yW_2368 8 * rowA 5 9 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 5 9 = (5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_6_0 :
    yW_2368 0 * rowA 6 0 0 + yW_2368 1 * rowA 6 0 1 + yW_2368 2 * rowA 6 0 2 + yW_2368 3 * rowA 6 0 3 + yW_2368 4 * rowA 6 0 4 + yW_2368 5 * rowA 6 0 5 + yW_2368 6 * rowA 6 0 6 + yW_2368 7 * rowA 6 0 7 + yW_2368 8 * rowA 6 0 8 ≤ db_2368 6 0 := by
  have hleft : yW_2368 0 * rowA 6 0 0 + yW_2368 1 * rowA 6 0 1 + yW_2368 2 * rowA 6 0 2 + yW_2368 3 * rowA 6 0 3 + yW_2368 4 * rowA 6 0 4 + yW_2368 5 * rowA 6 0 5 + yW_2368 6 * rowA 6 0 6 + yW_2368 7 * rowA 6 0 7 + yW_2368 8 * rowA 6 0 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 6 0 = (-3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_6_1 :
    yW_2368 0 * rowA 6 1 0 + yW_2368 1 * rowA 6 1 1 + yW_2368 2 * rowA 6 1 2 + yW_2368 3 * rowA 6 1 3 + yW_2368 4 * rowA 6 1 4 + yW_2368 5 * rowA 6 1 5 + yW_2368 6 * rowA 6 1 6 + yW_2368 7 * rowA 6 1 7 + yW_2368 8 * rowA 6 1 8 ≤ db_2368 6 1 := by
  have hleft : yW_2368 0 * rowA 6 1 0 + yW_2368 1 * rowA 6 1 1 + yW_2368 2 * rowA 6 1 2 + yW_2368 3 * rowA 6 1 3 + yW_2368 4 * rowA 6 1 4 + yW_2368 5 * rowA 6 1 5 + yW_2368 6 * rowA 6 1 6 + yW_2368 7 * rowA 6 1 7 + yW_2368 8 * rowA 6 1 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 6 1 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_6_2 :
    yW_2368 0 * rowA 6 2 0 + yW_2368 1 * rowA 6 2 1 + yW_2368 2 * rowA 6 2 2 + yW_2368 3 * rowA 6 2 3 + yW_2368 4 * rowA 6 2 4 + yW_2368 5 * rowA 6 2 5 + yW_2368 6 * rowA 6 2 6 + yW_2368 7 * rowA 6 2 7 + yW_2368 8 * rowA 6 2 8 ≤ db_2368 6 2 := by
  have hleft : yW_2368 0 * rowA 6 2 0 + yW_2368 1 * rowA 6 2 1 + yW_2368 2 * rowA 6 2 2 + yW_2368 3 * rowA 6 2 3 + yW_2368 4 * rowA 6 2 4 + yW_2368 5 * rowA 6 2 5 + yW_2368 6 * rowA 6 2 6 + yW_2368 7 * rowA 6 2 7 + yW_2368 8 * rowA 6 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 6 2 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_6_3 :
    yW_2368 0 * rowA 6 3 0 + yW_2368 1 * rowA 6 3 1 + yW_2368 2 * rowA 6 3 2 + yW_2368 3 * rowA 6 3 3 + yW_2368 4 * rowA 6 3 4 + yW_2368 5 * rowA 6 3 5 + yW_2368 6 * rowA 6 3 6 + yW_2368 7 * rowA 6 3 7 + yW_2368 8 * rowA 6 3 8 ≤ db_2368 6 3 := by
  have hleft : yW_2368 0 * rowA 6 3 0 + yW_2368 1 * rowA 6 3 1 + yW_2368 2 * rowA 6 3 2 + yW_2368 3 * rowA 6 3 3 + yW_2368 4 * rowA 6 3 4 + yW_2368 5 * rowA 6 3 5 + yW_2368 6 * rowA 6 3 6 + yW_2368 7 * rowA 6 3 7 + yW_2368 8 * rowA 6 3 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 6 3 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_6_4 :
    yW_2368 0 * rowA 6 4 0 + yW_2368 1 * rowA 6 4 1 + yW_2368 2 * rowA 6 4 2 + yW_2368 3 * rowA 6 4 3 + yW_2368 4 * rowA 6 4 4 + yW_2368 5 * rowA 6 4 5 + yW_2368 6 * rowA 6 4 6 + yW_2368 7 * rowA 6 4 7 + yW_2368 8 * rowA 6 4 8 ≤ db_2368 6 4 := by
  have hleft : yW_2368 0 * rowA 6 4 0 + yW_2368 1 * rowA 6 4 1 + yW_2368 2 * rowA 6 4 2 + yW_2368 3 * rowA 6 4 3 + yW_2368 4 * rowA 6 4 4 + yW_2368 5 * rowA 6 4 5 + yW_2368 6 * rowA 6 4 6 + yW_2368 7 * rowA 6 4 7 + yW_2368 8 * rowA 6 4 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 6 4 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_6_5 :
    yW_2368 0 * rowA 6 5 0 + yW_2368 1 * rowA 6 5 1 + yW_2368 2 * rowA 6 5 2 + yW_2368 3 * rowA 6 5 3 + yW_2368 4 * rowA 6 5 4 + yW_2368 5 * rowA 6 5 5 + yW_2368 6 * rowA 6 5 6 + yW_2368 7 * rowA 6 5 7 + yW_2368 8 * rowA 6 5 8 ≤ db_2368 6 5 := by
  have hleft : yW_2368 0 * rowA 6 5 0 + yW_2368 1 * rowA 6 5 1 + yW_2368 2 * rowA 6 5 2 + yW_2368 3 * rowA 6 5 3 + yW_2368 4 * rowA 6 5 4 + yW_2368 5 * rowA 6 5 5 + yW_2368 6 * rowA 6 5 6 + yW_2368 7 * rowA 6 5 7 + yW_2368 8 * rowA 6 5 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 6 5 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_6_6 :
    yW_2368 0 * rowA 6 6 0 + yW_2368 1 * rowA 6 6 1 + yW_2368 2 * rowA 6 6 2 + yW_2368 3 * rowA 6 6 3 + yW_2368 4 * rowA 6 6 4 + yW_2368 5 * rowA 6 6 5 + yW_2368 6 * rowA 6 6 6 + yW_2368 7 * rowA 6 6 7 + yW_2368 8 * rowA 6 6 8 ≤ db_2368 6 6 := by
  have hleft : yW_2368 0 * rowA 6 6 0 + yW_2368 1 * rowA 6 6 1 + yW_2368 2 * rowA 6 6 2 + yW_2368 3 * rowA 6 6 3 + yW_2368 4 * rowA 6 6 4 + yW_2368 5 * rowA 6 6 5 + yW_2368 6 * rowA 6 6 6 + yW_2368 7 * rowA 6 6 7 + yW_2368 8 * rowA 6 6 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 6 6 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_6_7 :
    yW_2368 0 * rowA 6 7 0 + yW_2368 1 * rowA 6 7 1 + yW_2368 2 * rowA 6 7 2 + yW_2368 3 * rowA 6 7 3 + yW_2368 4 * rowA 6 7 4 + yW_2368 5 * rowA 6 7 5 + yW_2368 6 * rowA 6 7 6 + yW_2368 7 * rowA 6 7 7 + yW_2368 8 * rowA 6 7 8 ≤ db_2368 6 7 := by
  have hleft : yW_2368 0 * rowA 6 7 0 + yW_2368 1 * rowA 6 7 1 + yW_2368 2 * rowA 6 7 2 + yW_2368 3 * rowA 6 7 3 + yW_2368 4 * rowA 6 7 4 + yW_2368 5 * rowA 6 7 5 + yW_2368 6 * rowA 6 7 6 + yW_2368 7 * rowA 6 7 7 + yW_2368 8 * rowA 6 7 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 6 7 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_6_8 :
    yW_2368 0 * rowA 6 8 0 + yW_2368 1 * rowA 6 8 1 + yW_2368 2 * rowA 6 8 2 + yW_2368 3 * rowA 6 8 3 + yW_2368 4 * rowA 6 8 4 + yW_2368 5 * rowA 6 8 5 + yW_2368 6 * rowA 6 8 6 + yW_2368 7 * rowA 6 8 7 + yW_2368 8 * rowA 6 8 8 ≤ db_2368 6 8 := by
  have hleft : yW_2368 0 * rowA 6 8 0 + yW_2368 1 * rowA 6 8 1 + yW_2368 2 * rowA 6 8 2 + yW_2368 3 * rowA 6 8 3 + yW_2368 4 * rowA 6 8 4 + yW_2368 5 * rowA 6 8 5 + yW_2368 6 * rowA 6 8 6 + yW_2368 7 * rowA 6 8 7 + yW_2368 8 * rowA 6 8 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 6 8 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_6_9 :
    yW_2368 0 * rowA 6 9 0 + yW_2368 1 * rowA 6 9 1 + yW_2368 2 * rowA 6 9 2 + yW_2368 3 * rowA 6 9 3 + yW_2368 4 * rowA 6 9 4 + yW_2368 5 * rowA 6 9 5 + yW_2368 6 * rowA 6 9 6 + yW_2368 7 * rowA 6 9 7 + yW_2368 8 * rowA 6 9 8 ≤ db_2368 6 9 := by
  have hleft : yW_2368 0 * rowA 6 9 0 + yW_2368 1 * rowA 6 9 1 + yW_2368 2 * rowA 6 9 2 + yW_2368 3 * rowA 6 9 3 + yW_2368 4 * rowA 6 9 4 + yW_2368 5 * rowA 6 9 5 + yW_2368 6 * rowA 6 9 6 + yW_2368 7 * rowA 6 9 7 + yW_2368 8 * rowA 6 9 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 6 9 = (5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_7_0 :
    yW_2368 0 * rowA 7 0 0 + yW_2368 1 * rowA 7 0 1 + yW_2368 2 * rowA 7 0 2 + yW_2368 3 * rowA 7 0 3 + yW_2368 4 * rowA 7 0 4 + yW_2368 5 * rowA 7 0 5 + yW_2368 6 * rowA 7 0 6 + yW_2368 7 * rowA 7 0 7 + yW_2368 8 * rowA 7 0 8 ≤ db_2368 7 0 := by
  have hleft : yW_2368 0 * rowA 7 0 0 + yW_2368 1 * rowA 7 0 1 + yW_2368 2 * rowA 7 0 2 + yW_2368 3 * rowA 7 0 3 + yW_2368 4 * rowA 7 0 4 + yW_2368 5 * rowA 7 0 5 + yW_2368 6 * rowA 7 0 6 + yW_2368 7 * rowA 7 0 7 + yW_2368 8 * rowA 7 0 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 7 0 = (-1 : ℚ) / 2 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_7_1 :
    yW_2368 0 * rowA 7 1 0 + yW_2368 1 * rowA 7 1 1 + yW_2368 2 * rowA 7 1 2 + yW_2368 3 * rowA 7 1 3 + yW_2368 4 * rowA 7 1 4 + yW_2368 5 * rowA 7 1 5 + yW_2368 6 * rowA 7 1 6 + yW_2368 7 * rowA 7 1 7 + yW_2368 8 * rowA 7 1 8 ≤ db_2368 7 1 := by
  have hleft : yW_2368 0 * rowA 7 1 0 + yW_2368 1 * rowA 7 1 1 + yW_2368 2 * rowA 7 1 2 + yW_2368 3 * rowA 7 1 3 + yW_2368 4 * rowA 7 1 4 + yW_2368 5 * rowA 7 1 5 + yW_2368 6 * rowA 7 1 6 + yW_2368 7 * rowA 7 1 7 + yW_2368 8 * rowA 7 1 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 7 1 = (-1 : ℚ) / 2 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_7_2 :
    yW_2368 0 * rowA 7 2 0 + yW_2368 1 * rowA 7 2 1 + yW_2368 2 * rowA 7 2 2 + yW_2368 3 * rowA 7 2 3 + yW_2368 4 * rowA 7 2 4 + yW_2368 5 * rowA 7 2 5 + yW_2368 6 * rowA 7 2 6 + yW_2368 7 * rowA 7 2 7 + yW_2368 8 * rowA 7 2 8 ≤ db_2368 7 2 := by
  have hleft : yW_2368 0 * rowA 7 2 0 + yW_2368 1 * rowA 7 2 1 + yW_2368 2 * rowA 7 2 2 + yW_2368 3 * rowA 7 2 3 + yW_2368 4 * rowA 7 2 4 + yW_2368 5 * rowA 7 2 5 + yW_2368 6 * rowA 7 2 6 + yW_2368 7 * rowA 7 2 7 + yW_2368 8 * rowA 7 2 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 7 2 = (-1 : ℚ) / 2 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_7_3 :
    yW_2368 0 * rowA 7 3 0 + yW_2368 1 * rowA 7 3 1 + yW_2368 2 * rowA 7 3 2 + yW_2368 3 * rowA 7 3 3 + yW_2368 4 * rowA 7 3 4 + yW_2368 5 * rowA 7 3 5 + yW_2368 6 * rowA 7 3 6 + yW_2368 7 * rowA 7 3 7 + yW_2368 8 * rowA 7 3 8 ≤ db_2368 7 3 := by
  have hleft : yW_2368 0 * rowA 7 3 0 + yW_2368 1 * rowA 7 3 1 + yW_2368 2 * rowA 7 3 2 + yW_2368 3 * rowA 7 3 3 + yW_2368 4 * rowA 7 3 4 + yW_2368 5 * rowA 7 3 5 + yW_2368 6 * rowA 7 3 6 + yW_2368 7 * rowA 7 3 7 + yW_2368 8 * rowA 7 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 7 3 = (-1 : ℚ) / 2 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_7_4 :
    yW_2368 0 * rowA 7 4 0 + yW_2368 1 * rowA 7 4 1 + yW_2368 2 * rowA 7 4 2 + yW_2368 3 * rowA 7 4 3 + yW_2368 4 * rowA 7 4 4 + yW_2368 5 * rowA 7 4 5 + yW_2368 6 * rowA 7 4 6 + yW_2368 7 * rowA 7 4 7 + yW_2368 8 * rowA 7 4 8 ≤ db_2368 7 4 := by
  have hleft : yW_2368 0 * rowA 7 4 0 + yW_2368 1 * rowA 7 4 1 + yW_2368 2 * rowA 7 4 2 + yW_2368 3 * rowA 7 4 3 + yW_2368 4 * rowA 7 4 4 + yW_2368 5 * rowA 7 4 5 + yW_2368 6 * rowA 7 4 6 + yW_2368 7 * rowA 7 4 7 + yW_2368 8 * rowA 7 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 7 4 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_7_5 :
    yW_2368 0 * rowA 7 5 0 + yW_2368 1 * rowA 7 5 1 + yW_2368 2 * rowA 7 5 2 + yW_2368 3 * rowA 7 5 3 + yW_2368 4 * rowA 7 5 4 + yW_2368 5 * rowA 7 5 5 + yW_2368 6 * rowA 7 5 6 + yW_2368 7 * rowA 7 5 7 + yW_2368 8 * rowA 7 5 8 ≤ db_2368 7 5 := by
  have hleft : yW_2368 0 * rowA 7 5 0 + yW_2368 1 * rowA 7 5 1 + yW_2368 2 * rowA 7 5 2 + yW_2368 3 * rowA 7 5 3 + yW_2368 4 * rowA 7 5 4 + yW_2368 5 * rowA 7 5 5 + yW_2368 6 * rowA 7 5 6 + yW_2368 7 * rowA 7 5 7 + yW_2368 8 * rowA 7 5 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 7 5 = (-1 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_7_6 :
    yW_2368 0 * rowA 7 6 0 + yW_2368 1 * rowA 7 6 1 + yW_2368 2 * rowA 7 6 2 + yW_2368 3 * rowA 7 6 3 + yW_2368 4 * rowA 7 6 4 + yW_2368 5 * rowA 7 6 5 + yW_2368 6 * rowA 7 6 6 + yW_2368 7 * rowA 7 6 7 + yW_2368 8 * rowA 7 6 8 ≤ db_2368 7 6 := by
  have hleft : yW_2368 0 * rowA 7 6 0 + yW_2368 1 * rowA 7 6 1 + yW_2368 2 * rowA 7 6 2 + yW_2368 3 * rowA 7 6 3 + yW_2368 4 * rowA 7 6 4 + yW_2368 5 * rowA 7 6 5 + yW_2368 6 * rowA 7 6 6 + yW_2368 7 * rowA 7 6 7 + yW_2368 8 * rowA 7 6 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 7 6 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_7_7 :
    yW_2368 0 * rowA 7 7 0 + yW_2368 1 * rowA 7 7 1 + yW_2368 2 * rowA 7 7 2 + yW_2368 3 * rowA 7 7 3 + yW_2368 4 * rowA 7 7 4 + yW_2368 5 * rowA 7 7 5 + yW_2368 6 * rowA 7 7 6 + yW_2368 7 * rowA 7 7 7 + yW_2368 8 * rowA 7 7 8 ≤ db_2368 7 7 := by
  have hleft : yW_2368 0 * rowA 7 7 0 + yW_2368 1 * rowA 7 7 1 + yW_2368 2 * rowA 7 7 2 + yW_2368 3 * rowA 7 7 3 + yW_2368 4 * rowA 7 7 4 + yW_2368 5 * rowA 7 7 5 + yW_2368 6 * rowA 7 7 6 + yW_2368 7 * rowA 7 7 7 + yW_2368 8 * rowA 7 7 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 7 7 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_7_8 :
    yW_2368 0 * rowA 7 8 0 + yW_2368 1 * rowA 7 8 1 + yW_2368 2 * rowA 7 8 2 + yW_2368 3 * rowA 7 8 3 + yW_2368 4 * rowA 7 8 4 + yW_2368 5 * rowA 7 8 5 + yW_2368 6 * rowA 7 8 6 + yW_2368 7 * rowA 7 8 7 + yW_2368 8 * rowA 7 8 8 ≤ db_2368 7 8 := by
  have hleft : yW_2368 0 * rowA 7 8 0 + yW_2368 1 * rowA 7 8 1 + yW_2368 2 * rowA 7 8 2 + yW_2368 3 * rowA 7 8 3 + yW_2368 4 * rowA 7 8 4 + yW_2368 5 * rowA 7 8 5 + yW_2368 6 * rowA 7 8 6 + yW_2368 7 * rowA 7 8 7 + yW_2368 8 * rowA 7 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 7 8 = (1 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_7_9 :
    yW_2368 0 * rowA 7 9 0 + yW_2368 1 * rowA 7 9 1 + yW_2368 2 * rowA 7 9 2 + yW_2368 3 * rowA 7 9 3 + yW_2368 4 * rowA 7 9 4 + yW_2368 5 * rowA 7 9 5 + yW_2368 6 * rowA 7 9 6 + yW_2368 7 * rowA 7 9 7 + yW_2368 8 * rowA 7 9 8 ≤ db_2368 7 9 := by
  have hleft : yW_2368 0 * rowA 7 9 0 + yW_2368 1 * rowA 7 9 1 + yW_2368 2 * rowA 7 9 2 + yW_2368 3 * rowA 7 9 3 + yW_2368 4 * rowA 7 9 4 + yW_2368 5 * rowA 7 9 5 + yW_2368 6 * rowA 7 9 6 + yW_2368 7 * rowA 7 9 7 + yW_2368 8 * rowA 7 9 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 7 9 = (1 : ℚ) / 2 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_8_0 :
    yW_2368 0 * rowA 8 0 0 + yW_2368 1 * rowA 8 0 1 + yW_2368 2 * rowA 8 0 2 + yW_2368 3 * rowA 8 0 3 + yW_2368 4 * rowA 8 0 4 + yW_2368 5 * rowA 8 0 5 + yW_2368 6 * rowA 8 0 6 + yW_2368 7 * rowA 8 0 7 + yW_2368 8 * rowA 8 0 8 ≤ db_2368 8 0 := by
  have hleft : yW_2368 0 * rowA 8 0 0 + yW_2368 1 * rowA 8 0 1 + yW_2368 2 * rowA 8 0 2 + yW_2368 3 * rowA 8 0 3 + yW_2368 4 * rowA 8 0 4 + yW_2368 5 * rowA 8 0 5 + yW_2368 6 * rowA 8 0 6 + yW_2368 7 * rowA 8 0 7 + yW_2368 8 * rowA 8 0 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 8 0 = (-5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_8_1 :
    yW_2368 0 * rowA 8 1 0 + yW_2368 1 * rowA 8 1 1 + yW_2368 2 * rowA 8 1 2 + yW_2368 3 * rowA 8 1 3 + yW_2368 4 * rowA 8 1 4 + yW_2368 5 * rowA 8 1 5 + yW_2368 6 * rowA 8 1 6 + yW_2368 7 * rowA 8 1 7 + yW_2368 8 * rowA 8 1 8 ≤ db_2368 8 1 := by
  have hleft : yW_2368 0 * rowA 8 1 0 + yW_2368 1 * rowA 8 1 1 + yW_2368 2 * rowA 8 1 2 + yW_2368 3 * rowA 8 1 3 + yW_2368 4 * rowA 8 1 4 + yW_2368 5 * rowA 8 1 5 + yW_2368 6 * rowA 8 1 6 + yW_2368 7 * rowA 8 1 7 + yW_2368 8 * rowA 8 1 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 8 1 = (-5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_8_2 :
    yW_2368 0 * rowA 8 2 0 + yW_2368 1 * rowA 8 2 1 + yW_2368 2 * rowA 8 2 2 + yW_2368 3 * rowA 8 2 3 + yW_2368 4 * rowA 8 2 4 + yW_2368 5 * rowA 8 2 5 + yW_2368 6 * rowA 8 2 6 + yW_2368 7 * rowA 8 2 7 + yW_2368 8 * rowA 8 2 8 ≤ db_2368 8 2 := by
  have hleft : yW_2368 0 * rowA 8 2 0 + yW_2368 1 * rowA 8 2 1 + yW_2368 2 * rowA 8 2 2 + yW_2368 3 * rowA 8 2 3 + yW_2368 4 * rowA 8 2 4 + yW_2368 5 * rowA 8 2 5 + yW_2368 6 * rowA 8 2 6 + yW_2368 7 * rowA 8 2 7 + yW_2368 8 * rowA 8 2 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 8 2 = (-5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_8_3 :
    yW_2368 0 * rowA 8 3 0 + yW_2368 1 * rowA 8 3 1 + yW_2368 2 * rowA 8 3 2 + yW_2368 3 * rowA 8 3 3 + yW_2368 4 * rowA 8 3 4 + yW_2368 5 * rowA 8 3 5 + yW_2368 6 * rowA 8 3 6 + yW_2368 7 * rowA 8 3 7 + yW_2368 8 * rowA 8 3 8 ≤ db_2368 8 3 := by
  have hleft : yW_2368 0 * rowA 8 3 0 + yW_2368 1 * rowA 8 3 1 + yW_2368 2 * rowA 8 3 2 + yW_2368 3 * rowA 8 3 3 + yW_2368 4 * rowA 8 3 4 + yW_2368 5 * rowA 8 3 5 + yW_2368 6 * rowA 8 3 6 + yW_2368 7 * rowA 8 3 7 + yW_2368 8 * rowA 8 3 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 8 3 = (-5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_8_4 :
    yW_2368 0 * rowA 8 4 0 + yW_2368 1 * rowA 8 4 1 + yW_2368 2 * rowA 8 4 2 + yW_2368 3 * rowA 8 4 3 + yW_2368 4 * rowA 8 4 4 + yW_2368 5 * rowA 8 4 5 + yW_2368 6 * rowA 8 4 6 + yW_2368 7 * rowA 8 4 7 + yW_2368 8 * rowA 8 4 8 ≤ db_2368 8 4 := by
  have hleft : yW_2368 0 * rowA 8 4 0 + yW_2368 1 * rowA 8 4 1 + yW_2368 2 * rowA 8 4 2 + yW_2368 3 * rowA 8 4 3 + yW_2368 4 * rowA 8 4 4 + yW_2368 5 * rowA 8 4 5 + yW_2368 6 * rowA 8 4 6 + yW_2368 7 * rowA 8 4 7 + yW_2368 8 * rowA 8 4 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 8 4 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_8_5 :
    yW_2368 0 * rowA 8 5 0 + yW_2368 1 * rowA 8 5 1 + yW_2368 2 * rowA 8 5 2 + yW_2368 3 * rowA 8 5 3 + yW_2368 4 * rowA 8 5 4 + yW_2368 5 * rowA 8 5 5 + yW_2368 6 * rowA 8 5 6 + yW_2368 7 * rowA 8 5 7 + yW_2368 8 * rowA 8 5 8 ≤ db_2368 8 5 := by
  have hleft : yW_2368 0 * rowA 8 5 0 + yW_2368 1 * rowA 8 5 1 + yW_2368 2 * rowA 8 5 2 + yW_2368 3 * rowA 8 5 3 + yW_2368 4 * rowA 8 5 4 + yW_2368 5 * rowA 8 5 5 + yW_2368 6 * rowA 8 5 6 + yW_2368 7 * rowA 8 5 7 + yW_2368 8 * rowA 8 5 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 8 5 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_8_6 :
    yW_2368 0 * rowA 8 6 0 + yW_2368 1 * rowA 8 6 1 + yW_2368 2 * rowA 8 6 2 + yW_2368 3 * rowA 8 6 3 + yW_2368 4 * rowA 8 6 4 + yW_2368 5 * rowA 8 6 5 + yW_2368 6 * rowA 8 6 6 + yW_2368 7 * rowA 8 6 7 + yW_2368 8 * rowA 8 6 8 ≤ db_2368 8 6 := by
  have hleft : yW_2368 0 * rowA 8 6 0 + yW_2368 1 * rowA 8 6 1 + yW_2368 2 * rowA 8 6 2 + yW_2368 3 * rowA 8 6 3 + yW_2368 4 * rowA 8 6 4 + yW_2368 5 * rowA 8 6 5 + yW_2368 6 * rowA 8 6 6 + yW_2368 7 * rowA 8 6 7 + yW_2368 8 * rowA 8 6 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 8 6 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_8_7 :
    yW_2368 0 * rowA 8 7 0 + yW_2368 1 * rowA 8 7 1 + yW_2368 2 * rowA 8 7 2 + yW_2368 3 * rowA 8 7 3 + yW_2368 4 * rowA 8 7 4 + yW_2368 5 * rowA 8 7 5 + yW_2368 6 * rowA 8 7 6 + yW_2368 7 * rowA 8 7 7 + yW_2368 8 * rowA 8 7 8 ≤ db_2368 8 7 := by
  have hleft : yW_2368 0 * rowA 8 7 0 + yW_2368 1 * rowA 8 7 1 + yW_2368 2 * rowA 8 7 2 + yW_2368 3 * rowA 8 7 3 + yW_2368 4 * rowA 8 7 4 + yW_2368 5 * rowA 8 7 5 + yW_2368 6 * rowA 8 7 6 + yW_2368 7 * rowA 8 7 7 + yW_2368 8 * rowA 8 7 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 8 7 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_8_8 :
    yW_2368 0 * rowA 8 8 0 + yW_2368 1 * rowA 8 8 1 + yW_2368 2 * rowA 8 8 2 + yW_2368 3 * rowA 8 8 3 + yW_2368 4 * rowA 8 8 4 + yW_2368 5 * rowA 8 8 5 + yW_2368 6 * rowA 8 8 6 + yW_2368 7 * rowA 8 8 7 + yW_2368 8 * rowA 8 8 8 ≤ db_2368 8 8 := by
  have hleft : yW_2368 0 * rowA 8 8 0 + yW_2368 1 * rowA 8 8 1 + yW_2368 2 * rowA 8 8 2 + yW_2368 3 * rowA 8 8 3 + yW_2368 4 * rowA 8 8 4 + yW_2368 5 * rowA 8 8 5 + yW_2368 6 * rowA 8 8 6 + yW_2368 7 * rowA 8 8 7 + yW_2368 8 * rowA 8 8 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 8 8 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_8_9 :
    yW_2368 0 * rowA 8 9 0 + yW_2368 1 * rowA 8 9 1 + yW_2368 2 * rowA 8 9 2 + yW_2368 3 * rowA 8 9 3 + yW_2368 4 * rowA 8 9 4 + yW_2368 5 * rowA 8 9 5 + yW_2368 6 * rowA 8 9 6 + yW_2368 7 * rowA 8 9 7 + yW_2368 8 * rowA 8 9 8 ≤ db_2368 8 9 := by
  have hleft : yW_2368 0 * rowA 8 9 0 + yW_2368 1 * rowA 8 9 1 + yW_2368 2 * rowA 8 9 2 + yW_2368 3 * rowA 8 9 3 + yW_2368 4 * rowA 8 9 4 + yW_2368 5 * rowA 8 9 5 + yW_2368 6 * rowA 8 9 6 + yW_2368 7 * rowA 8 9 7 + yW_2368 8 * rowA 8 9 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 8 9 = (3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_9_0 :
    yW_2368 0 * rowA 9 0 0 + yW_2368 1 * rowA 9 0 1 + yW_2368 2 * rowA 9 0 2 + yW_2368 3 * rowA 9 0 3 + yW_2368 4 * rowA 9 0 4 + yW_2368 5 * rowA 9 0 5 + yW_2368 6 * rowA 9 0 6 + yW_2368 7 * rowA 9 0 7 + yW_2368 8 * rowA 9 0 8 ≤ db_2368 9 0 := by
  have hleft : yW_2368 0 * rowA 9 0 0 + yW_2368 1 * rowA 9 0 1 + yW_2368 2 * rowA 9 0 2 + yW_2368 3 * rowA 9 0 3 + yW_2368 4 * rowA 9 0 4 + yW_2368 5 * rowA 9 0 5 + yW_2368 6 * rowA 9 0 6 + yW_2368 7 * rowA 9 0 7 + yW_2368 8 * rowA 9 0 8 = (-1 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 9 0 = (-1 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_9_1 :
    yW_2368 0 * rowA 9 1 0 + yW_2368 1 * rowA 9 1 1 + yW_2368 2 * rowA 9 1 2 + yW_2368 3 * rowA 9 1 3 + yW_2368 4 * rowA 9 1 4 + yW_2368 5 * rowA 9 1 5 + yW_2368 6 * rowA 9 1 6 + yW_2368 7 * rowA 9 1 7 + yW_2368 8 * rowA 9 1 8 ≤ db_2368 9 1 := by
  have hleft : yW_2368 0 * rowA 9 1 0 + yW_2368 1 * rowA 9 1 1 + yW_2368 2 * rowA 9 1 2 + yW_2368 3 * rowA 9 1 3 + yW_2368 4 * rowA 9 1 4 + yW_2368 5 * rowA 9 1 5 + yW_2368 6 * rowA 9 1 6 + yW_2368 7 * rowA 9 1 7 + yW_2368 8 * rowA 9 1 8 = (-1 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 9 1 = (-7 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_9_2 :
    yW_2368 0 * rowA 9 2 0 + yW_2368 1 * rowA 9 2 1 + yW_2368 2 * rowA 9 2 2 + yW_2368 3 * rowA 9 2 3 + yW_2368 4 * rowA 9 2 4 + yW_2368 5 * rowA 9 2 5 + yW_2368 6 * rowA 9 2 6 + yW_2368 7 * rowA 9 2 7 + yW_2368 8 * rowA 9 2 8 ≤ db_2368 9 2 := by
  have hleft : yW_2368 0 * rowA 9 2 0 + yW_2368 1 * rowA 9 2 1 + yW_2368 2 * rowA 9 2 2 + yW_2368 3 * rowA 9 2 3 + yW_2368 4 * rowA 9 2 4 + yW_2368 5 * rowA 9 2 5 + yW_2368 6 * rowA 9 2 6 + yW_2368 7 * rowA 9 2 7 + yW_2368 8 * rowA 9 2 8 = (-1 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 9 2 = (-7 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_9_3 :
    yW_2368 0 * rowA 9 3 0 + yW_2368 1 * rowA 9 3 1 + yW_2368 2 * rowA 9 3 2 + yW_2368 3 * rowA 9 3 3 + yW_2368 4 * rowA 9 3 4 + yW_2368 5 * rowA 9 3 5 + yW_2368 6 * rowA 9 3 6 + yW_2368 7 * rowA 9 3 7 + yW_2368 8 * rowA 9 3 8 ≤ db_2368 9 3 := by
  have hleft : yW_2368 0 * rowA 9 3 0 + yW_2368 1 * rowA 9 3 1 + yW_2368 2 * rowA 9 3 2 + yW_2368 3 * rowA 9 3 3 + yW_2368 4 * rowA 9 3 4 + yW_2368 5 * rowA 9 3 5 + yW_2368 6 * rowA 9 3 6 + yW_2368 7 * rowA 9 3 7 + yW_2368 8 * rowA 9 3 8 = (-7 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 9 3 = (-7 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_9_4 :
    yW_2368 0 * rowA 9 4 0 + yW_2368 1 * rowA 9 4 1 + yW_2368 2 * rowA 9 4 2 + yW_2368 3 * rowA 9 4 3 + yW_2368 4 * rowA 9 4 4 + yW_2368 5 * rowA 9 4 5 + yW_2368 6 * rowA 9 4 6 + yW_2368 7 * rowA 9 4 7 + yW_2368 8 * rowA 9 4 8 ≤ db_2368 9 4 := by
  have hleft : yW_2368 0 * rowA 9 4 0 + yW_2368 1 * rowA 9 4 1 + yW_2368 2 * rowA 9 4 2 + yW_2368 3 * rowA 9 4 3 + yW_2368 4 * rowA 9 4 4 + yW_2368 5 * rowA 9 4 5 + yW_2368 6 * rowA 9 4 6 + yW_2368 7 * rowA 9 4 7 + yW_2368 8 * rowA 9 4 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 9 4 = (-5 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_9_5 :
    yW_2368 0 * rowA 9 5 0 + yW_2368 1 * rowA 9 5 1 + yW_2368 2 * rowA 9 5 2 + yW_2368 3 * rowA 9 5 3 + yW_2368 4 * rowA 9 5 4 + yW_2368 5 * rowA 9 5 5 + yW_2368 6 * rowA 9 5 6 + yW_2368 7 * rowA 9 5 7 + yW_2368 8 * rowA 9 5 8 ≤ db_2368 9 5 := by
  have hleft : yW_2368 0 * rowA 9 5 0 + yW_2368 1 * rowA 9 5 1 + yW_2368 2 * rowA 9 5 2 + yW_2368 3 * rowA 9 5 3 + yW_2368 4 * rowA 9 5 4 + yW_2368 5 * rowA 9 5 5 + yW_2368 6 * rowA 9 5 6 + yW_2368 7 * rowA 9 5 7 + yW_2368 8 * rowA 9 5 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 9 5 = (-1 : ℚ) / 2 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_9_6 :
    yW_2368 0 * rowA 9 6 0 + yW_2368 1 * rowA 9 6 1 + yW_2368 2 * rowA 9 6 2 + yW_2368 3 * rowA 9 6 3 + yW_2368 4 * rowA 9 6 4 + yW_2368 5 * rowA 9 6 5 + yW_2368 6 * rowA 9 6 6 + yW_2368 7 * rowA 9 6 7 + yW_2368 8 * rowA 9 6 8 ≤ db_2368 9 6 := by
  have hleft : yW_2368 0 * rowA 9 6 0 + yW_2368 1 * rowA 9 6 1 + yW_2368 2 * rowA 9 6 2 + yW_2368 3 * rowA 9 6 3 + yW_2368 4 * rowA 9 6 4 + yW_2368 5 * rowA 9 6 5 + yW_2368 6 * rowA 9 6 6 + yW_2368 7 * rowA 9 6 7 + yW_2368 8 * rowA 9 6 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 9 6 = (-3 : ℚ) / 8 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_9_7 :
    yW_2368 0 * rowA 9 7 0 + yW_2368 1 * rowA 9 7 1 + yW_2368 2 * rowA 9 7 2 + yW_2368 3 * rowA 9 7 3 + yW_2368 4 * rowA 9 7 4 + yW_2368 5 * rowA 9 7 5 + yW_2368 6 * rowA 9 7 6 + yW_2368 7 * rowA 9 7 7 + yW_2368 8 * rowA 9 7 8 ≤ db_2368 9 7 := by
  have hleft : yW_2368 0 * rowA 9 7 0 + yW_2368 1 * rowA 9 7 1 + yW_2368 2 * rowA 9 7 2 + yW_2368 3 * rowA 9 7 3 + yW_2368 4 * rowA 9 7 4 + yW_2368 5 * rowA 9 7 5 + yW_2368 6 * rowA 9 7 6 + yW_2368 7 * rowA 9 7 7 + yW_2368 8 * rowA 9 7 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 9 7 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_9_8 :
    yW_2368 0 * rowA 9 8 0 + yW_2368 1 * rowA 9 8 1 + yW_2368 2 * rowA 9 8 2 + yW_2368 3 * rowA 9 8 3 + yW_2368 4 * rowA 9 8 4 + yW_2368 5 * rowA 9 8 5 + yW_2368 6 * rowA 9 8 6 + yW_2368 7 * rowA 9 8 7 + yW_2368 8 * rowA 9 8 8 ≤ db_2368 9 8 := by
  have hleft : yW_2368 0 * rowA 9 8 0 + yW_2368 1 * rowA 9 8 1 + yW_2368 2 * rowA 9 8 2 + yW_2368 3 * rowA 9 8 3 + yW_2368 4 * rowA 9 8 4 + yW_2368 5 * rowA 9 8 5 + yW_2368 6 * rowA 9 8 6 + yW_2368 7 * rowA 9 8 7 + yW_2368 8 * rowA 9 8 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 9 8 = (-1 : ℚ) / 4 := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_9_9 :
    yW_2368 0 * rowA 9 9 0 + yW_2368 1 * rowA 9 9 1 + yW_2368 2 * rowA 9 9 2 + yW_2368 3 * rowA 9 9 3 + yW_2368 4 * rowA 9 9 4 + yW_2368 5 * rowA 9 9 5 + yW_2368 6 * rowA 9 9 6 + yW_2368 7 * rowA 9 9 7 + yW_2368 8 * rowA 9 9 8 ≤ db_2368 9 9 := by
  have hleft : yW_2368 0 * rowA 9 9 0 + yW_2368 1 * rowA 9 9 1 + yW_2368 2 * rowA 9 9 2 + yW_2368 3 * rowA 9 9 3 + yW_2368 4 * rowA 9 9 4 + yW_2368 5 * rowA 9 9 5 + yW_2368 6 * rowA 9 9 6 + yW_2368 7 * rowA 9 9 7 + yW_2368 8 * rowA 9 9 8 = (0 : ℚ) := by
    norm_num [yW_2368, rowA]
  have hright : db_2368 9 9 = (0 : ℚ) := by
    norm_num [db_2368, dbmVal_2368]
  rw [hleft, hright]
  norm_num

theorem row_cap_2368_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 0 j q) ≤ db_2368 0 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_0_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_0_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_0_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_0_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_0_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_0_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_0_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_0_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_0_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_0_9

theorem row_cap_2368_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 1 j q) ≤ db_2368 1 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_1_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_1_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_1_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_1_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_1_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_1_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_1_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_1_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_1_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_1_9

theorem row_cap_2368_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 2 j q) ≤ db_2368 2 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_2_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_2_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_2_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_2_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_2_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_2_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_2_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_2_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_2_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_2_9

theorem row_cap_2368_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 3 j q) ≤ db_2368 3 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_3_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_3_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_3_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_3_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_3_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_3_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_3_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_3_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_3_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_3_9

theorem row_cap_2368_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 4 j q) ≤ db_2368 4 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_4_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_4_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_4_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_4_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_4_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_4_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_4_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_4_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_4_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_4_9

theorem row_cap_2368_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 5 j q) ≤ db_2368 5 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_5_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_5_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_5_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_5_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_5_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_5_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_5_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_5_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_5_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_5_9

theorem row_cap_2368_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 6 j q) ≤ db_2368 6 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_6_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_6_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_6_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_6_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_6_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_6_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_6_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_6_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_6_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_6_9

theorem row_cap_2368_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 7 j q) ≤ db_2368 7 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_7_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_7_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_7_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_7_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_7_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_7_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_7_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_7_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_7_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_7_9

theorem row_cap_2368_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 8 j q) ≤ db_2368 8 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_8_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_8_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_8_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_8_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_8_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_8_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_8_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_8_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_8_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_8_9

theorem row_cap_2368_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 9 j q) ≤ db_2368 9 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_9_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_9_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_9_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_9_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_9_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_9_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_9_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_9_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_9_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2368_9_9

theorem row_cap_2368 (i j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA i j q) ≤ db_2368 i j := by
  fin_cases i
  · exact row_cap_2368_0 j
  · exact row_cap_2368_1 j
  · exact row_cap_2368_2 j
  · exact row_cap_2368_3 j
  · exact row_cap_2368_4 j
  · exact row_cap_2368_5 j
  · exact row_cap_2368_6 j
  · exact row_cap_2368_7 j
  · exact row_cap_2368_8 j
  · exact row_cap_2368_9 j

def dbmVal_2370 : Fin 10 → Fin 10 → ℤ
  | i, j => ![
      ![0, 1024, 1024, 1024, 1536, 2048, 2560, 3584, 3584, 4096],
      ![0, 0, 1024, 1024, 1536, 2048, 2560, 3584, 3584, 4096],
      ![0, 0, 0, 1024, 1536, 2048, 2560, 3584, 3584, 4096],
      ![0, 0, 0, 0, 1024, 1536, 2560, 2560, 2560, 4096],
      ![-1024, 0, 0, 0, 0, 1024, 1536, 2048, 2048, 3072],
      ![-1024, 0, 0, 0, 0, 0, 1536, 2048, 2048, 3072],
      ![-1280, -1280, -1280, -1280, -256, 0, 0, 1280, 1280, 2816],
      ![-2048, -2048, -2048, -2048, -1024, -512, 0, 0, 512, 2048],
      ![-2560, -2048, -2048, -2048, -1536, -1024, 0, 0, 0, 1536],
      ![-4096, -3072, -3072, -3072, -2560, -2048, -1536, -512, -512, 0]
    ] i j

def db_2370 (i j : Fin 10) : ℚ := (dbmVal_2370 i j : ℚ) / 4096

theorem row_cap_2370_0_0 :
    yW_2370 0 * rowA 0 0 0 + yW_2370 1 * rowA 0 0 1 + yW_2370 2 * rowA 0 0 2 + yW_2370 3 * rowA 0 0 3 + yW_2370 4 * rowA 0 0 4 + yW_2370 5 * rowA 0 0 5 + yW_2370 6 * rowA 0 0 6 + yW_2370 7 * rowA 0 0 7 + yW_2370 8 * rowA 0 0 8 ≤ db_2370 0 0 := by
  have hleft : yW_2370 0 * rowA 0 0 0 + yW_2370 1 * rowA 0 0 1 + yW_2370 2 * rowA 0 0 2 + yW_2370 3 * rowA 0 0 3 + yW_2370 4 * rowA 0 0 4 + yW_2370 5 * rowA 0 0 5 + yW_2370 6 * rowA 0 0 6 + yW_2370 7 * rowA 0 0 7 + yW_2370 8 * rowA 0 0 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 0 0 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_0_1 :
    yW_2370 0 * rowA 0 1 0 + yW_2370 1 * rowA 0 1 1 + yW_2370 2 * rowA 0 1 2 + yW_2370 3 * rowA 0 1 3 + yW_2370 4 * rowA 0 1 4 + yW_2370 5 * rowA 0 1 5 + yW_2370 6 * rowA 0 1 6 + yW_2370 7 * rowA 0 1 7 + yW_2370 8 * rowA 0 1 8 ≤ db_2370 0 1 := by
  have hleft : yW_2370 0 * rowA 0 1 0 + yW_2370 1 * rowA 0 1 1 + yW_2370 2 * rowA 0 1 2 + yW_2370 3 * rowA 0 1 3 + yW_2370 4 * rowA 0 1 4 + yW_2370 5 * rowA 0 1 5 + yW_2370 6 * rowA 0 1 6 + yW_2370 7 * rowA 0 1 7 + yW_2370 8 * rowA 0 1 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 0 1 = (1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_0_2 :
    yW_2370 0 * rowA 0 2 0 + yW_2370 1 * rowA 0 2 1 + yW_2370 2 * rowA 0 2 2 + yW_2370 3 * rowA 0 2 3 + yW_2370 4 * rowA 0 2 4 + yW_2370 5 * rowA 0 2 5 + yW_2370 6 * rowA 0 2 6 + yW_2370 7 * rowA 0 2 7 + yW_2370 8 * rowA 0 2 8 ≤ db_2370 0 2 := by
  have hleft : yW_2370 0 * rowA 0 2 0 + yW_2370 1 * rowA 0 2 1 + yW_2370 2 * rowA 0 2 2 + yW_2370 3 * rowA 0 2 3 + yW_2370 4 * rowA 0 2 4 + yW_2370 5 * rowA 0 2 5 + yW_2370 6 * rowA 0 2 6 + yW_2370 7 * rowA 0 2 7 + yW_2370 8 * rowA 0 2 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 0 2 = (1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_0_3 :
    yW_2370 0 * rowA 0 3 0 + yW_2370 1 * rowA 0 3 1 + yW_2370 2 * rowA 0 3 2 + yW_2370 3 * rowA 0 3 3 + yW_2370 4 * rowA 0 3 4 + yW_2370 5 * rowA 0 3 5 + yW_2370 6 * rowA 0 3 6 + yW_2370 7 * rowA 0 3 7 + yW_2370 8 * rowA 0 3 8 ≤ db_2370 0 3 := by
  have hleft : yW_2370 0 * rowA 0 3 0 + yW_2370 1 * rowA 0 3 1 + yW_2370 2 * rowA 0 3 2 + yW_2370 3 * rowA 0 3 3 + yW_2370 4 * rowA 0 3 4 + yW_2370 5 * rowA 0 3 5 + yW_2370 6 * rowA 0 3 6 + yW_2370 7 * rowA 0 3 7 + yW_2370 8 * rowA 0 3 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 0 3 = (1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_0_4 :
    yW_2370 0 * rowA 0 4 0 + yW_2370 1 * rowA 0 4 1 + yW_2370 2 * rowA 0 4 2 + yW_2370 3 * rowA 0 4 3 + yW_2370 4 * rowA 0 4 4 + yW_2370 5 * rowA 0 4 5 + yW_2370 6 * rowA 0 4 6 + yW_2370 7 * rowA 0 4 7 + yW_2370 8 * rowA 0 4 8 ≤ db_2370 0 4 := by
  have hleft : yW_2370 0 * rowA 0 4 0 + yW_2370 1 * rowA 0 4 1 + yW_2370 2 * rowA 0 4 2 + yW_2370 3 * rowA 0 4 3 + yW_2370 4 * rowA 0 4 4 + yW_2370 5 * rowA 0 4 5 + yW_2370 6 * rowA 0 4 6 + yW_2370 7 * rowA 0 4 7 + yW_2370 8 * rowA 0 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 0 4 = (3 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_0_5 :
    yW_2370 0 * rowA 0 5 0 + yW_2370 1 * rowA 0 5 1 + yW_2370 2 * rowA 0 5 2 + yW_2370 3 * rowA 0 5 3 + yW_2370 4 * rowA 0 5 4 + yW_2370 5 * rowA 0 5 5 + yW_2370 6 * rowA 0 5 6 + yW_2370 7 * rowA 0 5 7 + yW_2370 8 * rowA 0 5 8 ≤ db_2370 0 5 := by
  have hleft : yW_2370 0 * rowA 0 5 0 + yW_2370 1 * rowA 0 5 1 + yW_2370 2 * rowA 0 5 2 + yW_2370 3 * rowA 0 5 3 + yW_2370 4 * rowA 0 5 4 + yW_2370 5 * rowA 0 5 5 + yW_2370 6 * rowA 0 5 6 + yW_2370 7 * rowA 0 5 7 + yW_2370 8 * rowA 0 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 0 5 = (1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_0_6 :
    yW_2370 0 * rowA 0 6 0 + yW_2370 1 * rowA 0 6 1 + yW_2370 2 * rowA 0 6 2 + yW_2370 3 * rowA 0 6 3 + yW_2370 4 * rowA 0 6 4 + yW_2370 5 * rowA 0 6 5 + yW_2370 6 * rowA 0 6 6 + yW_2370 7 * rowA 0 6 7 + yW_2370 8 * rowA 0 6 8 ≤ db_2370 0 6 := by
  have hleft : yW_2370 0 * rowA 0 6 0 + yW_2370 1 * rowA 0 6 1 + yW_2370 2 * rowA 0 6 2 + yW_2370 3 * rowA 0 6 3 + yW_2370 4 * rowA 0 6 4 + yW_2370 5 * rowA 0 6 5 + yW_2370 6 * rowA 0 6 6 + yW_2370 7 * rowA 0 6 7 + yW_2370 8 * rowA 0 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 0 6 = (5 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_0_7 :
    yW_2370 0 * rowA 0 7 0 + yW_2370 1 * rowA 0 7 1 + yW_2370 2 * rowA 0 7 2 + yW_2370 3 * rowA 0 7 3 + yW_2370 4 * rowA 0 7 4 + yW_2370 5 * rowA 0 7 5 + yW_2370 6 * rowA 0 7 6 + yW_2370 7 * rowA 0 7 7 + yW_2370 8 * rowA 0 7 8 ≤ db_2370 0 7 := by
  have hleft : yW_2370 0 * rowA 0 7 0 + yW_2370 1 * rowA 0 7 1 + yW_2370 2 * rowA 0 7 2 + yW_2370 3 * rowA 0 7 3 + yW_2370 4 * rowA 0 7 4 + yW_2370 5 * rowA 0 7 5 + yW_2370 6 * rowA 0 7 6 + yW_2370 7 * rowA 0 7 7 + yW_2370 8 * rowA 0 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 0 7 = (7 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_0_8 :
    yW_2370 0 * rowA 0 8 0 + yW_2370 1 * rowA 0 8 1 + yW_2370 2 * rowA 0 8 2 + yW_2370 3 * rowA 0 8 3 + yW_2370 4 * rowA 0 8 4 + yW_2370 5 * rowA 0 8 5 + yW_2370 6 * rowA 0 8 6 + yW_2370 7 * rowA 0 8 7 + yW_2370 8 * rowA 0 8 8 ≤ db_2370 0 8 := by
  have hleft : yW_2370 0 * rowA 0 8 0 + yW_2370 1 * rowA 0 8 1 + yW_2370 2 * rowA 0 8 2 + yW_2370 3 * rowA 0 8 3 + yW_2370 4 * rowA 0 8 4 + yW_2370 5 * rowA 0 8 5 + yW_2370 6 * rowA 0 8 6 + yW_2370 7 * rowA 0 8 7 + yW_2370 8 * rowA 0 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 0 8 = (7 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_0_9 :
    yW_2370 0 * rowA 0 9 0 + yW_2370 1 * rowA 0 9 1 + yW_2370 2 * rowA 0 9 2 + yW_2370 3 * rowA 0 9 3 + yW_2370 4 * rowA 0 9 4 + yW_2370 5 * rowA 0 9 5 + yW_2370 6 * rowA 0 9 6 + yW_2370 7 * rowA 0 9 7 + yW_2370 8 * rowA 0 9 8 ≤ db_2370 0 9 := by
  have hleft : yW_2370 0 * rowA 0 9 0 + yW_2370 1 * rowA 0 9 1 + yW_2370 2 * rowA 0 9 2 + yW_2370 3 * rowA 0 9 3 + yW_2370 4 * rowA 0 9 4 + yW_2370 5 * rowA 0 9 5 + yW_2370 6 * rowA 0 9 6 + yW_2370 7 * rowA 0 9 7 + yW_2370 8 * rowA 0 9 8 = (1 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 0 9 = (1 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_1_0 :
    yW_2370 0 * rowA 1 0 0 + yW_2370 1 * rowA 1 0 1 + yW_2370 2 * rowA 1 0 2 + yW_2370 3 * rowA 1 0 3 + yW_2370 4 * rowA 1 0 4 + yW_2370 5 * rowA 1 0 5 + yW_2370 6 * rowA 1 0 6 + yW_2370 7 * rowA 1 0 7 + yW_2370 8 * rowA 1 0 8 ≤ db_2370 1 0 := by
  have hleft : yW_2370 0 * rowA 1 0 0 + yW_2370 1 * rowA 1 0 1 + yW_2370 2 * rowA 1 0 2 + yW_2370 3 * rowA 1 0 3 + yW_2370 4 * rowA 1 0 4 + yW_2370 5 * rowA 1 0 5 + yW_2370 6 * rowA 1 0 6 + yW_2370 7 * rowA 1 0 7 + yW_2370 8 * rowA 1 0 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 1 0 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_1_1 :
    yW_2370 0 * rowA 1 1 0 + yW_2370 1 * rowA 1 1 1 + yW_2370 2 * rowA 1 1 2 + yW_2370 3 * rowA 1 1 3 + yW_2370 4 * rowA 1 1 4 + yW_2370 5 * rowA 1 1 5 + yW_2370 6 * rowA 1 1 6 + yW_2370 7 * rowA 1 1 7 + yW_2370 8 * rowA 1 1 8 ≤ db_2370 1 1 := by
  have hleft : yW_2370 0 * rowA 1 1 0 + yW_2370 1 * rowA 1 1 1 + yW_2370 2 * rowA 1 1 2 + yW_2370 3 * rowA 1 1 3 + yW_2370 4 * rowA 1 1 4 + yW_2370 5 * rowA 1 1 5 + yW_2370 6 * rowA 1 1 6 + yW_2370 7 * rowA 1 1 7 + yW_2370 8 * rowA 1 1 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 1 1 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_1_2 :
    yW_2370 0 * rowA 1 2 0 + yW_2370 1 * rowA 1 2 1 + yW_2370 2 * rowA 1 2 2 + yW_2370 3 * rowA 1 2 3 + yW_2370 4 * rowA 1 2 4 + yW_2370 5 * rowA 1 2 5 + yW_2370 6 * rowA 1 2 6 + yW_2370 7 * rowA 1 2 7 + yW_2370 8 * rowA 1 2 8 ≤ db_2370 1 2 := by
  have hleft : yW_2370 0 * rowA 1 2 0 + yW_2370 1 * rowA 1 2 1 + yW_2370 2 * rowA 1 2 2 + yW_2370 3 * rowA 1 2 3 + yW_2370 4 * rowA 1 2 4 + yW_2370 5 * rowA 1 2 5 + yW_2370 6 * rowA 1 2 6 + yW_2370 7 * rowA 1 2 7 + yW_2370 8 * rowA 1 2 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 1 2 = (1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_1_3 :
    yW_2370 0 * rowA 1 3 0 + yW_2370 1 * rowA 1 3 1 + yW_2370 2 * rowA 1 3 2 + yW_2370 3 * rowA 1 3 3 + yW_2370 4 * rowA 1 3 4 + yW_2370 5 * rowA 1 3 5 + yW_2370 6 * rowA 1 3 6 + yW_2370 7 * rowA 1 3 7 + yW_2370 8 * rowA 1 3 8 ≤ db_2370 1 3 := by
  have hleft : yW_2370 0 * rowA 1 3 0 + yW_2370 1 * rowA 1 3 1 + yW_2370 2 * rowA 1 3 2 + yW_2370 3 * rowA 1 3 3 + yW_2370 4 * rowA 1 3 4 + yW_2370 5 * rowA 1 3 5 + yW_2370 6 * rowA 1 3 6 + yW_2370 7 * rowA 1 3 7 + yW_2370 8 * rowA 1 3 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 1 3 = (1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_1_4 :
    yW_2370 0 * rowA 1 4 0 + yW_2370 1 * rowA 1 4 1 + yW_2370 2 * rowA 1 4 2 + yW_2370 3 * rowA 1 4 3 + yW_2370 4 * rowA 1 4 4 + yW_2370 5 * rowA 1 4 5 + yW_2370 6 * rowA 1 4 6 + yW_2370 7 * rowA 1 4 7 + yW_2370 8 * rowA 1 4 8 ≤ db_2370 1 4 := by
  have hleft : yW_2370 0 * rowA 1 4 0 + yW_2370 1 * rowA 1 4 1 + yW_2370 2 * rowA 1 4 2 + yW_2370 3 * rowA 1 4 3 + yW_2370 4 * rowA 1 4 4 + yW_2370 5 * rowA 1 4 5 + yW_2370 6 * rowA 1 4 6 + yW_2370 7 * rowA 1 4 7 + yW_2370 8 * rowA 1 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 1 4 = (3 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_1_5 :
    yW_2370 0 * rowA 1 5 0 + yW_2370 1 * rowA 1 5 1 + yW_2370 2 * rowA 1 5 2 + yW_2370 3 * rowA 1 5 3 + yW_2370 4 * rowA 1 5 4 + yW_2370 5 * rowA 1 5 5 + yW_2370 6 * rowA 1 5 6 + yW_2370 7 * rowA 1 5 7 + yW_2370 8 * rowA 1 5 8 ≤ db_2370 1 5 := by
  have hleft : yW_2370 0 * rowA 1 5 0 + yW_2370 1 * rowA 1 5 1 + yW_2370 2 * rowA 1 5 2 + yW_2370 3 * rowA 1 5 3 + yW_2370 4 * rowA 1 5 4 + yW_2370 5 * rowA 1 5 5 + yW_2370 6 * rowA 1 5 6 + yW_2370 7 * rowA 1 5 7 + yW_2370 8 * rowA 1 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 1 5 = (1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_1_6 :
    yW_2370 0 * rowA 1 6 0 + yW_2370 1 * rowA 1 6 1 + yW_2370 2 * rowA 1 6 2 + yW_2370 3 * rowA 1 6 3 + yW_2370 4 * rowA 1 6 4 + yW_2370 5 * rowA 1 6 5 + yW_2370 6 * rowA 1 6 6 + yW_2370 7 * rowA 1 6 7 + yW_2370 8 * rowA 1 6 8 ≤ db_2370 1 6 := by
  have hleft : yW_2370 0 * rowA 1 6 0 + yW_2370 1 * rowA 1 6 1 + yW_2370 2 * rowA 1 6 2 + yW_2370 3 * rowA 1 6 3 + yW_2370 4 * rowA 1 6 4 + yW_2370 5 * rowA 1 6 5 + yW_2370 6 * rowA 1 6 6 + yW_2370 7 * rowA 1 6 7 + yW_2370 8 * rowA 1 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 1 6 = (5 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_1_7 :
    yW_2370 0 * rowA 1 7 0 + yW_2370 1 * rowA 1 7 1 + yW_2370 2 * rowA 1 7 2 + yW_2370 3 * rowA 1 7 3 + yW_2370 4 * rowA 1 7 4 + yW_2370 5 * rowA 1 7 5 + yW_2370 6 * rowA 1 7 6 + yW_2370 7 * rowA 1 7 7 + yW_2370 8 * rowA 1 7 8 ≤ db_2370 1 7 := by
  have hleft : yW_2370 0 * rowA 1 7 0 + yW_2370 1 * rowA 1 7 1 + yW_2370 2 * rowA 1 7 2 + yW_2370 3 * rowA 1 7 3 + yW_2370 4 * rowA 1 7 4 + yW_2370 5 * rowA 1 7 5 + yW_2370 6 * rowA 1 7 6 + yW_2370 7 * rowA 1 7 7 + yW_2370 8 * rowA 1 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 1 7 = (7 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_1_8 :
    yW_2370 0 * rowA 1 8 0 + yW_2370 1 * rowA 1 8 1 + yW_2370 2 * rowA 1 8 2 + yW_2370 3 * rowA 1 8 3 + yW_2370 4 * rowA 1 8 4 + yW_2370 5 * rowA 1 8 5 + yW_2370 6 * rowA 1 8 6 + yW_2370 7 * rowA 1 8 7 + yW_2370 8 * rowA 1 8 8 ≤ db_2370 1 8 := by
  have hleft : yW_2370 0 * rowA 1 8 0 + yW_2370 1 * rowA 1 8 1 + yW_2370 2 * rowA 1 8 2 + yW_2370 3 * rowA 1 8 3 + yW_2370 4 * rowA 1 8 4 + yW_2370 5 * rowA 1 8 5 + yW_2370 6 * rowA 1 8 6 + yW_2370 7 * rowA 1 8 7 + yW_2370 8 * rowA 1 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 1 8 = (7 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_1_9 :
    yW_2370 0 * rowA 1 9 0 + yW_2370 1 * rowA 1 9 1 + yW_2370 2 * rowA 1 9 2 + yW_2370 3 * rowA 1 9 3 + yW_2370 4 * rowA 1 9 4 + yW_2370 5 * rowA 1 9 5 + yW_2370 6 * rowA 1 9 6 + yW_2370 7 * rowA 1 9 7 + yW_2370 8 * rowA 1 9 8 ≤ db_2370 1 9 := by
  have hleft : yW_2370 0 * rowA 1 9 0 + yW_2370 1 * rowA 1 9 1 + yW_2370 2 * rowA 1 9 2 + yW_2370 3 * rowA 1 9 3 + yW_2370 4 * rowA 1 9 4 + yW_2370 5 * rowA 1 9 5 + yW_2370 6 * rowA 1 9 6 + yW_2370 7 * rowA 1 9 7 + yW_2370 8 * rowA 1 9 8 = (1 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 1 9 = (1 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_2_0 :
    yW_2370 0 * rowA 2 0 0 + yW_2370 1 * rowA 2 0 1 + yW_2370 2 * rowA 2 0 2 + yW_2370 3 * rowA 2 0 3 + yW_2370 4 * rowA 2 0 4 + yW_2370 5 * rowA 2 0 5 + yW_2370 6 * rowA 2 0 6 + yW_2370 7 * rowA 2 0 7 + yW_2370 8 * rowA 2 0 8 ≤ db_2370 2 0 := by
  have hleft : yW_2370 0 * rowA 2 0 0 + yW_2370 1 * rowA 2 0 1 + yW_2370 2 * rowA 2 0 2 + yW_2370 3 * rowA 2 0 3 + yW_2370 4 * rowA 2 0 4 + yW_2370 5 * rowA 2 0 5 + yW_2370 6 * rowA 2 0 6 + yW_2370 7 * rowA 2 0 7 + yW_2370 8 * rowA 2 0 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 2 0 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_2_1 :
    yW_2370 0 * rowA 2 1 0 + yW_2370 1 * rowA 2 1 1 + yW_2370 2 * rowA 2 1 2 + yW_2370 3 * rowA 2 1 3 + yW_2370 4 * rowA 2 1 4 + yW_2370 5 * rowA 2 1 5 + yW_2370 6 * rowA 2 1 6 + yW_2370 7 * rowA 2 1 7 + yW_2370 8 * rowA 2 1 8 ≤ db_2370 2 1 := by
  have hleft : yW_2370 0 * rowA 2 1 0 + yW_2370 1 * rowA 2 1 1 + yW_2370 2 * rowA 2 1 2 + yW_2370 3 * rowA 2 1 3 + yW_2370 4 * rowA 2 1 4 + yW_2370 5 * rowA 2 1 5 + yW_2370 6 * rowA 2 1 6 + yW_2370 7 * rowA 2 1 7 + yW_2370 8 * rowA 2 1 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 2 1 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_2_2 :
    yW_2370 0 * rowA 2 2 0 + yW_2370 1 * rowA 2 2 1 + yW_2370 2 * rowA 2 2 2 + yW_2370 3 * rowA 2 2 3 + yW_2370 4 * rowA 2 2 4 + yW_2370 5 * rowA 2 2 5 + yW_2370 6 * rowA 2 2 6 + yW_2370 7 * rowA 2 2 7 + yW_2370 8 * rowA 2 2 8 ≤ db_2370 2 2 := by
  have hleft : yW_2370 0 * rowA 2 2 0 + yW_2370 1 * rowA 2 2 1 + yW_2370 2 * rowA 2 2 2 + yW_2370 3 * rowA 2 2 3 + yW_2370 4 * rowA 2 2 4 + yW_2370 5 * rowA 2 2 5 + yW_2370 6 * rowA 2 2 6 + yW_2370 7 * rowA 2 2 7 + yW_2370 8 * rowA 2 2 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 2 2 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_2_3 :
    yW_2370 0 * rowA 2 3 0 + yW_2370 1 * rowA 2 3 1 + yW_2370 2 * rowA 2 3 2 + yW_2370 3 * rowA 2 3 3 + yW_2370 4 * rowA 2 3 4 + yW_2370 5 * rowA 2 3 5 + yW_2370 6 * rowA 2 3 6 + yW_2370 7 * rowA 2 3 7 + yW_2370 8 * rowA 2 3 8 ≤ db_2370 2 3 := by
  have hleft : yW_2370 0 * rowA 2 3 0 + yW_2370 1 * rowA 2 3 1 + yW_2370 2 * rowA 2 3 2 + yW_2370 3 * rowA 2 3 3 + yW_2370 4 * rowA 2 3 4 + yW_2370 5 * rowA 2 3 5 + yW_2370 6 * rowA 2 3 6 + yW_2370 7 * rowA 2 3 7 + yW_2370 8 * rowA 2 3 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 2 3 = (1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_2_4 :
    yW_2370 0 * rowA 2 4 0 + yW_2370 1 * rowA 2 4 1 + yW_2370 2 * rowA 2 4 2 + yW_2370 3 * rowA 2 4 3 + yW_2370 4 * rowA 2 4 4 + yW_2370 5 * rowA 2 4 5 + yW_2370 6 * rowA 2 4 6 + yW_2370 7 * rowA 2 4 7 + yW_2370 8 * rowA 2 4 8 ≤ db_2370 2 4 := by
  have hleft : yW_2370 0 * rowA 2 4 0 + yW_2370 1 * rowA 2 4 1 + yW_2370 2 * rowA 2 4 2 + yW_2370 3 * rowA 2 4 3 + yW_2370 4 * rowA 2 4 4 + yW_2370 5 * rowA 2 4 5 + yW_2370 6 * rowA 2 4 6 + yW_2370 7 * rowA 2 4 7 + yW_2370 8 * rowA 2 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 2 4 = (3 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_2_5 :
    yW_2370 0 * rowA 2 5 0 + yW_2370 1 * rowA 2 5 1 + yW_2370 2 * rowA 2 5 2 + yW_2370 3 * rowA 2 5 3 + yW_2370 4 * rowA 2 5 4 + yW_2370 5 * rowA 2 5 5 + yW_2370 6 * rowA 2 5 6 + yW_2370 7 * rowA 2 5 7 + yW_2370 8 * rowA 2 5 8 ≤ db_2370 2 5 := by
  have hleft : yW_2370 0 * rowA 2 5 0 + yW_2370 1 * rowA 2 5 1 + yW_2370 2 * rowA 2 5 2 + yW_2370 3 * rowA 2 5 3 + yW_2370 4 * rowA 2 5 4 + yW_2370 5 * rowA 2 5 5 + yW_2370 6 * rowA 2 5 6 + yW_2370 7 * rowA 2 5 7 + yW_2370 8 * rowA 2 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 2 5 = (1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_2_6 :
    yW_2370 0 * rowA 2 6 0 + yW_2370 1 * rowA 2 6 1 + yW_2370 2 * rowA 2 6 2 + yW_2370 3 * rowA 2 6 3 + yW_2370 4 * rowA 2 6 4 + yW_2370 5 * rowA 2 6 5 + yW_2370 6 * rowA 2 6 6 + yW_2370 7 * rowA 2 6 7 + yW_2370 8 * rowA 2 6 8 ≤ db_2370 2 6 := by
  have hleft : yW_2370 0 * rowA 2 6 0 + yW_2370 1 * rowA 2 6 1 + yW_2370 2 * rowA 2 6 2 + yW_2370 3 * rowA 2 6 3 + yW_2370 4 * rowA 2 6 4 + yW_2370 5 * rowA 2 6 5 + yW_2370 6 * rowA 2 6 6 + yW_2370 7 * rowA 2 6 7 + yW_2370 8 * rowA 2 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 2 6 = (5 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_2_7 :
    yW_2370 0 * rowA 2 7 0 + yW_2370 1 * rowA 2 7 1 + yW_2370 2 * rowA 2 7 2 + yW_2370 3 * rowA 2 7 3 + yW_2370 4 * rowA 2 7 4 + yW_2370 5 * rowA 2 7 5 + yW_2370 6 * rowA 2 7 6 + yW_2370 7 * rowA 2 7 7 + yW_2370 8 * rowA 2 7 8 ≤ db_2370 2 7 := by
  have hleft : yW_2370 0 * rowA 2 7 0 + yW_2370 1 * rowA 2 7 1 + yW_2370 2 * rowA 2 7 2 + yW_2370 3 * rowA 2 7 3 + yW_2370 4 * rowA 2 7 4 + yW_2370 5 * rowA 2 7 5 + yW_2370 6 * rowA 2 7 6 + yW_2370 7 * rowA 2 7 7 + yW_2370 8 * rowA 2 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 2 7 = (7 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_2_8 :
    yW_2370 0 * rowA 2 8 0 + yW_2370 1 * rowA 2 8 1 + yW_2370 2 * rowA 2 8 2 + yW_2370 3 * rowA 2 8 3 + yW_2370 4 * rowA 2 8 4 + yW_2370 5 * rowA 2 8 5 + yW_2370 6 * rowA 2 8 6 + yW_2370 7 * rowA 2 8 7 + yW_2370 8 * rowA 2 8 8 ≤ db_2370 2 8 := by
  have hleft : yW_2370 0 * rowA 2 8 0 + yW_2370 1 * rowA 2 8 1 + yW_2370 2 * rowA 2 8 2 + yW_2370 3 * rowA 2 8 3 + yW_2370 4 * rowA 2 8 4 + yW_2370 5 * rowA 2 8 5 + yW_2370 6 * rowA 2 8 6 + yW_2370 7 * rowA 2 8 7 + yW_2370 8 * rowA 2 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 2 8 = (7 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_2_9 :
    yW_2370 0 * rowA 2 9 0 + yW_2370 1 * rowA 2 9 1 + yW_2370 2 * rowA 2 9 2 + yW_2370 3 * rowA 2 9 3 + yW_2370 4 * rowA 2 9 4 + yW_2370 5 * rowA 2 9 5 + yW_2370 6 * rowA 2 9 6 + yW_2370 7 * rowA 2 9 7 + yW_2370 8 * rowA 2 9 8 ≤ db_2370 2 9 := by
  have hleft : yW_2370 0 * rowA 2 9 0 + yW_2370 1 * rowA 2 9 1 + yW_2370 2 * rowA 2 9 2 + yW_2370 3 * rowA 2 9 3 + yW_2370 4 * rowA 2 9 4 + yW_2370 5 * rowA 2 9 5 + yW_2370 6 * rowA 2 9 6 + yW_2370 7 * rowA 2 9 7 + yW_2370 8 * rowA 2 9 8 = (1 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 2 9 = (1 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_3_0 :
    yW_2370 0 * rowA 3 0 0 + yW_2370 1 * rowA 3 0 1 + yW_2370 2 * rowA 3 0 2 + yW_2370 3 * rowA 3 0 3 + yW_2370 4 * rowA 3 0 4 + yW_2370 5 * rowA 3 0 5 + yW_2370 6 * rowA 3 0 6 + yW_2370 7 * rowA 3 0 7 + yW_2370 8 * rowA 3 0 8 ≤ db_2370 3 0 := by
  have hleft : yW_2370 0 * rowA 3 0 0 + yW_2370 1 * rowA 3 0 1 + yW_2370 2 * rowA 3 0 2 + yW_2370 3 * rowA 3 0 3 + yW_2370 4 * rowA 3 0 4 + yW_2370 5 * rowA 3 0 5 + yW_2370 6 * rowA 3 0 6 + yW_2370 7 * rowA 3 0 7 + yW_2370 8 * rowA 3 0 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 3 0 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_3_1 :
    yW_2370 0 * rowA 3 1 0 + yW_2370 1 * rowA 3 1 1 + yW_2370 2 * rowA 3 1 2 + yW_2370 3 * rowA 3 1 3 + yW_2370 4 * rowA 3 1 4 + yW_2370 5 * rowA 3 1 5 + yW_2370 6 * rowA 3 1 6 + yW_2370 7 * rowA 3 1 7 + yW_2370 8 * rowA 3 1 8 ≤ db_2370 3 1 := by
  have hleft : yW_2370 0 * rowA 3 1 0 + yW_2370 1 * rowA 3 1 1 + yW_2370 2 * rowA 3 1 2 + yW_2370 3 * rowA 3 1 3 + yW_2370 4 * rowA 3 1 4 + yW_2370 5 * rowA 3 1 5 + yW_2370 6 * rowA 3 1 6 + yW_2370 7 * rowA 3 1 7 + yW_2370 8 * rowA 3 1 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 3 1 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_3_2 :
    yW_2370 0 * rowA 3 2 0 + yW_2370 1 * rowA 3 2 1 + yW_2370 2 * rowA 3 2 2 + yW_2370 3 * rowA 3 2 3 + yW_2370 4 * rowA 3 2 4 + yW_2370 5 * rowA 3 2 5 + yW_2370 6 * rowA 3 2 6 + yW_2370 7 * rowA 3 2 7 + yW_2370 8 * rowA 3 2 8 ≤ db_2370 3 2 := by
  have hleft : yW_2370 0 * rowA 3 2 0 + yW_2370 1 * rowA 3 2 1 + yW_2370 2 * rowA 3 2 2 + yW_2370 3 * rowA 3 2 3 + yW_2370 4 * rowA 3 2 4 + yW_2370 5 * rowA 3 2 5 + yW_2370 6 * rowA 3 2 6 + yW_2370 7 * rowA 3 2 7 + yW_2370 8 * rowA 3 2 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 3 2 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_3_3 :
    yW_2370 0 * rowA 3 3 0 + yW_2370 1 * rowA 3 3 1 + yW_2370 2 * rowA 3 3 2 + yW_2370 3 * rowA 3 3 3 + yW_2370 4 * rowA 3 3 4 + yW_2370 5 * rowA 3 3 5 + yW_2370 6 * rowA 3 3 6 + yW_2370 7 * rowA 3 3 7 + yW_2370 8 * rowA 3 3 8 ≤ db_2370 3 3 := by
  have hleft : yW_2370 0 * rowA 3 3 0 + yW_2370 1 * rowA 3 3 1 + yW_2370 2 * rowA 3 3 2 + yW_2370 3 * rowA 3 3 3 + yW_2370 4 * rowA 3 3 4 + yW_2370 5 * rowA 3 3 5 + yW_2370 6 * rowA 3 3 6 + yW_2370 7 * rowA 3 3 7 + yW_2370 8 * rowA 3 3 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 3 3 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_3_4 :
    yW_2370 0 * rowA 3 4 0 + yW_2370 1 * rowA 3 4 1 + yW_2370 2 * rowA 3 4 2 + yW_2370 3 * rowA 3 4 3 + yW_2370 4 * rowA 3 4 4 + yW_2370 5 * rowA 3 4 5 + yW_2370 6 * rowA 3 4 6 + yW_2370 7 * rowA 3 4 7 + yW_2370 8 * rowA 3 4 8 ≤ db_2370 3 4 := by
  have hleft : yW_2370 0 * rowA 3 4 0 + yW_2370 1 * rowA 3 4 1 + yW_2370 2 * rowA 3 4 2 + yW_2370 3 * rowA 3 4 3 + yW_2370 4 * rowA 3 4 4 + yW_2370 5 * rowA 3 4 5 + yW_2370 6 * rowA 3 4 6 + yW_2370 7 * rowA 3 4 7 + yW_2370 8 * rowA 3 4 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 3 4 = (1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_3_5 :
    yW_2370 0 * rowA 3 5 0 + yW_2370 1 * rowA 3 5 1 + yW_2370 2 * rowA 3 5 2 + yW_2370 3 * rowA 3 5 3 + yW_2370 4 * rowA 3 5 4 + yW_2370 5 * rowA 3 5 5 + yW_2370 6 * rowA 3 5 6 + yW_2370 7 * rowA 3 5 7 + yW_2370 8 * rowA 3 5 8 ≤ db_2370 3 5 := by
  have hleft : yW_2370 0 * rowA 3 5 0 + yW_2370 1 * rowA 3 5 1 + yW_2370 2 * rowA 3 5 2 + yW_2370 3 * rowA 3 5 3 + yW_2370 4 * rowA 3 5 4 + yW_2370 5 * rowA 3 5 5 + yW_2370 6 * rowA 3 5 6 + yW_2370 7 * rowA 3 5 7 + yW_2370 8 * rowA 3 5 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 3 5 = (3 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_3_6 :
    yW_2370 0 * rowA 3 6 0 + yW_2370 1 * rowA 3 6 1 + yW_2370 2 * rowA 3 6 2 + yW_2370 3 * rowA 3 6 3 + yW_2370 4 * rowA 3 6 4 + yW_2370 5 * rowA 3 6 5 + yW_2370 6 * rowA 3 6 6 + yW_2370 7 * rowA 3 6 7 + yW_2370 8 * rowA 3 6 8 ≤ db_2370 3 6 := by
  have hleft : yW_2370 0 * rowA 3 6 0 + yW_2370 1 * rowA 3 6 1 + yW_2370 2 * rowA 3 6 2 + yW_2370 3 * rowA 3 6 3 + yW_2370 4 * rowA 3 6 4 + yW_2370 5 * rowA 3 6 5 + yW_2370 6 * rowA 3 6 6 + yW_2370 7 * rowA 3 6 7 + yW_2370 8 * rowA 3 6 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 3 6 = (5 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_3_7 :
    yW_2370 0 * rowA 3 7 0 + yW_2370 1 * rowA 3 7 1 + yW_2370 2 * rowA 3 7 2 + yW_2370 3 * rowA 3 7 3 + yW_2370 4 * rowA 3 7 4 + yW_2370 5 * rowA 3 7 5 + yW_2370 6 * rowA 3 7 6 + yW_2370 7 * rowA 3 7 7 + yW_2370 8 * rowA 3 7 8 ≤ db_2370 3 7 := by
  have hleft : yW_2370 0 * rowA 3 7 0 + yW_2370 1 * rowA 3 7 1 + yW_2370 2 * rowA 3 7 2 + yW_2370 3 * rowA 3 7 3 + yW_2370 4 * rowA 3 7 4 + yW_2370 5 * rowA 3 7 5 + yW_2370 6 * rowA 3 7 6 + yW_2370 7 * rowA 3 7 7 + yW_2370 8 * rowA 3 7 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 3 7 = (5 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_3_8 :
    yW_2370 0 * rowA 3 8 0 + yW_2370 1 * rowA 3 8 1 + yW_2370 2 * rowA 3 8 2 + yW_2370 3 * rowA 3 8 3 + yW_2370 4 * rowA 3 8 4 + yW_2370 5 * rowA 3 8 5 + yW_2370 6 * rowA 3 8 6 + yW_2370 7 * rowA 3 8 7 + yW_2370 8 * rowA 3 8 8 ≤ db_2370 3 8 := by
  have hleft : yW_2370 0 * rowA 3 8 0 + yW_2370 1 * rowA 3 8 1 + yW_2370 2 * rowA 3 8 2 + yW_2370 3 * rowA 3 8 3 + yW_2370 4 * rowA 3 8 4 + yW_2370 5 * rowA 3 8 5 + yW_2370 6 * rowA 3 8 6 + yW_2370 7 * rowA 3 8 7 + yW_2370 8 * rowA 3 8 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 3 8 = (5 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_3_9 :
    yW_2370 0 * rowA 3 9 0 + yW_2370 1 * rowA 3 9 1 + yW_2370 2 * rowA 3 9 2 + yW_2370 3 * rowA 3 9 3 + yW_2370 4 * rowA 3 9 4 + yW_2370 5 * rowA 3 9 5 + yW_2370 6 * rowA 3 9 6 + yW_2370 7 * rowA 3 9 7 + yW_2370 8 * rowA 3 9 8 ≤ db_2370 3 9 := by
  have hleft : yW_2370 0 * rowA 3 9 0 + yW_2370 1 * rowA 3 9 1 + yW_2370 2 * rowA 3 9 2 + yW_2370 3 * rowA 3 9 3 + yW_2370 4 * rowA 3 9 4 + yW_2370 5 * rowA 3 9 5 + yW_2370 6 * rowA 3 9 6 + yW_2370 7 * rowA 3 9 7 + yW_2370 8 * rowA 3 9 8 = (1 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 3 9 = (1 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_4_0 :
    yW_2370 0 * rowA 4 0 0 + yW_2370 1 * rowA 4 0 1 + yW_2370 2 * rowA 4 0 2 + yW_2370 3 * rowA 4 0 3 + yW_2370 4 * rowA 4 0 4 + yW_2370 5 * rowA 4 0 5 + yW_2370 6 * rowA 4 0 6 + yW_2370 7 * rowA 4 0 7 + yW_2370 8 * rowA 4 0 8 ≤ db_2370 4 0 := by
  have hleft : yW_2370 0 * rowA 4 0 0 + yW_2370 1 * rowA 4 0 1 + yW_2370 2 * rowA 4 0 2 + yW_2370 3 * rowA 4 0 3 + yW_2370 4 * rowA 4 0 4 + yW_2370 5 * rowA 4 0 5 + yW_2370 6 * rowA 4 0 6 + yW_2370 7 * rowA 4 0 7 + yW_2370 8 * rowA 4 0 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 4 0 = (-1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_4_1 :
    yW_2370 0 * rowA 4 1 0 + yW_2370 1 * rowA 4 1 1 + yW_2370 2 * rowA 4 1 2 + yW_2370 3 * rowA 4 1 3 + yW_2370 4 * rowA 4 1 4 + yW_2370 5 * rowA 4 1 5 + yW_2370 6 * rowA 4 1 6 + yW_2370 7 * rowA 4 1 7 + yW_2370 8 * rowA 4 1 8 ≤ db_2370 4 1 := by
  have hleft : yW_2370 0 * rowA 4 1 0 + yW_2370 1 * rowA 4 1 1 + yW_2370 2 * rowA 4 1 2 + yW_2370 3 * rowA 4 1 3 + yW_2370 4 * rowA 4 1 4 + yW_2370 5 * rowA 4 1 5 + yW_2370 6 * rowA 4 1 6 + yW_2370 7 * rowA 4 1 7 + yW_2370 8 * rowA 4 1 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 4 1 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_4_2 :
    yW_2370 0 * rowA 4 2 0 + yW_2370 1 * rowA 4 2 1 + yW_2370 2 * rowA 4 2 2 + yW_2370 3 * rowA 4 2 3 + yW_2370 4 * rowA 4 2 4 + yW_2370 5 * rowA 4 2 5 + yW_2370 6 * rowA 4 2 6 + yW_2370 7 * rowA 4 2 7 + yW_2370 8 * rowA 4 2 8 ≤ db_2370 4 2 := by
  have hleft : yW_2370 0 * rowA 4 2 0 + yW_2370 1 * rowA 4 2 1 + yW_2370 2 * rowA 4 2 2 + yW_2370 3 * rowA 4 2 3 + yW_2370 4 * rowA 4 2 4 + yW_2370 5 * rowA 4 2 5 + yW_2370 6 * rowA 4 2 6 + yW_2370 7 * rowA 4 2 7 + yW_2370 8 * rowA 4 2 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 4 2 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_4_3 :
    yW_2370 0 * rowA 4 3 0 + yW_2370 1 * rowA 4 3 1 + yW_2370 2 * rowA 4 3 2 + yW_2370 3 * rowA 4 3 3 + yW_2370 4 * rowA 4 3 4 + yW_2370 5 * rowA 4 3 5 + yW_2370 6 * rowA 4 3 6 + yW_2370 7 * rowA 4 3 7 + yW_2370 8 * rowA 4 3 8 ≤ db_2370 4 3 := by
  have hleft : yW_2370 0 * rowA 4 3 0 + yW_2370 1 * rowA 4 3 1 + yW_2370 2 * rowA 4 3 2 + yW_2370 3 * rowA 4 3 3 + yW_2370 4 * rowA 4 3 4 + yW_2370 5 * rowA 4 3 5 + yW_2370 6 * rowA 4 3 6 + yW_2370 7 * rowA 4 3 7 + yW_2370 8 * rowA 4 3 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 4 3 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_4_4 :
    yW_2370 0 * rowA 4 4 0 + yW_2370 1 * rowA 4 4 1 + yW_2370 2 * rowA 4 4 2 + yW_2370 3 * rowA 4 4 3 + yW_2370 4 * rowA 4 4 4 + yW_2370 5 * rowA 4 4 5 + yW_2370 6 * rowA 4 4 6 + yW_2370 7 * rowA 4 4 7 + yW_2370 8 * rowA 4 4 8 ≤ db_2370 4 4 := by
  have hleft : yW_2370 0 * rowA 4 4 0 + yW_2370 1 * rowA 4 4 1 + yW_2370 2 * rowA 4 4 2 + yW_2370 3 * rowA 4 4 3 + yW_2370 4 * rowA 4 4 4 + yW_2370 5 * rowA 4 4 5 + yW_2370 6 * rowA 4 4 6 + yW_2370 7 * rowA 4 4 7 + yW_2370 8 * rowA 4 4 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 4 4 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_4_5 :
    yW_2370 0 * rowA 4 5 0 + yW_2370 1 * rowA 4 5 1 + yW_2370 2 * rowA 4 5 2 + yW_2370 3 * rowA 4 5 3 + yW_2370 4 * rowA 4 5 4 + yW_2370 5 * rowA 4 5 5 + yW_2370 6 * rowA 4 5 6 + yW_2370 7 * rowA 4 5 7 + yW_2370 8 * rowA 4 5 8 ≤ db_2370 4 5 := by
  have hleft : yW_2370 0 * rowA 4 5 0 + yW_2370 1 * rowA 4 5 1 + yW_2370 2 * rowA 4 5 2 + yW_2370 3 * rowA 4 5 3 + yW_2370 4 * rowA 4 5 4 + yW_2370 5 * rowA 4 5 5 + yW_2370 6 * rowA 4 5 6 + yW_2370 7 * rowA 4 5 7 + yW_2370 8 * rowA 4 5 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 4 5 = (1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_4_6 :
    yW_2370 0 * rowA 4 6 0 + yW_2370 1 * rowA 4 6 1 + yW_2370 2 * rowA 4 6 2 + yW_2370 3 * rowA 4 6 3 + yW_2370 4 * rowA 4 6 4 + yW_2370 5 * rowA 4 6 5 + yW_2370 6 * rowA 4 6 6 + yW_2370 7 * rowA 4 6 7 + yW_2370 8 * rowA 4 6 8 ≤ db_2370 4 6 := by
  have hleft : yW_2370 0 * rowA 4 6 0 + yW_2370 1 * rowA 4 6 1 + yW_2370 2 * rowA 4 6 2 + yW_2370 3 * rowA 4 6 3 + yW_2370 4 * rowA 4 6 4 + yW_2370 5 * rowA 4 6 5 + yW_2370 6 * rowA 4 6 6 + yW_2370 7 * rowA 4 6 7 + yW_2370 8 * rowA 4 6 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 4 6 = (3 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_4_7 :
    yW_2370 0 * rowA 4 7 0 + yW_2370 1 * rowA 4 7 1 + yW_2370 2 * rowA 4 7 2 + yW_2370 3 * rowA 4 7 3 + yW_2370 4 * rowA 4 7 4 + yW_2370 5 * rowA 4 7 5 + yW_2370 6 * rowA 4 7 6 + yW_2370 7 * rowA 4 7 7 + yW_2370 8 * rowA 4 7 8 ≤ db_2370 4 7 := by
  have hleft : yW_2370 0 * rowA 4 7 0 + yW_2370 1 * rowA 4 7 1 + yW_2370 2 * rowA 4 7 2 + yW_2370 3 * rowA 4 7 3 + yW_2370 4 * rowA 4 7 4 + yW_2370 5 * rowA 4 7 5 + yW_2370 6 * rowA 4 7 6 + yW_2370 7 * rowA 4 7 7 + yW_2370 8 * rowA 4 7 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 4 7 = (1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_4_8 :
    yW_2370 0 * rowA 4 8 0 + yW_2370 1 * rowA 4 8 1 + yW_2370 2 * rowA 4 8 2 + yW_2370 3 * rowA 4 8 3 + yW_2370 4 * rowA 4 8 4 + yW_2370 5 * rowA 4 8 5 + yW_2370 6 * rowA 4 8 6 + yW_2370 7 * rowA 4 8 7 + yW_2370 8 * rowA 4 8 8 ≤ db_2370 4 8 := by
  have hleft : yW_2370 0 * rowA 4 8 0 + yW_2370 1 * rowA 4 8 1 + yW_2370 2 * rowA 4 8 2 + yW_2370 3 * rowA 4 8 3 + yW_2370 4 * rowA 4 8 4 + yW_2370 5 * rowA 4 8 5 + yW_2370 6 * rowA 4 8 6 + yW_2370 7 * rowA 4 8 7 + yW_2370 8 * rowA 4 8 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 4 8 = (1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_4_9 :
    yW_2370 0 * rowA 4 9 0 + yW_2370 1 * rowA 4 9 1 + yW_2370 2 * rowA 4 9 2 + yW_2370 3 * rowA 4 9 3 + yW_2370 4 * rowA 4 9 4 + yW_2370 5 * rowA 4 9 5 + yW_2370 6 * rowA 4 9 6 + yW_2370 7 * rowA 4 9 7 + yW_2370 8 * rowA 4 9 8 ≤ db_2370 4 9 := by
  have hleft : yW_2370 0 * rowA 4 9 0 + yW_2370 1 * rowA 4 9 1 + yW_2370 2 * rowA 4 9 2 + yW_2370 3 * rowA 4 9 3 + yW_2370 4 * rowA 4 9 4 + yW_2370 5 * rowA 4 9 5 + yW_2370 6 * rowA 4 9 6 + yW_2370 7 * rowA 4 9 7 + yW_2370 8 * rowA 4 9 8 = (3 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 4 9 = (3 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_5_0 :
    yW_2370 0 * rowA 5 0 0 + yW_2370 1 * rowA 5 0 1 + yW_2370 2 * rowA 5 0 2 + yW_2370 3 * rowA 5 0 3 + yW_2370 4 * rowA 5 0 4 + yW_2370 5 * rowA 5 0 5 + yW_2370 6 * rowA 5 0 6 + yW_2370 7 * rowA 5 0 7 + yW_2370 8 * rowA 5 0 8 ≤ db_2370 5 0 := by
  have hleft : yW_2370 0 * rowA 5 0 0 + yW_2370 1 * rowA 5 0 1 + yW_2370 2 * rowA 5 0 2 + yW_2370 3 * rowA 5 0 3 + yW_2370 4 * rowA 5 0 4 + yW_2370 5 * rowA 5 0 5 + yW_2370 6 * rowA 5 0 6 + yW_2370 7 * rowA 5 0 7 + yW_2370 8 * rowA 5 0 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 5 0 = (-1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_5_1 :
    yW_2370 0 * rowA 5 1 0 + yW_2370 1 * rowA 5 1 1 + yW_2370 2 * rowA 5 1 2 + yW_2370 3 * rowA 5 1 3 + yW_2370 4 * rowA 5 1 4 + yW_2370 5 * rowA 5 1 5 + yW_2370 6 * rowA 5 1 6 + yW_2370 7 * rowA 5 1 7 + yW_2370 8 * rowA 5 1 8 ≤ db_2370 5 1 := by
  have hleft : yW_2370 0 * rowA 5 1 0 + yW_2370 1 * rowA 5 1 1 + yW_2370 2 * rowA 5 1 2 + yW_2370 3 * rowA 5 1 3 + yW_2370 4 * rowA 5 1 4 + yW_2370 5 * rowA 5 1 5 + yW_2370 6 * rowA 5 1 6 + yW_2370 7 * rowA 5 1 7 + yW_2370 8 * rowA 5 1 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 5 1 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_5_2 :
    yW_2370 0 * rowA 5 2 0 + yW_2370 1 * rowA 5 2 1 + yW_2370 2 * rowA 5 2 2 + yW_2370 3 * rowA 5 2 3 + yW_2370 4 * rowA 5 2 4 + yW_2370 5 * rowA 5 2 5 + yW_2370 6 * rowA 5 2 6 + yW_2370 7 * rowA 5 2 7 + yW_2370 8 * rowA 5 2 8 ≤ db_2370 5 2 := by
  have hleft : yW_2370 0 * rowA 5 2 0 + yW_2370 1 * rowA 5 2 1 + yW_2370 2 * rowA 5 2 2 + yW_2370 3 * rowA 5 2 3 + yW_2370 4 * rowA 5 2 4 + yW_2370 5 * rowA 5 2 5 + yW_2370 6 * rowA 5 2 6 + yW_2370 7 * rowA 5 2 7 + yW_2370 8 * rowA 5 2 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 5 2 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_5_3 :
    yW_2370 0 * rowA 5 3 0 + yW_2370 1 * rowA 5 3 1 + yW_2370 2 * rowA 5 3 2 + yW_2370 3 * rowA 5 3 3 + yW_2370 4 * rowA 5 3 4 + yW_2370 5 * rowA 5 3 5 + yW_2370 6 * rowA 5 3 6 + yW_2370 7 * rowA 5 3 7 + yW_2370 8 * rowA 5 3 8 ≤ db_2370 5 3 := by
  have hleft : yW_2370 0 * rowA 5 3 0 + yW_2370 1 * rowA 5 3 1 + yW_2370 2 * rowA 5 3 2 + yW_2370 3 * rowA 5 3 3 + yW_2370 4 * rowA 5 3 4 + yW_2370 5 * rowA 5 3 5 + yW_2370 6 * rowA 5 3 6 + yW_2370 7 * rowA 5 3 7 + yW_2370 8 * rowA 5 3 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 5 3 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_5_4 :
    yW_2370 0 * rowA 5 4 0 + yW_2370 1 * rowA 5 4 1 + yW_2370 2 * rowA 5 4 2 + yW_2370 3 * rowA 5 4 3 + yW_2370 4 * rowA 5 4 4 + yW_2370 5 * rowA 5 4 5 + yW_2370 6 * rowA 5 4 6 + yW_2370 7 * rowA 5 4 7 + yW_2370 8 * rowA 5 4 8 ≤ db_2370 5 4 := by
  have hleft : yW_2370 0 * rowA 5 4 0 + yW_2370 1 * rowA 5 4 1 + yW_2370 2 * rowA 5 4 2 + yW_2370 3 * rowA 5 4 3 + yW_2370 4 * rowA 5 4 4 + yW_2370 5 * rowA 5 4 5 + yW_2370 6 * rowA 5 4 6 + yW_2370 7 * rowA 5 4 7 + yW_2370 8 * rowA 5 4 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 5 4 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_5_5 :
    yW_2370 0 * rowA 5 5 0 + yW_2370 1 * rowA 5 5 1 + yW_2370 2 * rowA 5 5 2 + yW_2370 3 * rowA 5 5 3 + yW_2370 4 * rowA 5 5 4 + yW_2370 5 * rowA 5 5 5 + yW_2370 6 * rowA 5 5 6 + yW_2370 7 * rowA 5 5 7 + yW_2370 8 * rowA 5 5 8 ≤ db_2370 5 5 := by
  have hleft : yW_2370 0 * rowA 5 5 0 + yW_2370 1 * rowA 5 5 1 + yW_2370 2 * rowA 5 5 2 + yW_2370 3 * rowA 5 5 3 + yW_2370 4 * rowA 5 5 4 + yW_2370 5 * rowA 5 5 5 + yW_2370 6 * rowA 5 5 6 + yW_2370 7 * rowA 5 5 7 + yW_2370 8 * rowA 5 5 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 5 5 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_5_6 :
    yW_2370 0 * rowA 5 6 0 + yW_2370 1 * rowA 5 6 1 + yW_2370 2 * rowA 5 6 2 + yW_2370 3 * rowA 5 6 3 + yW_2370 4 * rowA 5 6 4 + yW_2370 5 * rowA 5 6 5 + yW_2370 6 * rowA 5 6 6 + yW_2370 7 * rowA 5 6 7 + yW_2370 8 * rowA 5 6 8 ≤ db_2370 5 6 := by
  have hleft : yW_2370 0 * rowA 5 6 0 + yW_2370 1 * rowA 5 6 1 + yW_2370 2 * rowA 5 6 2 + yW_2370 3 * rowA 5 6 3 + yW_2370 4 * rowA 5 6 4 + yW_2370 5 * rowA 5 6 5 + yW_2370 6 * rowA 5 6 6 + yW_2370 7 * rowA 5 6 7 + yW_2370 8 * rowA 5 6 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 5 6 = (3 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_5_7 :
    yW_2370 0 * rowA 5 7 0 + yW_2370 1 * rowA 5 7 1 + yW_2370 2 * rowA 5 7 2 + yW_2370 3 * rowA 5 7 3 + yW_2370 4 * rowA 5 7 4 + yW_2370 5 * rowA 5 7 5 + yW_2370 6 * rowA 5 7 6 + yW_2370 7 * rowA 5 7 7 + yW_2370 8 * rowA 5 7 8 ≤ db_2370 5 7 := by
  have hleft : yW_2370 0 * rowA 5 7 0 + yW_2370 1 * rowA 5 7 1 + yW_2370 2 * rowA 5 7 2 + yW_2370 3 * rowA 5 7 3 + yW_2370 4 * rowA 5 7 4 + yW_2370 5 * rowA 5 7 5 + yW_2370 6 * rowA 5 7 6 + yW_2370 7 * rowA 5 7 7 + yW_2370 8 * rowA 5 7 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 5 7 = (1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_5_8 :
    yW_2370 0 * rowA 5 8 0 + yW_2370 1 * rowA 5 8 1 + yW_2370 2 * rowA 5 8 2 + yW_2370 3 * rowA 5 8 3 + yW_2370 4 * rowA 5 8 4 + yW_2370 5 * rowA 5 8 5 + yW_2370 6 * rowA 5 8 6 + yW_2370 7 * rowA 5 8 7 + yW_2370 8 * rowA 5 8 8 ≤ db_2370 5 8 := by
  have hleft : yW_2370 0 * rowA 5 8 0 + yW_2370 1 * rowA 5 8 1 + yW_2370 2 * rowA 5 8 2 + yW_2370 3 * rowA 5 8 3 + yW_2370 4 * rowA 5 8 4 + yW_2370 5 * rowA 5 8 5 + yW_2370 6 * rowA 5 8 6 + yW_2370 7 * rowA 5 8 7 + yW_2370 8 * rowA 5 8 8 = (1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 5 8 = (1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_5_9 :
    yW_2370 0 * rowA 5 9 0 + yW_2370 1 * rowA 5 9 1 + yW_2370 2 * rowA 5 9 2 + yW_2370 3 * rowA 5 9 3 + yW_2370 4 * rowA 5 9 4 + yW_2370 5 * rowA 5 9 5 + yW_2370 6 * rowA 5 9 6 + yW_2370 7 * rowA 5 9 7 + yW_2370 8 * rowA 5 9 8 ≤ db_2370 5 9 := by
  have hleft : yW_2370 0 * rowA 5 9 0 + yW_2370 1 * rowA 5 9 1 + yW_2370 2 * rowA 5 9 2 + yW_2370 3 * rowA 5 9 3 + yW_2370 4 * rowA 5 9 4 + yW_2370 5 * rowA 5 9 5 + yW_2370 6 * rowA 5 9 6 + yW_2370 7 * rowA 5 9 7 + yW_2370 8 * rowA 5 9 8 = (5 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 5 9 = (3 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_6_0 :
    yW_2370 0 * rowA 6 0 0 + yW_2370 1 * rowA 6 0 1 + yW_2370 2 * rowA 6 0 2 + yW_2370 3 * rowA 6 0 3 + yW_2370 4 * rowA 6 0 4 + yW_2370 5 * rowA 6 0 5 + yW_2370 6 * rowA 6 0 6 + yW_2370 7 * rowA 6 0 7 + yW_2370 8 * rowA 6 0 8 ≤ db_2370 6 0 := by
  have hleft : yW_2370 0 * rowA 6 0 0 + yW_2370 1 * rowA 6 0 1 + yW_2370 2 * rowA 6 0 2 + yW_2370 3 * rowA 6 0 3 + yW_2370 4 * rowA 6 0 4 + yW_2370 5 * rowA 6 0 5 + yW_2370 6 * rowA 6 0 6 + yW_2370 7 * rowA 6 0 7 + yW_2370 8 * rowA 6 0 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 6 0 = (-5 : ℚ) / 16 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_6_1 :
    yW_2370 0 * rowA 6 1 0 + yW_2370 1 * rowA 6 1 1 + yW_2370 2 * rowA 6 1 2 + yW_2370 3 * rowA 6 1 3 + yW_2370 4 * rowA 6 1 4 + yW_2370 5 * rowA 6 1 5 + yW_2370 6 * rowA 6 1 6 + yW_2370 7 * rowA 6 1 7 + yW_2370 8 * rowA 6 1 8 ≤ db_2370 6 1 := by
  have hleft : yW_2370 0 * rowA 6 1 0 + yW_2370 1 * rowA 6 1 1 + yW_2370 2 * rowA 6 1 2 + yW_2370 3 * rowA 6 1 3 + yW_2370 4 * rowA 6 1 4 + yW_2370 5 * rowA 6 1 5 + yW_2370 6 * rowA 6 1 6 + yW_2370 7 * rowA 6 1 7 + yW_2370 8 * rowA 6 1 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 6 1 = (-5 : ℚ) / 16 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_6_2 :
    yW_2370 0 * rowA 6 2 0 + yW_2370 1 * rowA 6 2 1 + yW_2370 2 * rowA 6 2 2 + yW_2370 3 * rowA 6 2 3 + yW_2370 4 * rowA 6 2 4 + yW_2370 5 * rowA 6 2 5 + yW_2370 6 * rowA 6 2 6 + yW_2370 7 * rowA 6 2 7 + yW_2370 8 * rowA 6 2 8 ≤ db_2370 6 2 := by
  have hleft : yW_2370 0 * rowA 6 2 0 + yW_2370 1 * rowA 6 2 1 + yW_2370 2 * rowA 6 2 2 + yW_2370 3 * rowA 6 2 3 + yW_2370 4 * rowA 6 2 4 + yW_2370 5 * rowA 6 2 5 + yW_2370 6 * rowA 6 2 6 + yW_2370 7 * rowA 6 2 7 + yW_2370 8 * rowA 6 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 6 2 = (-5 : ℚ) / 16 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_6_3 :
    yW_2370 0 * rowA 6 3 0 + yW_2370 1 * rowA 6 3 1 + yW_2370 2 * rowA 6 3 2 + yW_2370 3 * rowA 6 3 3 + yW_2370 4 * rowA 6 3 4 + yW_2370 5 * rowA 6 3 5 + yW_2370 6 * rowA 6 3 6 + yW_2370 7 * rowA 6 3 7 + yW_2370 8 * rowA 6 3 8 ≤ db_2370 6 3 := by
  have hleft : yW_2370 0 * rowA 6 3 0 + yW_2370 1 * rowA 6 3 1 + yW_2370 2 * rowA 6 3 2 + yW_2370 3 * rowA 6 3 3 + yW_2370 4 * rowA 6 3 4 + yW_2370 5 * rowA 6 3 5 + yW_2370 6 * rowA 6 3 6 + yW_2370 7 * rowA 6 3 7 + yW_2370 8 * rowA 6 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 6 3 = (-5 : ℚ) / 16 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_6_4 :
    yW_2370 0 * rowA 6 4 0 + yW_2370 1 * rowA 6 4 1 + yW_2370 2 * rowA 6 4 2 + yW_2370 3 * rowA 6 4 3 + yW_2370 4 * rowA 6 4 4 + yW_2370 5 * rowA 6 4 5 + yW_2370 6 * rowA 6 4 6 + yW_2370 7 * rowA 6 4 7 + yW_2370 8 * rowA 6 4 8 ≤ db_2370 6 4 := by
  have hleft : yW_2370 0 * rowA 6 4 0 + yW_2370 1 * rowA 6 4 1 + yW_2370 2 * rowA 6 4 2 + yW_2370 3 * rowA 6 4 3 + yW_2370 4 * rowA 6 4 4 + yW_2370 5 * rowA 6 4 5 + yW_2370 6 * rowA 6 4 6 + yW_2370 7 * rowA 6 4 7 + yW_2370 8 * rowA 6 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 6 4 = (-1 : ℚ) / 16 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_6_5 :
    yW_2370 0 * rowA 6 5 0 + yW_2370 1 * rowA 6 5 1 + yW_2370 2 * rowA 6 5 2 + yW_2370 3 * rowA 6 5 3 + yW_2370 4 * rowA 6 5 4 + yW_2370 5 * rowA 6 5 5 + yW_2370 6 * rowA 6 5 6 + yW_2370 7 * rowA 6 5 7 + yW_2370 8 * rowA 6 5 8 ≤ db_2370 6 5 := by
  have hleft : yW_2370 0 * rowA 6 5 0 + yW_2370 1 * rowA 6 5 1 + yW_2370 2 * rowA 6 5 2 + yW_2370 3 * rowA 6 5 3 + yW_2370 4 * rowA 6 5 4 + yW_2370 5 * rowA 6 5 5 + yW_2370 6 * rowA 6 5 6 + yW_2370 7 * rowA 6 5 7 + yW_2370 8 * rowA 6 5 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 6 5 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_6_6 :
    yW_2370 0 * rowA 6 6 0 + yW_2370 1 * rowA 6 6 1 + yW_2370 2 * rowA 6 6 2 + yW_2370 3 * rowA 6 6 3 + yW_2370 4 * rowA 6 6 4 + yW_2370 5 * rowA 6 6 5 + yW_2370 6 * rowA 6 6 6 + yW_2370 7 * rowA 6 6 7 + yW_2370 8 * rowA 6 6 8 ≤ db_2370 6 6 := by
  have hleft : yW_2370 0 * rowA 6 6 0 + yW_2370 1 * rowA 6 6 1 + yW_2370 2 * rowA 6 6 2 + yW_2370 3 * rowA 6 6 3 + yW_2370 4 * rowA 6 6 4 + yW_2370 5 * rowA 6 6 5 + yW_2370 6 * rowA 6 6 6 + yW_2370 7 * rowA 6 6 7 + yW_2370 8 * rowA 6 6 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 6 6 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_6_7 :
    yW_2370 0 * rowA 6 7 0 + yW_2370 1 * rowA 6 7 1 + yW_2370 2 * rowA 6 7 2 + yW_2370 3 * rowA 6 7 3 + yW_2370 4 * rowA 6 7 4 + yW_2370 5 * rowA 6 7 5 + yW_2370 6 * rowA 6 7 6 + yW_2370 7 * rowA 6 7 7 + yW_2370 8 * rowA 6 7 8 ≤ db_2370 6 7 := by
  have hleft : yW_2370 0 * rowA 6 7 0 + yW_2370 1 * rowA 6 7 1 + yW_2370 2 * rowA 6 7 2 + yW_2370 3 * rowA 6 7 3 + yW_2370 4 * rowA 6 7 4 + yW_2370 5 * rowA 6 7 5 + yW_2370 6 * rowA 6 7 6 + yW_2370 7 * rowA 6 7 7 + yW_2370 8 * rowA 6 7 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 6 7 = (5 : ℚ) / 16 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_6_8 :
    yW_2370 0 * rowA 6 8 0 + yW_2370 1 * rowA 6 8 1 + yW_2370 2 * rowA 6 8 2 + yW_2370 3 * rowA 6 8 3 + yW_2370 4 * rowA 6 8 4 + yW_2370 5 * rowA 6 8 5 + yW_2370 6 * rowA 6 8 6 + yW_2370 7 * rowA 6 8 7 + yW_2370 8 * rowA 6 8 8 ≤ db_2370 6 8 := by
  have hleft : yW_2370 0 * rowA 6 8 0 + yW_2370 1 * rowA 6 8 1 + yW_2370 2 * rowA 6 8 2 + yW_2370 3 * rowA 6 8 3 + yW_2370 4 * rowA 6 8 4 + yW_2370 5 * rowA 6 8 5 + yW_2370 6 * rowA 6 8 6 + yW_2370 7 * rowA 6 8 7 + yW_2370 8 * rowA 6 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 6 8 = (5 : ℚ) / 16 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_6_9 :
    yW_2370 0 * rowA 6 9 0 + yW_2370 1 * rowA 6 9 1 + yW_2370 2 * rowA 6 9 2 + yW_2370 3 * rowA 6 9 3 + yW_2370 4 * rowA 6 9 4 + yW_2370 5 * rowA 6 9 5 + yW_2370 6 * rowA 6 9 6 + yW_2370 7 * rowA 6 9 7 + yW_2370 8 * rowA 6 9 8 ≤ db_2370 6 9 := by
  have hleft : yW_2370 0 * rowA 6 9 0 + yW_2370 1 * rowA 6 9 1 + yW_2370 2 * rowA 6 9 2 + yW_2370 3 * rowA 6 9 3 + yW_2370 4 * rowA 6 9 4 + yW_2370 5 * rowA 6 9 5 + yW_2370 6 * rowA 6 9 6 + yW_2370 7 * rowA 6 9 7 + yW_2370 8 * rowA 6 9 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 6 9 = (11 : ℚ) / 16 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_7_0 :
    yW_2370 0 * rowA 7 0 0 + yW_2370 1 * rowA 7 0 1 + yW_2370 2 * rowA 7 0 2 + yW_2370 3 * rowA 7 0 3 + yW_2370 4 * rowA 7 0 4 + yW_2370 5 * rowA 7 0 5 + yW_2370 6 * rowA 7 0 6 + yW_2370 7 * rowA 7 0 7 + yW_2370 8 * rowA 7 0 8 ≤ db_2370 7 0 := by
  have hleft : yW_2370 0 * rowA 7 0 0 + yW_2370 1 * rowA 7 0 1 + yW_2370 2 * rowA 7 0 2 + yW_2370 3 * rowA 7 0 3 + yW_2370 4 * rowA 7 0 4 + yW_2370 5 * rowA 7 0 5 + yW_2370 6 * rowA 7 0 6 + yW_2370 7 * rowA 7 0 7 + yW_2370 8 * rowA 7 0 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 7 0 = (-1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_7_1 :
    yW_2370 0 * rowA 7 1 0 + yW_2370 1 * rowA 7 1 1 + yW_2370 2 * rowA 7 1 2 + yW_2370 3 * rowA 7 1 3 + yW_2370 4 * rowA 7 1 4 + yW_2370 5 * rowA 7 1 5 + yW_2370 6 * rowA 7 1 6 + yW_2370 7 * rowA 7 1 7 + yW_2370 8 * rowA 7 1 8 ≤ db_2370 7 1 := by
  have hleft : yW_2370 0 * rowA 7 1 0 + yW_2370 1 * rowA 7 1 1 + yW_2370 2 * rowA 7 1 2 + yW_2370 3 * rowA 7 1 3 + yW_2370 4 * rowA 7 1 4 + yW_2370 5 * rowA 7 1 5 + yW_2370 6 * rowA 7 1 6 + yW_2370 7 * rowA 7 1 7 + yW_2370 8 * rowA 7 1 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 7 1 = (-1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_7_2 :
    yW_2370 0 * rowA 7 2 0 + yW_2370 1 * rowA 7 2 1 + yW_2370 2 * rowA 7 2 2 + yW_2370 3 * rowA 7 2 3 + yW_2370 4 * rowA 7 2 4 + yW_2370 5 * rowA 7 2 5 + yW_2370 6 * rowA 7 2 6 + yW_2370 7 * rowA 7 2 7 + yW_2370 8 * rowA 7 2 8 ≤ db_2370 7 2 := by
  have hleft : yW_2370 0 * rowA 7 2 0 + yW_2370 1 * rowA 7 2 1 + yW_2370 2 * rowA 7 2 2 + yW_2370 3 * rowA 7 2 3 + yW_2370 4 * rowA 7 2 4 + yW_2370 5 * rowA 7 2 5 + yW_2370 6 * rowA 7 2 6 + yW_2370 7 * rowA 7 2 7 + yW_2370 8 * rowA 7 2 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 7 2 = (-1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_7_3 :
    yW_2370 0 * rowA 7 3 0 + yW_2370 1 * rowA 7 3 1 + yW_2370 2 * rowA 7 3 2 + yW_2370 3 * rowA 7 3 3 + yW_2370 4 * rowA 7 3 4 + yW_2370 5 * rowA 7 3 5 + yW_2370 6 * rowA 7 3 6 + yW_2370 7 * rowA 7 3 7 + yW_2370 8 * rowA 7 3 8 ≤ db_2370 7 3 := by
  have hleft : yW_2370 0 * rowA 7 3 0 + yW_2370 1 * rowA 7 3 1 + yW_2370 2 * rowA 7 3 2 + yW_2370 3 * rowA 7 3 3 + yW_2370 4 * rowA 7 3 4 + yW_2370 5 * rowA 7 3 5 + yW_2370 6 * rowA 7 3 6 + yW_2370 7 * rowA 7 3 7 + yW_2370 8 * rowA 7 3 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 7 3 = (-1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_7_4 :
    yW_2370 0 * rowA 7 4 0 + yW_2370 1 * rowA 7 4 1 + yW_2370 2 * rowA 7 4 2 + yW_2370 3 * rowA 7 4 3 + yW_2370 4 * rowA 7 4 4 + yW_2370 5 * rowA 7 4 5 + yW_2370 6 * rowA 7 4 6 + yW_2370 7 * rowA 7 4 7 + yW_2370 8 * rowA 7 4 8 ≤ db_2370 7 4 := by
  have hleft : yW_2370 0 * rowA 7 4 0 + yW_2370 1 * rowA 7 4 1 + yW_2370 2 * rowA 7 4 2 + yW_2370 3 * rowA 7 4 3 + yW_2370 4 * rowA 7 4 4 + yW_2370 5 * rowA 7 4 5 + yW_2370 6 * rowA 7 4 6 + yW_2370 7 * rowA 7 4 7 + yW_2370 8 * rowA 7 4 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 7 4 = (-1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_7_5 :
    yW_2370 0 * rowA 7 5 0 + yW_2370 1 * rowA 7 5 1 + yW_2370 2 * rowA 7 5 2 + yW_2370 3 * rowA 7 5 3 + yW_2370 4 * rowA 7 5 4 + yW_2370 5 * rowA 7 5 5 + yW_2370 6 * rowA 7 5 6 + yW_2370 7 * rowA 7 5 7 + yW_2370 8 * rowA 7 5 8 ≤ db_2370 7 5 := by
  have hleft : yW_2370 0 * rowA 7 5 0 + yW_2370 1 * rowA 7 5 1 + yW_2370 2 * rowA 7 5 2 + yW_2370 3 * rowA 7 5 3 + yW_2370 4 * rowA 7 5 4 + yW_2370 5 * rowA 7 5 5 + yW_2370 6 * rowA 7 5 6 + yW_2370 7 * rowA 7 5 7 + yW_2370 8 * rowA 7 5 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 7 5 = (-1 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_7_6 :
    yW_2370 0 * rowA 7 6 0 + yW_2370 1 * rowA 7 6 1 + yW_2370 2 * rowA 7 6 2 + yW_2370 3 * rowA 7 6 3 + yW_2370 4 * rowA 7 6 4 + yW_2370 5 * rowA 7 6 5 + yW_2370 6 * rowA 7 6 6 + yW_2370 7 * rowA 7 6 7 + yW_2370 8 * rowA 7 6 8 ≤ db_2370 7 6 := by
  have hleft : yW_2370 0 * rowA 7 6 0 + yW_2370 1 * rowA 7 6 1 + yW_2370 2 * rowA 7 6 2 + yW_2370 3 * rowA 7 6 3 + yW_2370 4 * rowA 7 6 4 + yW_2370 5 * rowA 7 6 5 + yW_2370 6 * rowA 7 6 6 + yW_2370 7 * rowA 7 6 7 + yW_2370 8 * rowA 7 6 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 7 6 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_7_7 :
    yW_2370 0 * rowA 7 7 0 + yW_2370 1 * rowA 7 7 1 + yW_2370 2 * rowA 7 7 2 + yW_2370 3 * rowA 7 7 3 + yW_2370 4 * rowA 7 7 4 + yW_2370 5 * rowA 7 7 5 + yW_2370 6 * rowA 7 7 6 + yW_2370 7 * rowA 7 7 7 + yW_2370 8 * rowA 7 7 8 ≤ db_2370 7 7 := by
  have hleft : yW_2370 0 * rowA 7 7 0 + yW_2370 1 * rowA 7 7 1 + yW_2370 2 * rowA 7 7 2 + yW_2370 3 * rowA 7 7 3 + yW_2370 4 * rowA 7 7 4 + yW_2370 5 * rowA 7 7 5 + yW_2370 6 * rowA 7 7 6 + yW_2370 7 * rowA 7 7 7 + yW_2370 8 * rowA 7 7 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 7 7 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_7_8 :
    yW_2370 0 * rowA 7 8 0 + yW_2370 1 * rowA 7 8 1 + yW_2370 2 * rowA 7 8 2 + yW_2370 3 * rowA 7 8 3 + yW_2370 4 * rowA 7 8 4 + yW_2370 5 * rowA 7 8 5 + yW_2370 6 * rowA 7 8 6 + yW_2370 7 * rowA 7 8 7 + yW_2370 8 * rowA 7 8 8 ≤ db_2370 7 8 := by
  have hleft : yW_2370 0 * rowA 7 8 0 + yW_2370 1 * rowA 7 8 1 + yW_2370 2 * rowA 7 8 2 + yW_2370 3 * rowA 7 8 3 + yW_2370 4 * rowA 7 8 4 + yW_2370 5 * rowA 7 8 5 + yW_2370 6 * rowA 7 8 6 + yW_2370 7 * rowA 7 8 7 + yW_2370 8 * rowA 7 8 8 = (1 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 7 8 = (1 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_7_9 :
    yW_2370 0 * rowA 7 9 0 + yW_2370 1 * rowA 7 9 1 + yW_2370 2 * rowA 7 9 2 + yW_2370 3 * rowA 7 9 3 + yW_2370 4 * rowA 7 9 4 + yW_2370 5 * rowA 7 9 5 + yW_2370 6 * rowA 7 9 6 + yW_2370 7 * rowA 7 9 7 + yW_2370 8 * rowA 7 9 8 ≤ db_2370 7 9 := by
  have hleft : yW_2370 0 * rowA 7 9 0 + yW_2370 1 * rowA 7 9 1 + yW_2370 2 * rowA 7 9 2 + yW_2370 3 * rowA 7 9 3 + yW_2370 4 * rowA 7 9 4 + yW_2370 5 * rowA 7 9 5 + yW_2370 6 * rowA 7 9 6 + yW_2370 7 * rowA 7 9 7 + yW_2370 8 * rowA 7 9 8 = (1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 7 9 = (1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_8_0 :
    yW_2370 0 * rowA 8 0 0 + yW_2370 1 * rowA 8 0 1 + yW_2370 2 * rowA 8 0 2 + yW_2370 3 * rowA 8 0 3 + yW_2370 4 * rowA 8 0 4 + yW_2370 5 * rowA 8 0 5 + yW_2370 6 * rowA 8 0 6 + yW_2370 7 * rowA 8 0 7 + yW_2370 8 * rowA 8 0 8 ≤ db_2370 8 0 := by
  have hleft : yW_2370 0 * rowA 8 0 0 + yW_2370 1 * rowA 8 0 1 + yW_2370 2 * rowA 8 0 2 + yW_2370 3 * rowA 8 0 3 + yW_2370 4 * rowA 8 0 4 + yW_2370 5 * rowA 8 0 5 + yW_2370 6 * rowA 8 0 6 + yW_2370 7 * rowA 8 0 7 + yW_2370 8 * rowA 8 0 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 8 0 = (-5 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_8_1 :
    yW_2370 0 * rowA 8 1 0 + yW_2370 1 * rowA 8 1 1 + yW_2370 2 * rowA 8 1 2 + yW_2370 3 * rowA 8 1 3 + yW_2370 4 * rowA 8 1 4 + yW_2370 5 * rowA 8 1 5 + yW_2370 6 * rowA 8 1 6 + yW_2370 7 * rowA 8 1 7 + yW_2370 8 * rowA 8 1 8 ≤ db_2370 8 1 := by
  have hleft : yW_2370 0 * rowA 8 1 0 + yW_2370 1 * rowA 8 1 1 + yW_2370 2 * rowA 8 1 2 + yW_2370 3 * rowA 8 1 3 + yW_2370 4 * rowA 8 1 4 + yW_2370 5 * rowA 8 1 5 + yW_2370 6 * rowA 8 1 6 + yW_2370 7 * rowA 8 1 7 + yW_2370 8 * rowA 8 1 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 8 1 = (-1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_8_2 :
    yW_2370 0 * rowA 8 2 0 + yW_2370 1 * rowA 8 2 1 + yW_2370 2 * rowA 8 2 2 + yW_2370 3 * rowA 8 2 3 + yW_2370 4 * rowA 8 2 4 + yW_2370 5 * rowA 8 2 5 + yW_2370 6 * rowA 8 2 6 + yW_2370 7 * rowA 8 2 7 + yW_2370 8 * rowA 8 2 8 ≤ db_2370 8 2 := by
  have hleft : yW_2370 0 * rowA 8 2 0 + yW_2370 1 * rowA 8 2 1 + yW_2370 2 * rowA 8 2 2 + yW_2370 3 * rowA 8 2 3 + yW_2370 4 * rowA 8 2 4 + yW_2370 5 * rowA 8 2 5 + yW_2370 6 * rowA 8 2 6 + yW_2370 7 * rowA 8 2 7 + yW_2370 8 * rowA 8 2 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 8 2 = (-1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_8_3 :
    yW_2370 0 * rowA 8 3 0 + yW_2370 1 * rowA 8 3 1 + yW_2370 2 * rowA 8 3 2 + yW_2370 3 * rowA 8 3 3 + yW_2370 4 * rowA 8 3 4 + yW_2370 5 * rowA 8 3 5 + yW_2370 6 * rowA 8 3 6 + yW_2370 7 * rowA 8 3 7 + yW_2370 8 * rowA 8 3 8 ≤ db_2370 8 3 := by
  have hleft : yW_2370 0 * rowA 8 3 0 + yW_2370 1 * rowA 8 3 1 + yW_2370 2 * rowA 8 3 2 + yW_2370 3 * rowA 8 3 3 + yW_2370 4 * rowA 8 3 4 + yW_2370 5 * rowA 8 3 5 + yW_2370 6 * rowA 8 3 6 + yW_2370 7 * rowA 8 3 7 + yW_2370 8 * rowA 8 3 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 8 3 = (-1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_8_4 :
    yW_2370 0 * rowA 8 4 0 + yW_2370 1 * rowA 8 4 1 + yW_2370 2 * rowA 8 4 2 + yW_2370 3 * rowA 8 4 3 + yW_2370 4 * rowA 8 4 4 + yW_2370 5 * rowA 8 4 5 + yW_2370 6 * rowA 8 4 6 + yW_2370 7 * rowA 8 4 7 + yW_2370 8 * rowA 8 4 8 ≤ db_2370 8 4 := by
  have hleft : yW_2370 0 * rowA 8 4 0 + yW_2370 1 * rowA 8 4 1 + yW_2370 2 * rowA 8 4 2 + yW_2370 3 * rowA 8 4 3 + yW_2370 4 * rowA 8 4 4 + yW_2370 5 * rowA 8 4 5 + yW_2370 6 * rowA 8 4 6 + yW_2370 7 * rowA 8 4 7 + yW_2370 8 * rowA 8 4 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 8 4 = (-3 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_8_5 :
    yW_2370 0 * rowA 8 5 0 + yW_2370 1 * rowA 8 5 1 + yW_2370 2 * rowA 8 5 2 + yW_2370 3 * rowA 8 5 3 + yW_2370 4 * rowA 8 5 4 + yW_2370 5 * rowA 8 5 5 + yW_2370 6 * rowA 8 5 6 + yW_2370 7 * rowA 8 5 7 + yW_2370 8 * rowA 8 5 8 ≤ db_2370 8 5 := by
  have hleft : yW_2370 0 * rowA 8 5 0 + yW_2370 1 * rowA 8 5 1 + yW_2370 2 * rowA 8 5 2 + yW_2370 3 * rowA 8 5 3 + yW_2370 4 * rowA 8 5 4 + yW_2370 5 * rowA 8 5 5 + yW_2370 6 * rowA 8 5 6 + yW_2370 7 * rowA 8 5 7 + yW_2370 8 * rowA 8 5 8 = (-1 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 8 5 = (-1 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_8_6 :
    yW_2370 0 * rowA 8 6 0 + yW_2370 1 * rowA 8 6 1 + yW_2370 2 * rowA 8 6 2 + yW_2370 3 * rowA 8 6 3 + yW_2370 4 * rowA 8 6 4 + yW_2370 5 * rowA 8 6 5 + yW_2370 6 * rowA 8 6 6 + yW_2370 7 * rowA 8 6 7 + yW_2370 8 * rowA 8 6 8 ≤ db_2370 8 6 := by
  have hleft : yW_2370 0 * rowA 8 6 0 + yW_2370 1 * rowA 8 6 1 + yW_2370 2 * rowA 8 6 2 + yW_2370 3 * rowA 8 6 3 + yW_2370 4 * rowA 8 6 4 + yW_2370 5 * rowA 8 6 5 + yW_2370 6 * rowA 8 6 6 + yW_2370 7 * rowA 8 6 7 + yW_2370 8 * rowA 8 6 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 8 6 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_8_7 :
    yW_2370 0 * rowA 8 7 0 + yW_2370 1 * rowA 8 7 1 + yW_2370 2 * rowA 8 7 2 + yW_2370 3 * rowA 8 7 3 + yW_2370 4 * rowA 8 7 4 + yW_2370 5 * rowA 8 7 5 + yW_2370 6 * rowA 8 7 6 + yW_2370 7 * rowA 8 7 7 + yW_2370 8 * rowA 8 7 8 ≤ db_2370 8 7 := by
  have hleft : yW_2370 0 * rowA 8 7 0 + yW_2370 1 * rowA 8 7 1 + yW_2370 2 * rowA 8 7 2 + yW_2370 3 * rowA 8 7 3 + yW_2370 4 * rowA 8 7 4 + yW_2370 5 * rowA 8 7 5 + yW_2370 6 * rowA 8 7 6 + yW_2370 7 * rowA 8 7 7 + yW_2370 8 * rowA 8 7 8 = (-1 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 8 7 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_8_8 :
    yW_2370 0 * rowA 8 8 0 + yW_2370 1 * rowA 8 8 1 + yW_2370 2 * rowA 8 8 2 + yW_2370 3 * rowA 8 8 3 + yW_2370 4 * rowA 8 8 4 + yW_2370 5 * rowA 8 8 5 + yW_2370 6 * rowA 8 8 6 + yW_2370 7 * rowA 8 8 7 + yW_2370 8 * rowA 8 8 8 ≤ db_2370 8 8 := by
  have hleft : yW_2370 0 * rowA 8 8 0 + yW_2370 1 * rowA 8 8 1 + yW_2370 2 * rowA 8 8 2 + yW_2370 3 * rowA 8 8 3 + yW_2370 4 * rowA 8 8 4 + yW_2370 5 * rowA 8 8 5 + yW_2370 6 * rowA 8 8 6 + yW_2370 7 * rowA 8 8 7 + yW_2370 8 * rowA 8 8 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 8 8 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_8_9 :
    yW_2370 0 * rowA 8 9 0 + yW_2370 1 * rowA 8 9 1 + yW_2370 2 * rowA 8 9 2 + yW_2370 3 * rowA 8 9 3 + yW_2370 4 * rowA 8 9 4 + yW_2370 5 * rowA 8 9 5 + yW_2370 6 * rowA 8 9 6 + yW_2370 7 * rowA 8 9 7 + yW_2370 8 * rowA 8 9 8 ≤ db_2370 8 9 := by
  have hleft : yW_2370 0 * rowA 8 9 0 + yW_2370 1 * rowA 8 9 1 + yW_2370 2 * rowA 8 9 2 + yW_2370 3 * rowA 8 9 3 + yW_2370 4 * rowA 8 9 4 + yW_2370 5 * rowA 8 9 5 + yW_2370 6 * rowA 8 9 6 + yW_2370 7 * rowA 8 9 7 + yW_2370 8 * rowA 8 9 8 = (3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 8 9 = (3 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_9_0 :
    yW_2370 0 * rowA 9 0 0 + yW_2370 1 * rowA 9 0 1 + yW_2370 2 * rowA 9 0 2 + yW_2370 3 * rowA 9 0 3 + yW_2370 4 * rowA 9 0 4 + yW_2370 5 * rowA 9 0 5 + yW_2370 6 * rowA 9 0 6 + yW_2370 7 * rowA 9 0 7 + yW_2370 8 * rowA 9 0 8 ≤ db_2370 9 0 := by
  have hleft : yW_2370 0 * rowA 9 0 0 + yW_2370 1 * rowA 9 0 1 + yW_2370 2 * rowA 9 0 2 + yW_2370 3 * rowA 9 0 3 + yW_2370 4 * rowA 9 0 4 + yW_2370 5 * rowA 9 0 5 + yW_2370 6 * rowA 9 0 6 + yW_2370 7 * rowA 9 0 7 + yW_2370 8 * rowA 9 0 8 = (-1 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 9 0 = (-1 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_9_1 :
    yW_2370 0 * rowA 9 1 0 + yW_2370 1 * rowA 9 1 1 + yW_2370 2 * rowA 9 1 2 + yW_2370 3 * rowA 9 1 3 + yW_2370 4 * rowA 9 1 4 + yW_2370 5 * rowA 9 1 5 + yW_2370 6 * rowA 9 1 6 + yW_2370 7 * rowA 9 1 7 + yW_2370 8 * rowA 9 1 8 ≤ db_2370 9 1 := by
  have hleft : yW_2370 0 * rowA 9 1 0 + yW_2370 1 * rowA 9 1 1 + yW_2370 2 * rowA 9 1 2 + yW_2370 3 * rowA 9 1 3 + yW_2370 4 * rowA 9 1 4 + yW_2370 5 * rowA 9 1 5 + yW_2370 6 * rowA 9 1 6 + yW_2370 7 * rowA 9 1 7 + yW_2370 8 * rowA 9 1 8 = (-1 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 9 1 = (-3 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_9_2 :
    yW_2370 0 * rowA 9 2 0 + yW_2370 1 * rowA 9 2 1 + yW_2370 2 * rowA 9 2 2 + yW_2370 3 * rowA 9 2 3 + yW_2370 4 * rowA 9 2 4 + yW_2370 5 * rowA 9 2 5 + yW_2370 6 * rowA 9 2 6 + yW_2370 7 * rowA 9 2 7 + yW_2370 8 * rowA 9 2 8 ≤ db_2370 9 2 := by
  have hleft : yW_2370 0 * rowA 9 2 0 + yW_2370 1 * rowA 9 2 1 + yW_2370 2 * rowA 9 2 2 + yW_2370 3 * rowA 9 2 3 + yW_2370 4 * rowA 9 2 4 + yW_2370 5 * rowA 9 2 5 + yW_2370 6 * rowA 9 2 6 + yW_2370 7 * rowA 9 2 7 + yW_2370 8 * rowA 9 2 8 = (-1 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 9 2 = (-3 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_9_3 :
    yW_2370 0 * rowA 9 3 0 + yW_2370 1 * rowA 9 3 1 + yW_2370 2 * rowA 9 3 2 + yW_2370 3 * rowA 9 3 3 + yW_2370 4 * rowA 9 3 4 + yW_2370 5 * rowA 9 3 5 + yW_2370 6 * rowA 9 3 6 + yW_2370 7 * rowA 9 3 7 + yW_2370 8 * rowA 9 3 8 ≤ db_2370 9 3 := by
  have hleft : yW_2370 0 * rowA 9 3 0 + yW_2370 1 * rowA 9 3 1 + yW_2370 2 * rowA 9 3 2 + yW_2370 3 * rowA 9 3 3 + yW_2370 4 * rowA 9 3 4 + yW_2370 5 * rowA 9 3 5 + yW_2370 6 * rowA 9 3 6 + yW_2370 7 * rowA 9 3 7 + yW_2370 8 * rowA 9 3 8 = (-1 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 9 3 = (-3 : ℚ) / 4 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_9_4 :
    yW_2370 0 * rowA 9 4 0 + yW_2370 1 * rowA 9 4 1 + yW_2370 2 * rowA 9 4 2 + yW_2370 3 * rowA 9 4 3 + yW_2370 4 * rowA 9 4 4 + yW_2370 5 * rowA 9 4 5 + yW_2370 6 * rowA 9 4 6 + yW_2370 7 * rowA 9 4 7 + yW_2370 8 * rowA 9 4 8 ≤ db_2370 9 4 := by
  have hleft : yW_2370 0 * rowA 9 4 0 + yW_2370 1 * rowA 9 4 1 + yW_2370 2 * rowA 9 4 2 + yW_2370 3 * rowA 9 4 3 + yW_2370 4 * rowA 9 4 4 + yW_2370 5 * rowA 9 4 5 + yW_2370 6 * rowA 9 4 6 + yW_2370 7 * rowA 9 4 7 + yW_2370 8 * rowA 9 4 8 = (-3 : ℚ) / 4 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 9 4 = (-5 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_9_5 :
    yW_2370 0 * rowA 9 5 0 + yW_2370 1 * rowA 9 5 1 + yW_2370 2 * rowA 9 5 2 + yW_2370 3 * rowA 9 5 3 + yW_2370 4 * rowA 9 5 4 + yW_2370 5 * rowA 9 5 5 + yW_2370 6 * rowA 9 5 6 + yW_2370 7 * rowA 9 5 7 + yW_2370 8 * rowA 9 5 8 ≤ db_2370 9 5 := by
  have hleft : yW_2370 0 * rowA 9 5 0 + yW_2370 1 * rowA 9 5 1 + yW_2370 2 * rowA 9 5 2 + yW_2370 3 * rowA 9 5 3 + yW_2370 4 * rowA 9 5 4 + yW_2370 5 * rowA 9 5 5 + yW_2370 6 * rowA 9 5 6 + yW_2370 7 * rowA 9 5 7 + yW_2370 8 * rowA 9 5 8 = (-5 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 9 5 = (-1 : ℚ) / 2 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_9_6 :
    yW_2370 0 * rowA 9 6 0 + yW_2370 1 * rowA 9 6 1 + yW_2370 2 * rowA 9 6 2 + yW_2370 3 * rowA 9 6 3 + yW_2370 4 * rowA 9 6 4 + yW_2370 5 * rowA 9 6 5 + yW_2370 6 * rowA 9 6 6 + yW_2370 7 * rowA 9 6 7 + yW_2370 8 * rowA 9 6 8 ≤ db_2370 9 6 := by
  have hleft : yW_2370 0 * rowA 9 6 0 + yW_2370 1 * rowA 9 6 1 + yW_2370 2 * rowA 9 6 2 + yW_2370 3 * rowA 9 6 3 + yW_2370 4 * rowA 9 6 4 + yW_2370 5 * rowA 9 6 5 + yW_2370 6 * rowA 9 6 6 + yW_2370 7 * rowA 9 6 7 + yW_2370 8 * rowA 9 6 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 9 6 = (-3 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_9_7 :
    yW_2370 0 * rowA 9 7 0 + yW_2370 1 * rowA 9 7 1 + yW_2370 2 * rowA 9 7 2 + yW_2370 3 * rowA 9 7 3 + yW_2370 4 * rowA 9 7 4 + yW_2370 5 * rowA 9 7 5 + yW_2370 6 * rowA 9 7 6 + yW_2370 7 * rowA 9 7 7 + yW_2370 8 * rowA 9 7 8 ≤ db_2370 9 7 := by
  have hleft : yW_2370 0 * rowA 9 7 0 + yW_2370 1 * rowA 9 7 1 + yW_2370 2 * rowA 9 7 2 + yW_2370 3 * rowA 9 7 3 + yW_2370 4 * rowA 9 7 4 + yW_2370 5 * rowA 9 7 5 + yW_2370 6 * rowA 9 7 6 + yW_2370 7 * rowA 9 7 7 + yW_2370 8 * rowA 9 7 8 = (-1 : ℚ) / 2 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 9 7 = (-1 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_9_8 :
    yW_2370 0 * rowA 9 8 0 + yW_2370 1 * rowA 9 8 1 + yW_2370 2 * rowA 9 8 2 + yW_2370 3 * rowA 9 8 3 + yW_2370 4 * rowA 9 8 4 + yW_2370 5 * rowA 9 8 5 + yW_2370 6 * rowA 9 8 6 + yW_2370 7 * rowA 9 8 7 + yW_2370 8 * rowA 9 8 8 ≤ db_2370 9 8 := by
  have hleft : yW_2370 0 * rowA 9 8 0 + yW_2370 1 * rowA 9 8 1 + yW_2370 2 * rowA 9 8 2 + yW_2370 3 * rowA 9 8 3 + yW_2370 4 * rowA 9 8 4 + yW_2370 5 * rowA 9 8 5 + yW_2370 6 * rowA 9 8 6 + yW_2370 7 * rowA 9 8 7 + yW_2370 8 * rowA 9 8 8 = (-3 : ℚ) / 8 := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 9 8 = (-1 : ℚ) / 8 := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_9_9 :
    yW_2370 0 * rowA 9 9 0 + yW_2370 1 * rowA 9 9 1 + yW_2370 2 * rowA 9 9 2 + yW_2370 3 * rowA 9 9 3 + yW_2370 4 * rowA 9 9 4 + yW_2370 5 * rowA 9 9 5 + yW_2370 6 * rowA 9 9 6 + yW_2370 7 * rowA 9 9 7 + yW_2370 8 * rowA 9 9 8 ≤ db_2370 9 9 := by
  have hleft : yW_2370 0 * rowA 9 9 0 + yW_2370 1 * rowA 9 9 1 + yW_2370 2 * rowA 9 9 2 + yW_2370 3 * rowA 9 9 3 + yW_2370 4 * rowA 9 9 4 + yW_2370 5 * rowA 9 9 5 + yW_2370 6 * rowA 9 9 6 + yW_2370 7 * rowA 9 9 7 + yW_2370 8 * rowA 9 9 8 = (0 : ℚ) := by
    norm_num [yW_2370, rowA]
  have hright : db_2370 9 9 = (0 : ℚ) := by
    norm_num [db_2370, dbmVal_2370]
  rw [hleft, hright]
  norm_num

theorem row_cap_2370_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 0 j q) ≤ db_2370 0 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_0_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_0_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_0_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_0_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_0_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_0_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_0_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_0_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_0_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_0_9

theorem row_cap_2370_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 1 j q) ≤ db_2370 1 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_1_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_1_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_1_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_1_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_1_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_1_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_1_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_1_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_1_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_1_9

theorem row_cap_2370_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 2 j q) ≤ db_2370 2 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_2_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_2_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_2_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_2_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_2_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_2_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_2_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_2_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_2_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_2_9

theorem row_cap_2370_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 3 j q) ≤ db_2370 3 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_3_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_3_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_3_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_3_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_3_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_3_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_3_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_3_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_3_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_3_9

theorem row_cap_2370_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 4 j q) ≤ db_2370 4 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_4_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_4_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_4_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_4_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_4_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_4_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_4_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_4_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_4_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_4_9

theorem row_cap_2370_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 5 j q) ≤ db_2370 5 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_5_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_5_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_5_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_5_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_5_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_5_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_5_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_5_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_5_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_5_9

theorem row_cap_2370_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 6 j q) ≤ db_2370 6 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_6_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_6_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_6_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_6_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_6_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_6_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_6_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_6_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_6_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_6_9

theorem row_cap_2370_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 7 j q) ≤ db_2370 7 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_7_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_7_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_7_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_7_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_7_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_7_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_7_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_7_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_7_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_7_9

theorem row_cap_2370_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 8 j q) ≤ db_2370 8 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_8_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_8_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_8_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_8_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_8_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_8_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_8_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_8_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_8_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_8_9

theorem row_cap_2370_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 9 j q) ≤ db_2370 9 j := by
  fin_cases j <;>
    first
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_9_0
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_9_1
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_9_2
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_9_3
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_9_4
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_9_5
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_9_6
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_9_7
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_9_8
    | simpa only [Fin.sum_univ_succ, Fin.sum_univ_one, Finset.sum_empty] using row_cap_2370_9_9

theorem row_cap_2370 (i j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA i j q) ≤ db_2370 i j := by
  fin_cases i
  · exact row_cap_2370_0 j
  · exact row_cap_2370_1 j
  · exact row_cap_2370_2 j
  · exact row_cap_2370_3 j
  · exact row_cap_2370_4 j
  · exact row_cap_2370_5 j
  · exact row_cap_2370_6 j
  · exact row_cap_2370_7 j
  · exact row_cap_2370_8 j
  · exact row_cap_2370_9 j

end
end N11Formalization.FrozenCapWideFieldRowCaps

#check @N11Formalization.FrozenCapWideFieldRowCaps.row_cap_1409
#check @N11Formalization.FrozenCapWideFieldRowCaps.row_cap_2370
