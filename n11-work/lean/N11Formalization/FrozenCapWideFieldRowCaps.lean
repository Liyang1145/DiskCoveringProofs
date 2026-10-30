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

theorem row_cap_1409_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 0 j q) ≤ db_1409 0 j := by
  fin_cases j <;> norm_num [yW_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 1 j q) ≤ db_1409 1 j := by
  fin_cases j <;> norm_num [yW_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 2 j q) ≤ db_1409 2 j := by
  fin_cases j <;> norm_num [yW_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 3 j q) ≤ db_1409 3 j := by
  fin_cases j <;> norm_num [yW_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 4 j q) ≤ db_1409 4 j := by
  fin_cases j <;> norm_num [yW_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 5 j q) ≤ db_1409 5 j := by
  fin_cases j <;> norm_num [yW_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 6 j q) ≤ db_1409 6 j := by
  fin_cases j <;> norm_num [yW_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 7 j q) ≤ db_1409 7 j := by
  fin_cases j <;> norm_num [yW_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 8 j q) ≤ db_1409 8 j := by
  fin_cases j <;> norm_num [yW_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_1409 q * rowA 9 j q) ≤ db_1409 9 j := by
  fin_cases j <;> norm_num [yW_1409, rowA, db_1409, Fin.sum_univ_succ]

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

theorem row_cap_2337_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 0 j q) ≤ db_2337 0 j := by
  fin_cases j <;> norm_num [yW_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 1 j q) ≤ db_2337 1 j := by
  fin_cases j <;> norm_num [yW_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 2 j q) ≤ db_2337 2 j := by
  fin_cases j <;> norm_num [yW_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 3 j q) ≤ db_2337 3 j := by
  fin_cases j <;> norm_num [yW_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 4 j q) ≤ db_2337 4 j := by
  fin_cases j <;> norm_num [yW_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 5 j q) ≤ db_2337 5 j := by
  fin_cases j <;> norm_num [yW_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 6 j q) ≤ db_2337 6 j := by
  fin_cases j <;> norm_num [yW_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 7 j q) ≤ db_2337 7 j := by
  fin_cases j <;> norm_num [yW_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 8 j q) ≤ db_2337 8 j := by
  fin_cases j <;> norm_num [yW_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2337 q * rowA 9 j q) ≤ db_2337 9 j := by
  fin_cases j <;> norm_num [yW_2337, rowA, db_2337, Fin.sum_univ_succ]

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

theorem row_cap_2341_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 0 j q) ≤ db_2341 0 j := by
  fin_cases j <;> norm_num [yW_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 1 j q) ≤ db_2341 1 j := by
  fin_cases j <;> norm_num [yW_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 2 j q) ≤ db_2341 2 j := by
  fin_cases j <;> norm_num [yW_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 3 j q) ≤ db_2341 3 j := by
  fin_cases j <;> norm_num [yW_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 4 j q) ≤ db_2341 4 j := by
  fin_cases j <;> norm_num [yW_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 5 j q) ≤ db_2341 5 j := by
  fin_cases j <;> norm_num [yW_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 6 j q) ≤ db_2341 6 j := by
  fin_cases j <;> norm_num [yW_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 7 j q) ≤ db_2341 7 j := by
  fin_cases j <;> norm_num [yW_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 8 j q) ≤ db_2341 8 j := by
  fin_cases j <;> norm_num [yW_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2341 q * rowA 9 j q) ≤ db_2341 9 j := by
  fin_cases j <;> norm_num [yW_2341, rowA, db_2341, Fin.sum_univ_succ]

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

theorem row_cap_2356_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 0 j q) ≤ db_2356 0 j := by
  fin_cases j <;> norm_num [yW_2356, rowA, db_2356, Fin.sum_univ_succ]

theorem row_cap_2356_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 1 j q) ≤ db_2356 1 j := by
  fin_cases j <;> norm_num [yW_2356, rowA, db_2356, Fin.sum_univ_succ]

theorem row_cap_2356_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 2 j q) ≤ db_2356 2 j := by
  fin_cases j <;> norm_num [yW_2356, rowA, db_2356, Fin.sum_univ_succ]

theorem row_cap_2356_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 3 j q) ≤ db_2356 3 j := by
  fin_cases j <;> norm_num [yW_2356, rowA, db_2356, Fin.sum_univ_succ]

theorem row_cap_2356_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 4 j q) ≤ db_2356 4 j := by
  fin_cases j <;> norm_num [yW_2356, rowA, db_2356, Fin.sum_univ_succ]

theorem row_cap_2356_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 5 j q) ≤ db_2356 5 j := by
  fin_cases j <;> norm_num [yW_2356, rowA, db_2356, Fin.sum_univ_succ]

theorem row_cap_2356_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 6 j q) ≤ db_2356 6 j := by
  fin_cases j <;> norm_num [yW_2356, rowA, db_2356, Fin.sum_univ_succ]

theorem row_cap_2356_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 7 j q) ≤ db_2356 7 j := by
  fin_cases j <;> norm_num [yW_2356, rowA, db_2356, Fin.sum_univ_succ]

theorem row_cap_2356_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 8 j q) ≤ db_2356 8 j := by
  fin_cases j <;> norm_num [yW_2356, rowA, db_2356, Fin.sum_univ_succ]

theorem row_cap_2356_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2356 q * rowA 9 j q) ≤ db_2356 9 j := by
  fin_cases j <;> norm_num [yW_2356, rowA, db_2356, Fin.sum_univ_succ]

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

theorem row_cap_2360_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 0 j q) ≤ db_2360 0 j := by
  fin_cases j <;> norm_num [yW_2360, rowA, db_2360, Fin.sum_univ_succ]

theorem row_cap_2360_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 1 j q) ≤ db_2360 1 j := by
  fin_cases j <;> norm_num [yW_2360, rowA, db_2360, Fin.sum_univ_succ]

theorem row_cap_2360_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 2 j q) ≤ db_2360 2 j := by
  fin_cases j <;> norm_num [yW_2360, rowA, db_2360, Fin.sum_univ_succ]

theorem row_cap_2360_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 3 j q) ≤ db_2360 3 j := by
  fin_cases j <;> norm_num [yW_2360, rowA, db_2360, Fin.sum_univ_succ]

theorem row_cap_2360_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 4 j q) ≤ db_2360 4 j := by
  fin_cases j <;> norm_num [yW_2360, rowA, db_2360, Fin.sum_univ_succ]

theorem row_cap_2360_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 5 j q) ≤ db_2360 5 j := by
  fin_cases j <;> norm_num [yW_2360, rowA, db_2360, Fin.sum_univ_succ]

theorem row_cap_2360_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 6 j q) ≤ db_2360 6 j := by
  fin_cases j <;> norm_num [yW_2360, rowA, db_2360, Fin.sum_univ_succ]

theorem row_cap_2360_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 7 j q) ≤ db_2360 7 j := by
  fin_cases j <;> norm_num [yW_2360, rowA, db_2360, Fin.sum_univ_succ]

theorem row_cap_2360_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 8 j q) ≤ db_2360 8 j := by
  fin_cases j <;> norm_num [yW_2360, rowA, db_2360, Fin.sum_univ_succ]

theorem row_cap_2360_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2360 q * rowA 9 j q) ≤ db_2360 9 j := by
  fin_cases j <;> norm_num [yW_2360, rowA, db_2360, Fin.sum_univ_succ]

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

theorem row_cap_2368_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 0 j q) ≤ db_2368 0 j := by
  fin_cases j <;> norm_num [yW_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 1 j q) ≤ db_2368 1 j := by
  fin_cases j <;> norm_num [yW_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 2 j q) ≤ db_2368 2 j := by
  fin_cases j <;> norm_num [yW_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 3 j q) ≤ db_2368 3 j := by
  fin_cases j <;> norm_num [yW_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 4 j q) ≤ db_2368 4 j := by
  fin_cases j <;> norm_num [yW_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 5 j q) ≤ db_2368 5 j := by
  fin_cases j <;> norm_num [yW_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 6 j q) ≤ db_2368 6 j := by
  fin_cases j <;> norm_num [yW_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 7 j q) ≤ db_2368 7 j := by
  fin_cases j <;> norm_num [yW_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 8 j q) ≤ db_2368 8 j := by
  fin_cases j <;> norm_num [yW_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2368 q * rowA 9 j q) ≤ db_2368 9 j := by
  fin_cases j <;> norm_num [yW_2368, rowA, db_2368, Fin.sum_univ_succ]

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

theorem row_cap_2370_0 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 0 j q) ≤ db_2370 0 j := by
  fin_cases j <;> norm_num [yW_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 1 j q) ≤ db_2370 1 j := by
  fin_cases j <;> norm_num [yW_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 2 j q) ≤ db_2370 2 j := by
  fin_cases j <;> norm_num [yW_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 3 j q) ≤ db_2370 3 j := by
  fin_cases j <;> norm_num [yW_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 4 j q) ≤ db_2370 4 j := by
  fin_cases j <;> norm_num [yW_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 5 j q) ≤ db_2370 5 j := by
  fin_cases j <;> norm_num [yW_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 6 j q) ≤ db_2370 6 j := by
  fin_cases j <;> norm_num [yW_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 7 j q) ≤ db_2370 7 j := by
  fin_cases j <;> norm_num [yW_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 8 j q) ≤ db_2370 8 j := by
  fin_cases j <;> norm_num [yW_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9 (j : Fin 10) :
    (∑ q : Fin 9, yW_2370 q * rowA 9 j q) ≤ db_2370 9 j := by
  fin_cases j <;> norm_num [yW_2370, rowA, db_2370, Fin.sum_univ_succ]

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
