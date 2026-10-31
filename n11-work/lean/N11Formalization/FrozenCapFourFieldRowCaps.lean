import N11Formalization.FrozenCapFourFieldWitnesses
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Exact 100-pair row caps for the five corrected four-field witnesses.
Generated deterministically by `ops/lanes/C/emit_four_field_row_caps.py`. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFourFieldRowCaps
open Finset
open N11Formalization.FrozenCapFourFieldWitnesses
noncomputable section

def rowA (i j : Fin 10) (q : Fin 9) : ℚ :=
  (if q.val < j.val then 1 else 0) - (if q.val < i.val then 1 else 0)

def db_1409 : Fin 10 → Fin 10 → ℚ
  | ⟨0, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : ℚ) / 4
  | ⟨0, _⟩, ⟨2, _⟩ => (1 : ℚ) / 4
  | ⟨0, _⟩, ⟨3, _⟩ => (1 : ℚ) / 4
  | ⟨0, _⟩, ⟨4, _⟩ => (1 : ℚ) / 2
  | ⟨0, _⟩, ⟨5, _⟩ => (3 : ℚ) / 4
  | ⟨0, _⟩, ⟨6, _⟩ => (3 : ℚ) / 4
  | ⟨0, _⟩, ⟨7, _⟩ => (3 : ℚ) / 4
  | ⟨0, _⟩, ⟨8, _⟩ => (7 : ℚ) / 8
  | ⟨0, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨1, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨1, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨1, _⟩, ⟨2, _⟩ => (1 : ℚ) / 4
  | ⟨1, _⟩, ⟨3, _⟩ => (1 : ℚ) / 4
  | ⟨1, _⟩, ⟨4, _⟩ => (1 : ℚ) / 2
  | ⟨1, _⟩, ⟨5, _⟩ => (3 : ℚ) / 4
  | ⟨1, _⟩, ⟨6, _⟩ => (3 : ℚ) / 4
  | ⟨1, _⟩, ⟨7, _⟩ => (3 : ℚ) / 4
  | ⟨1, _⟩, ⟨8, _⟩ => (7 : ℚ) / 8
  | ⟨1, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨2, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨3, _⟩ => (1 : ℚ) / 4
  | ⟨2, _⟩, ⟨4, _⟩ => (1 : ℚ) / 2
  | ⟨2, _⟩, ⟨5, _⟩ => (3 : ℚ) / 4
  | ⟨2, _⟩, ⟨6, _⟩ => (3 : ℚ) / 4
  | ⟨2, _⟩, ⟨7, _⟩ => (3 : ℚ) / 4
  | ⟨2, _⟩, ⟨8, _⟩ => (7 : ℚ) / 8
  | ⟨2, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨3, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨3, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨3, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨3, _⟩, ⟨6, _⟩ => (1 : ℚ) / 2
  | ⟨3, _⟩, ⟨7, _⟩ => (1 : ℚ) / 2
  | ⟨3, _⟩, ⟨8, _⟩ => (5 : ℚ) / 8
  | ⟨3, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨4, _⟩, ⟨0, _⟩ => (-3 : ℚ) / 8
  | ⟨4, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 8
  | ⟨4, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 8
  | ⟨4, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 8
  | ⟨4, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨4, _⟩, ⟨5, _⟩ => (1 : ℚ) / 4
  | ⟨4, _⟩, ⟨6, _⟩ => (1 : ℚ) / 4
  | ⟨4, _⟩, ⟨7, _⟩ => (1 : ℚ) / 4
  | ⟨4, _⟩, ⟨8, _⟩ => (3 : ℚ) / 8
  | ⟨4, _⟩, ⟨9, _⟩ => (5 : ℚ) / 8
  | ⟨5, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 2
  | ⟨5, _⟩, ⟨1, _⟩ => (-3 : ℚ) / 8
  | ⟨5, _⟩, ⟨2, _⟩ => (-3 : ℚ) / 8
  | ⟨5, _⟩, ⟨3, _⟩ => (-3 : ℚ) / 8
  | ⟨5, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 8
  | ⟨5, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨6, _⟩ => (1 : ℚ) / 8
  | ⟨5, _⟩, ⟨7, _⟩ => (1 : ℚ) / 8
  | ⟨5, _⟩, ⟨8, _⟩ => (1 : ℚ) / 8
  | ⟨5, _⟩, ⟨9, _⟩ => (1 : ℚ) / 2
  | ⟨6, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 2
  | ⟨6, _⟩, ⟨1, _⟩ => (-3 : ℚ) / 8
  | ⟨6, _⟩, ⟨2, _⟩ => (-3 : ℚ) / 8
  | ⟨6, _⟩, ⟨3, _⟩ => (-3 : ℚ) / 8
  | ⟨6, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 8
  | ⟨6, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨7, _⟩ => (1 : ℚ) / 8
  | ⟨6, _⟩, ⟨8, _⟩ => (1 : ℚ) / 8
  | ⟨6, _⟩, ⟨9, _⟩ => (1 : ℚ) / 2
  | ⟨7, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨1, _⟩ => (-3 : ℚ) / 8
  | ⟨7, _⟩, ⟨2, _⟩ => (-3 : ℚ) / 8
  | ⟨7, _⟩, ⟨3, _⟩ => (-3 : ℚ) / 8
  | ⟨7, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 8
  | ⟨7, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨7, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨8, _⟩ => (1 : ℚ) / 8
  | ⟨7, _⟩, ⟨9, _⟩ => (1 : ℚ) / 2
  | ⟨8, _⟩, ⟨0, _⟩ => (-5 : ℚ) / 8
  | ⟨8, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 4
  | ⟨8, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨7, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨8, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨9, _⟩ => (3 : ℚ) / 8
  | ⟨9, _⟩, ⟨0, _⟩ => (-1 : ℚ)
  | ⟨9, _⟩, ⟨1, _⟩ => (-3 : ℚ) / 4
  | ⟨9, _⟩, ⟨2, _⟩ => (-3 : ℚ) / 4
  | ⟨9, _⟩, ⟨3, _⟩ => (-3 : ℚ) / 4
  | ⟨9, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 2
  | ⟨9, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 4
  | ⟨9, _⟩, ⟨6, _⟩ => (-1 : ℚ) / 4
  | ⟨9, _⟩, ⟨7, _⟩ => (-1 : ℚ) / 4
  | ⟨9, _⟩, ⟨8, _⟩ => (-1 : ℚ) / 8
  | ⟨9, _⟩, ⟨9, _⟩ => (0 : ℚ)

theorem row_cap_1409_0_0 :
    (∑ q : Fin 9, y4_1409 q * rowA 0 0 q) ≤ db_1409 0 0 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_0_1 :
    (∑ q : Fin 9, y4_1409 q * rowA 0 1 q) ≤ db_1409 0 1 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_0_2 :
    (∑ q : Fin 9, y4_1409 q * rowA 0 2 q) ≤ db_1409 0 2 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_0_3 :
    (∑ q : Fin 9, y4_1409 q * rowA 0 3 q) ≤ db_1409 0 3 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_0_4 :
    (∑ q : Fin 9, y4_1409 q * rowA 0 4 q) ≤ db_1409 0 4 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_0_5 :
    (∑ q : Fin 9, y4_1409 q * rowA 0 5 q) ≤ db_1409 0 5 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_0_6 :
    (∑ q : Fin 9, y4_1409 q * rowA 0 6 q) ≤ db_1409 0 6 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_0_7 :
    (∑ q : Fin 9, y4_1409 q * rowA 0 7 q) ≤ db_1409 0 7 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_0_8 :
    (∑ q : Fin 9, y4_1409 q * rowA 0 8 q) ≤ db_1409 0 8 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_0_9 :
    (∑ q : Fin 9, y4_1409 q * rowA 0 9 q) ≤ db_1409 0 9 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1_0 :
    (∑ q : Fin 9, y4_1409 q * rowA 1 0 q) ≤ db_1409 1 0 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1_1 :
    (∑ q : Fin 9, y4_1409 q * rowA 1 1 q) ≤ db_1409 1 1 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1_2 :
    (∑ q : Fin 9, y4_1409 q * rowA 1 2 q) ≤ db_1409 1 2 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1_3 :
    (∑ q : Fin 9, y4_1409 q * rowA 1 3 q) ≤ db_1409 1 3 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1_4 :
    (∑ q : Fin 9, y4_1409 q * rowA 1 4 q) ≤ db_1409 1 4 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1_5 :
    (∑ q : Fin 9, y4_1409 q * rowA 1 5 q) ≤ db_1409 1 5 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1_6 :
    (∑ q : Fin 9, y4_1409 q * rowA 1 6 q) ≤ db_1409 1 6 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1_7 :
    (∑ q : Fin 9, y4_1409 q * rowA 1 7 q) ≤ db_1409 1 7 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1_8 :
    (∑ q : Fin 9, y4_1409 q * rowA 1 8 q) ≤ db_1409 1 8 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_1_9 :
    (∑ q : Fin 9, y4_1409 q * rowA 1 9 q) ≤ db_1409 1 9 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2_0 :
    (∑ q : Fin 9, y4_1409 q * rowA 2 0 q) ≤ db_1409 2 0 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2_1 :
    (∑ q : Fin 9, y4_1409 q * rowA 2 1 q) ≤ db_1409 2 1 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2_2 :
    (∑ q : Fin 9, y4_1409 q * rowA 2 2 q) ≤ db_1409 2 2 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2_3 :
    (∑ q : Fin 9, y4_1409 q * rowA 2 3 q) ≤ db_1409 2 3 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2_4 :
    (∑ q : Fin 9, y4_1409 q * rowA 2 4 q) ≤ db_1409 2 4 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2_5 :
    (∑ q : Fin 9, y4_1409 q * rowA 2 5 q) ≤ db_1409 2 5 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2_6 :
    (∑ q : Fin 9, y4_1409 q * rowA 2 6 q) ≤ db_1409 2 6 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2_7 :
    (∑ q : Fin 9, y4_1409 q * rowA 2 7 q) ≤ db_1409 2 7 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2_8 :
    (∑ q : Fin 9, y4_1409 q * rowA 2 8 q) ≤ db_1409 2 8 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_2_9 :
    (∑ q : Fin 9, y4_1409 q * rowA 2 9 q) ≤ db_1409 2 9 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3_0 :
    (∑ q : Fin 9, y4_1409 q * rowA 3 0 q) ≤ db_1409 3 0 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3_1 :
    (∑ q : Fin 9, y4_1409 q * rowA 3 1 q) ≤ db_1409 3 1 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3_2 :
    (∑ q : Fin 9, y4_1409 q * rowA 3 2 q) ≤ db_1409 3 2 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3_3 :
    (∑ q : Fin 9, y4_1409 q * rowA 3 3 q) ≤ db_1409 3 3 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3_4 :
    (∑ q : Fin 9, y4_1409 q * rowA 3 4 q) ≤ db_1409 3 4 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3_5 :
    (∑ q : Fin 9, y4_1409 q * rowA 3 5 q) ≤ db_1409 3 5 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3_6 :
    (∑ q : Fin 9, y4_1409 q * rowA 3 6 q) ≤ db_1409 3 6 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3_7 :
    (∑ q : Fin 9, y4_1409 q * rowA 3 7 q) ≤ db_1409 3 7 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3_8 :
    (∑ q : Fin 9, y4_1409 q * rowA 3 8 q) ≤ db_1409 3 8 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_3_9 :
    (∑ q : Fin 9, y4_1409 q * rowA 3 9 q) ≤ db_1409 3 9 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4_0 :
    (∑ q : Fin 9, y4_1409 q * rowA 4 0 q) ≤ db_1409 4 0 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4_1 :
    (∑ q : Fin 9, y4_1409 q * rowA 4 1 q) ≤ db_1409 4 1 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4_2 :
    (∑ q : Fin 9, y4_1409 q * rowA 4 2 q) ≤ db_1409 4 2 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4_3 :
    (∑ q : Fin 9, y4_1409 q * rowA 4 3 q) ≤ db_1409 4 3 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4_4 :
    (∑ q : Fin 9, y4_1409 q * rowA 4 4 q) ≤ db_1409 4 4 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4_5 :
    (∑ q : Fin 9, y4_1409 q * rowA 4 5 q) ≤ db_1409 4 5 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4_6 :
    (∑ q : Fin 9, y4_1409 q * rowA 4 6 q) ≤ db_1409 4 6 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4_7 :
    (∑ q : Fin 9, y4_1409 q * rowA 4 7 q) ≤ db_1409 4 7 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4_8 :
    (∑ q : Fin 9, y4_1409 q * rowA 4 8 q) ≤ db_1409 4 8 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_4_9 :
    (∑ q : Fin 9, y4_1409 q * rowA 4 9 q) ≤ db_1409 4 9 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5_0 :
    (∑ q : Fin 9, y4_1409 q * rowA 5 0 q) ≤ db_1409 5 0 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5_1 :
    (∑ q : Fin 9, y4_1409 q * rowA 5 1 q) ≤ db_1409 5 1 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5_2 :
    (∑ q : Fin 9, y4_1409 q * rowA 5 2 q) ≤ db_1409 5 2 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5_3 :
    (∑ q : Fin 9, y4_1409 q * rowA 5 3 q) ≤ db_1409 5 3 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5_4 :
    (∑ q : Fin 9, y4_1409 q * rowA 5 4 q) ≤ db_1409 5 4 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5_5 :
    (∑ q : Fin 9, y4_1409 q * rowA 5 5 q) ≤ db_1409 5 5 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5_6 :
    (∑ q : Fin 9, y4_1409 q * rowA 5 6 q) ≤ db_1409 5 6 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5_7 :
    (∑ q : Fin 9, y4_1409 q * rowA 5 7 q) ≤ db_1409 5 7 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5_8 :
    (∑ q : Fin 9, y4_1409 q * rowA 5 8 q) ≤ db_1409 5 8 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_5_9 :
    (∑ q : Fin 9, y4_1409 q * rowA 5 9 q) ≤ db_1409 5 9 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6_0 :
    (∑ q : Fin 9, y4_1409 q * rowA 6 0 q) ≤ db_1409 6 0 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6_1 :
    (∑ q : Fin 9, y4_1409 q * rowA 6 1 q) ≤ db_1409 6 1 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6_2 :
    (∑ q : Fin 9, y4_1409 q * rowA 6 2 q) ≤ db_1409 6 2 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6_3 :
    (∑ q : Fin 9, y4_1409 q * rowA 6 3 q) ≤ db_1409 6 3 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6_4 :
    (∑ q : Fin 9, y4_1409 q * rowA 6 4 q) ≤ db_1409 6 4 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6_5 :
    (∑ q : Fin 9, y4_1409 q * rowA 6 5 q) ≤ db_1409 6 5 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6_6 :
    (∑ q : Fin 9, y4_1409 q * rowA 6 6 q) ≤ db_1409 6 6 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6_7 :
    (∑ q : Fin 9, y4_1409 q * rowA 6 7 q) ≤ db_1409 6 7 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6_8 :
    (∑ q : Fin 9, y4_1409 q * rowA 6 8 q) ≤ db_1409 6 8 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_6_9 :
    (∑ q : Fin 9, y4_1409 q * rowA 6 9 q) ≤ db_1409 6 9 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7_0 :
    (∑ q : Fin 9, y4_1409 q * rowA 7 0 q) ≤ db_1409 7 0 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7_1 :
    (∑ q : Fin 9, y4_1409 q * rowA 7 1 q) ≤ db_1409 7 1 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7_2 :
    (∑ q : Fin 9, y4_1409 q * rowA 7 2 q) ≤ db_1409 7 2 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7_3 :
    (∑ q : Fin 9, y4_1409 q * rowA 7 3 q) ≤ db_1409 7 3 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7_4 :
    (∑ q : Fin 9, y4_1409 q * rowA 7 4 q) ≤ db_1409 7 4 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7_5 :
    (∑ q : Fin 9, y4_1409 q * rowA 7 5 q) ≤ db_1409 7 5 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7_6 :
    (∑ q : Fin 9, y4_1409 q * rowA 7 6 q) ≤ db_1409 7 6 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7_7 :
    (∑ q : Fin 9, y4_1409 q * rowA 7 7 q) ≤ db_1409 7 7 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7_8 :
    (∑ q : Fin 9, y4_1409 q * rowA 7 8 q) ≤ db_1409 7 8 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_7_9 :
    (∑ q : Fin 9, y4_1409 q * rowA 7 9 q) ≤ db_1409 7 9 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8_0 :
    (∑ q : Fin 9, y4_1409 q * rowA 8 0 q) ≤ db_1409 8 0 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8_1 :
    (∑ q : Fin 9, y4_1409 q * rowA 8 1 q) ≤ db_1409 8 1 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8_2 :
    (∑ q : Fin 9, y4_1409 q * rowA 8 2 q) ≤ db_1409 8 2 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8_3 :
    (∑ q : Fin 9, y4_1409 q * rowA 8 3 q) ≤ db_1409 8 3 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8_4 :
    (∑ q : Fin 9, y4_1409 q * rowA 8 4 q) ≤ db_1409 8 4 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8_5 :
    (∑ q : Fin 9, y4_1409 q * rowA 8 5 q) ≤ db_1409 8 5 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8_6 :
    (∑ q : Fin 9, y4_1409 q * rowA 8 6 q) ≤ db_1409 8 6 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8_7 :
    (∑ q : Fin 9, y4_1409 q * rowA 8 7 q) ≤ db_1409 8 7 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8_8 :
    (∑ q : Fin 9, y4_1409 q * rowA 8 8 q) ≤ db_1409 8 8 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_8_9 :
    (∑ q : Fin 9, y4_1409 q * rowA 8 9 q) ≤ db_1409 8 9 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9_0 :
    (∑ q : Fin 9, y4_1409 q * rowA 9 0 q) ≤ db_1409 9 0 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9_1 :
    (∑ q : Fin 9, y4_1409 q * rowA 9 1 q) ≤ db_1409 9 1 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9_2 :
    (∑ q : Fin 9, y4_1409 q * rowA 9 2 q) ≤ db_1409 9 2 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9_3 :
    (∑ q : Fin 9, y4_1409 q * rowA 9 3 q) ≤ db_1409 9 3 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9_4 :
    (∑ q : Fin 9, y4_1409 q * rowA 9 4 q) ≤ db_1409 9 4 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9_5 :
    (∑ q : Fin 9, y4_1409 q * rowA 9 5 q) ≤ db_1409 9 5 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9_6 :
    (∑ q : Fin 9, y4_1409 q * rowA 9 6 q) ≤ db_1409 9 6 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9_7 :
    (∑ q : Fin 9, y4_1409 q * rowA 9 7 q) ≤ db_1409 9 7 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9_8 :
    (∑ q : Fin 9, y4_1409 q * rowA 9 8 q) ≤ db_1409 9 8 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_9_9 :
    (∑ q : Fin 9, y4_1409 q * rowA 9 9 q) ≤ db_1409 9 9 := by
  norm_num [y4_1409, rowA, db_1409, Fin.sum_univ_succ]

theorem row_cap_1409_0 (j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA 0 j q) ≤ db_1409 0 j := by
  fin_cases j
  · exact row_cap_1409_0_0
  · exact row_cap_1409_0_1
  · exact row_cap_1409_0_2
  · exact row_cap_1409_0_3
  · exact row_cap_1409_0_4
  · exact row_cap_1409_0_5
  · exact row_cap_1409_0_6
  · exact row_cap_1409_0_7
  · exact row_cap_1409_0_8
  · exact row_cap_1409_0_9

theorem row_cap_1409_1 (j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA 1 j q) ≤ db_1409 1 j := by
  fin_cases j
  · exact row_cap_1409_1_0
  · exact row_cap_1409_1_1
  · exact row_cap_1409_1_2
  · exact row_cap_1409_1_3
  · exact row_cap_1409_1_4
  · exact row_cap_1409_1_5
  · exact row_cap_1409_1_6
  · exact row_cap_1409_1_7
  · exact row_cap_1409_1_8
  · exact row_cap_1409_1_9

theorem row_cap_1409_2 (j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA 2 j q) ≤ db_1409 2 j := by
  fin_cases j
  · exact row_cap_1409_2_0
  · exact row_cap_1409_2_1
  · exact row_cap_1409_2_2
  · exact row_cap_1409_2_3
  · exact row_cap_1409_2_4
  · exact row_cap_1409_2_5
  · exact row_cap_1409_2_6
  · exact row_cap_1409_2_7
  · exact row_cap_1409_2_8
  · exact row_cap_1409_2_9

theorem row_cap_1409_3 (j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA 3 j q) ≤ db_1409 3 j := by
  fin_cases j
  · exact row_cap_1409_3_0
  · exact row_cap_1409_3_1
  · exact row_cap_1409_3_2
  · exact row_cap_1409_3_3
  · exact row_cap_1409_3_4
  · exact row_cap_1409_3_5
  · exact row_cap_1409_3_6
  · exact row_cap_1409_3_7
  · exact row_cap_1409_3_8
  · exact row_cap_1409_3_9

theorem row_cap_1409_4 (j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA 4 j q) ≤ db_1409 4 j := by
  fin_cases j
  · exact row_cap_1409_4_0
  · exact row_cap_1409_4_1
  · exact row_cap_1409_4_2
  · exact row_cap_1409_4_3
  · exact row_cap_1409_4_4
  · exact row_cap_1409_4_5
  · exact row_cap_1409_4_6
  · exact row_cap_1409_4_7
  · exact row_cap_1409_4_8
  · exact row_cap_1409_4_9

theorem row_cap_1409_5 (j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA 5 j q) ≤ db_1409 5 j := by
  fin_cases j
  · exact row_cap_1409_5_0
  · exact row_cap_1409_5_1
  · exact row_cap_1409_5_2
  · exact row_cap_1409_5_3
  · exact row_cap_1409_5_4
  · exact row_cap_1409_5_5
  · exact row_cap_1409_5_6
  · exact row_cap_1409_5_7
  · exact row_cap_1409_5_8
  · exact row_cap_1409_5_9

theorem row_cap_1409_6 (j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA 6 j q) ≤ db_1409 6 j := by
  fin_cases j
  · exact row_cap_1409_6_0
  · exact row_cap_1409_6_1
  · exact row_cap_1409_6_2
  · exact row_cap_1409_6_3
  · exact row_cap_1409_6_4
  · exact row_cap_1409_6_5
  · exact row_cap_1409_6_6
  · exact row_cap_1409_6_7
  · exact row_cap_1409_6_8
  · exact row_cap_1409_6_9

theorem row_cap_1409_7 (j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA 7 j q) ≤ db_1409 7 j := by
  fin_cases j
  · exact row_cap_1409_7_0
  · exact row_cap_1409_7_1
  · exact row_cap_1409_7_2
  · exact row_cap_1409_7_3
  · exact row_cap_1409_7_4
  · exact row_cap_1409_7_5
  · exact row_cap_1409_7_6
  · exact row_cap_1409_7_7
  · exact row_cap_1409_7_8
  · exact row_cap_1409_7_9

theorem row_cap_1409_8 (j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA 8 j q) ≤ db_1409 8 j := by
  fin_cases j
  · exact row_cap_1409_8_0
  · exact row_cap_1409_8_1
  · exact row_cap_1409_8_2
  · exact row_cap_1409_8_3
  · exact row_cap_1409_8_4
  · exact row_cap_1409_8_5
  · exact row_cap_1409_8_6
  · exact row_cap_1409_8_7
  · exact row_cap_1409_8_8
  · exact row_cap_1409_8_9

theorem row_cap_1409_9 (j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA 9 j q) ≤ db_1409 9 j := by
  fin_cases j
  · exact row_cap_1409_9_0
  · exact row_cap_1409_9_1
  · exact row_cap_1409_9_2
  · exact row_cap_1409_9_3
  · exact row_cap_1409_9_4
  · exact row_cap_1409_9_5
  · exact row_cap_1409_9_6
  · exact row_cap_1409_9_7
  · exact row_cap_1409_9_8
  · exact row_cap_1409_9_9

theorem row_cap_1409 (i j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA i j q) ≤ db_1409 i j := by
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

def db_2337 : Fin 10 → Fin 10 → ℚ
  | ⟨0, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨0, _⟩, ⟨1, _⟩ => (3 : ℚ) / 16
  | ⟨0, _⟩, ⟨2, _⟩ => (3 : ℚ) / 16
  | ⟨0, _⟩, ⟨3, _⟩ => (3 : ℚ) / 16
  | ⟨0, _⟩, ⟨4, _⟩ => (5 : ℚ) / 16
  | ⟨0, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨0, _⟩, ⟨6, _⟩ => (1 : ℚ) / 2
  | ⟨0, _⟩, ⟨7, _⟩ => (11 : ℚ) / 16
  | ⟨0, _⟩, ⟨8, _⟩ => (11 : ℚ) / 16
  | ⟨0, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨1, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨1, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨1, _⟩, ⟨2, _⟩ => (3 : ℚ) / 16
  | ⟨1, _⟩, ⟨3, _⟩ => (3 : ℚ) / 16
  | ⟨1, _⟩, ⟨4, _⟩ => (5 : ℚ) / 16
  | ⟨1, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨1, _⟩, ⟨6, _⟩ => (1 : ℚ) / 2
  | ⟨1, _⟩, ⟨7, _⟩ => (11 : ℚ) / 16
  | ⟨1, _⟩, ⟨8, _⟩ => (11 : ℚ) / 16
  | ⟨1, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨2, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨3, _⟩ => (3 : ℚ) / 16
  | ⟨2, _⟩, ⟨4, _⟩ => (5 : ℚ) / 16
  | ⟨2, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨2, _⟩, ⟨6, _⟩ => (1 : ℚ) / 2
  | ⟨2, _⟩, ⟨7, _⟩ => (11 : ℚ) / 16
  | ⟨2, _⟩, ⟨8, _⟩ => (11 : ℚ) / 16
  | ⟨2, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨3, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨3, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨4, _⟩ => (5 : ℚ) / 16
  | ⟨3, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨3, _⟩, ⟨6, _⟩ => (1 : ℚ) / 2
  | ⟨3, _⟩, ⟨7, _⟩ => (5 : ℚ) / 8
  | ⟨3, _⟩, ⟨8, _⟩ => (5 : ℚ) / 8
  | ⟨3, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨4, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 4
  | ⟨4, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 8
  | ⟨4, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 8
  | ⟨4, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 8
  | ⟨4, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨4, _⟩, ⟨5, _⟩ => (1 : ℚ) / 4
  | ⟨4, _⟩, ⟨6, _⟩ => (1 : ℚ) / 4
  | ⟨4, _⟩, ⟨7, _⟩ => (3 : ℚ) / 8
  | ⟨4, _⟩, ⟨8, _⟩ => (3 : ℚ) / 8
  | ⟨4, _⟩, ⟨9, _⟩ => (3 : ℚ) / 4
  | ⟨5, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨6, _⟩ => (1 : ℚ) / 4
  | ⟨5, _⟩, ⟨7, _⟩ => (1 : ℚ) / 4
  | ⟨5, _⟩, ⟨8, _⟩ => (1 : ℚ) / 4
  | ⟨5, _⟩, ⟨9, _⟩ => (3 : ℚ) / 4
  | ⟨6, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 4
  | ⟨6, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 4
  | ⟨6, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 4
  | ⟨6, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 4
  | ⟨6, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨7, _⟩ => (1 : ℚ) / 4
  | ⟨6, _⟩, ⟨8, _⟩ => (1 : ℚ) / 4
  | ⟨6, _⟩, ⟨9, _⟩ => (3 : ℚ) / 4
  | ⟨7, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 4
  | ⟨7, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨7, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨8, _⟩ => (1 : ℚ) / 8
  | ⟨7, _⟩, ⟨9, _⟩ => (1 : ℚ) / 2
  | ⟨8, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 4
  | ⟨8, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 8
  | ⟨8, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨7, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨8, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨9, _⟩ => (1 : ℚ) / 2
  | ⟨9, _⟩, ⟨0, _⟩ => (-1 : ℚ)
  | ⟨9, _⟩, ⟨1, _⟩ => (-13 : ℚ) / 16
  | ⟨9, _⟩, ⟨2, _⟩ => (-13 : ℚ) / 16
  | ⟨9, _⟩, ⟨3, _⟩ => (-13 : ℚ) / 16
  | ⟨9, _⟩, ⟨4, _⟩ => (-11 : ℚ) / 16
  | ⟨9, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 2
  | ⟨9, _⟩, ⟨6, _⟩ => (-1 : ℚ) / 2
  | ⟨9, _⟩, ⟨7, _⟩ => (-5 : ℚ) / 16
  | ⟨9, _⟩, ⟨8, _⟩ => (-5 : ℚ) / 16
  | ⟨9, _⟩, ⟨9, _⟩ => (0 : ℚ)

theorem row_cap_2337_0_0 :
    (∑ q : Fin 9, y4_2337 q * rowA 0 0 q) ≤ db_2337 0 0 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_0_1 :
    (∑ q : Fin 9, y4_2337 q * rowA 0 1 q) ≤ db_2337 0 1 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_0_2 :
    (∑ q : Fin 9, y4_2337 q * rowA 0 2 q) ≤ db_2337 0 2 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_0_3 :
    (∑ q : Fin 9, y4_2337 q * rowA 0 3 q) ≤ db_2337 0 3 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_0_4 :
    (∑ q : Fin 9, y4_2337 q * rowA 0 4 q) ≤ db_2337 0 4 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_0_5 :
    (∑ q : Fin 9, y4_2337 q * rowA 0 5 q) ≤ db_2337 0 5 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_0_6 :
    (∑ q : Fin 9, y4_2337 q * rowA 0 6 q) ≤ db_2337 0 6 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_0_7 :
    (∑ q : Fin 9, y4_2337 q * rowA 0 7 q) ≤ db_2337 0 7 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_0_8 :
    (∑ q : Fin 9, y4_2337 q * rowA 0 8 q) ≤ db_2337 0 8 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_0_9 :
    (∑ q : Fin 9, y4_2337 q * rowA 0 9 q) ≤ db_2337 0 9 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1_0 :
    (∑ q : Fin 9, y4_2337 q * rowA 1 0 q) ≤ db_2337 1 0 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1_1 :
    (∑ q : Fin 9, y4_2337 q * rowA 1 1 q) ≤ db_2337 1 1 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1_2 :
    (∑ q : Fin 9, y4_2337 q * rowA 1 2 q) ≤ db_2337 1 2 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1_3 :
    (∑ q : Fin 9, y4_2337 q * rowA 1 3 q) ≤ db_2337 1 3 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1_4 :
    (∑ q : Fin 9, y4_2337 q * rowA 1 4 q) ≤ db_2337 1 4 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1_5 :
    (∑ q : Fin 9, y4_2337 q * rowA 1 5 q) ≤ db_2337 1 5 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1_6 :
    (∑ q : Fin 9, y4_2337 q * rowA 1 6 q) ≤ db_2337 1 6 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1_7 :
    (∑ q : Fin 9, y4_2337 q * rowA 1 7 q) ≤ db_2337 1 7 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1_8 :
    (∑ q : Fin 9, y4_2337 q * rowA 1 8 q) ≤ db_2337 1 8 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_1_9 :
    (∑ q : Fin 9, y4_2337 q * rowA 1 9 q) ≤ db_2337 1 9 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2_0 :
    (∑ q : Fin 9, y4_2337 q * rowA 2 0 q) ≤ db_2337 2 0 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2_1 :
    (∑ q : Fin 9, y4_2337 q * rowA 2 1 q) ≤ db_2337 2 1 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2_2 :
    (∑ q : Fin 9, y4_2337 q * rowA 2 2 q) ≤ db_2337 2 2 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2_3 :
    (∑ q : Fin 9, y4_2337 q * rowA 2 3 q) ≤ db_2337 2 3 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2_4 :
    (∑ q : Fin 9, y4_2337 q * rowA 2 4 q) ≤ db_2337 2 4 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2_5 :
    (∑ q : Fin 9, y4_2337 q * rowA 2 5 q) ≤ db_2337 2 5 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2_6 :
    (∑ q : Fin 9, y4_2337 q * rowA 2 6 q) ≤ db_2337 2 6 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2_7 :
    (∑ q : Fin 9, y4_2337 q * rowA 2 7 q) ≤ db_2337 2 7 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2_8 :
    (∑ q : Fin 9, y4_2337 q * rowA 2 8 q) ≤ db_2337 2 8 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_2_9 :
    (∑ q : Fin 9, y4_2337 q * rowA 2 9 q) ≤ db_2337 2 9 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3_0 :
    (∑ q : Fin 9, y4_2337 q * rowA 3 0 q) ≤ db_2337 3 0 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3_1 :
    (∑ q : Fin 9, y4_2337 q * rowA 3 1 q) ≤ db_2337 3 1 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3_2 :
    (∑ q : Fin 9, y4_2337 q * rowA 3 2 q) ≤ db_2337 3 2 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3_3 :
    (∑ q : Fin 9, y4_2337 q * rowA 3 3 q) ≤ db_2337 3 3 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3_4 :
    (∑ q : Fin 9, y4_2337 q * rowA 3 4 q) ≤ db_2337 3 4 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3_5 :
    (∑ q : Fin 9, y4_2337 q * rowA 3 5 q) ≤ db_2337 3 5 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3_6 :
    (∑ q : Fin 9, y4_2337 q * rowA 3 6 q) ≤ db_2337 3 6 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3_7 :
    (∑ q : Fin 9, y4_2337 q * rowA 3 7 q) ≤ db_2337 3 7 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3_8 :
    (∑ q : Fin 9, y4_2337 q * rowA 3 8 q) ≤ db_2337 3 8 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_3_9 :
    (∑ q : Fin 9, y4_2337 q * rowA 3 9 q) ≤ db_2337 3 9 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4_0 :
    (∑ q : Fin 9, y4_2337 q * rowA 4 0 q) ≤ db_2337 4 0 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4_1 :
    (∑ q : Fin 9, y4_2337 q * rowA 4 1 q) ≤ db_2337 4 1 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4_2 :
    (∑ q : Fin 9, y4_2337 q * rowA 4 2 q) ≤ db_2337 4 2 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4_3 :
    (∑ q : Fin 9, y4_2337 q * rowA 4 3 q) ≤ db_2337 4 3 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4_4 :
    (∑ q : Fin 9, y4_2337 q * rowA 4 4 q) ≤ db_2337 4 4 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4_5 :
    (∑ q : Fin 9, y4_2337 q * rowA 4 5 q) ≤ db_2337 4 5 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4_6 :
    (∑ q : Fin 9, y4_2337 q * rowA 4 6 q) ≤ db_2337 4 6 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4_7 :
    (∑ q : Fin 9, y4_2337 q * rowA 4 7 q) ≤ db_2337 4 7 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4_8 :
    (∑ q : Fin 9, y4_2337 q * rowA 4 8 q) ≤ db_2337 4 8 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_4_9 :
    (∑ q : Fin 9, y4_2337 q * rowA 4 9 q) ≤ db_2337 4 9 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5_0 :
    (∑ q : Fin 9, y4_2337 q * rowA 5 0 q) ≤ db_2337 5 0 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5_1 :
    (∑ q : Fin 9, y4_2337 q * rowA 5 1 q) ≤ db_2337 5 1 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5_2 :
    (∑ q : Fin 9, y4_2337 q * rowA 5 2 q) ≤ db_2337 5 2 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5_3 :
    (∑ q : Fin 9, y4_2337 q * rowA 5 3 q) ≤ db_2337 5 3 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5_4 :
    (∑ q : Fin 9, y4_2337 q * rowA 5 4 q) ≤ db_2337 5 4 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5_5 :
    (∑ q : Fin 9, y4_2337 q * rowA 5 5 q) ≤ db_2337 5 5 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5_6 :
    (∑ q : Fin 9, y4_2337 q * rowA 5 6 q) ≤ db_2337 5 6 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5_7 :
    (∑ q : Fin 9, y4_2337 q * rowA 5 7 q) ≤ db_2337 5 7 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5_8 :
    (∑ q : Fin 9, y4_2337 q * rowA 5 8 q) ≤ db_2337 5 8 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_5_9 :
    (∑ q : Fin 9, y4_2337 q * rowA 5 9 q) ≤ db_2337 5 9 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6_0 :
    (∑ q : Fin 9, y4_2337 q * rowA 6 0 q) ≤ db_2337 6 0 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6_1 :
    (∑ q : Fin 9, y4_2337 q * rowA 6 1 q) ≤ db_2337 6 1 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6_2 :
    (∑ q : Fin 9, y4_2337 q * rowA 6 2 q) ≤ db_2337 6 2 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6_3 :
    (∑ q : Fin 9, y4_2337 q * rowA 6 3 q) ≤ db_2337 6 3 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6_4 :
    (∑ q : Fin 9, y4_2337 q * rowA 6 4 q) ≤ db_2337 6 4 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6_5 :
    (∑ q : Fin 9, y4_2337 q * rowA 6 5 q) ≤ db_2337 6 5 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6_6 :
    (∑ q : Fin 9, y4_2337 q * rowA 6 6 q) ≤ db_2337 6 6 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6_7 :
    (∑ q : Fin 9, y4_2337 q * rowA 6 7 q) ≤ db_2337 6 7 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6_8 :
    (∑ q : Fin 9, y4_2337 q * rowA 6 8 q) ≤ db_2337 6 8 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_6_9 :
    (∑ q : Fin 9, y4_2337 q * rowA 6 9 q) ≤ db_2337 6 9 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7_0 :
    (∑ q : Fin 9, y4_2337 q * rowA 7 0 q) ≤ db_2337 7 0 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7_1 :
    (∑ q : Fin 9, y4_2337 q * rowA 7 1 q) ≤ db_2337 7 1 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7_2 :
    (∑ q : Fin 9, y4_2337 q * rowA 7 2 q) ≤ db_2337 7 2 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7_3 :
    (∑ q : Fin 9, y4_2337 q * rowA 7 3 q) ≤ db_2337 7 3 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7_4 :
    (∑ q : Fin 9, y4_2337 q * rowA 7 4 q) ≤ db_2337 7 4 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7_5 :
    (∑ q : Fin 9, y4_2337 q * rowA 7 5 q) ≤ db_2337 7 5 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7_6 :
    (∑ q : Fin 9, y4_2337 q * rowA 7 6 q) ≤ db_2337 7 6 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7_7 :
    (∑ q : Fin 9, y4_2337 q * rowA 7 7 q) ≤ db_2337 7 7 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7_8 :
    (∑ q : Fin 9, y4_2337 q * rowA 7 8 q) ≤ db_2337 7 8 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_7_9 :
    (∑ q : Fin 9, y4_2337 q * rowA 7 9 q) ≤ db_2337 7 9 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8_0 :
    (∑ q : Fin 9, y4_2337 q * rowA 8 0 q) ≤ db_2337 8 0 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8_1 :
    (∑ q : Fin 9, y4_2337 q * rowA 8 1 q) ≤ db_2337 8 1 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8_2 :
    (∑ q : Fin 9, y4_2337 q * rowA 8 2 q) ≤ db_2337 8 2 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8_3 :
    (∑ q : Fin 9, y4_2337 q * rowA 8 3 q) ≤ db_2337 8 3 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8_4 :
    (∑ q : Fin 9, y4_2337 q * rowA 8 4 q) ≤ db_2337 8 4 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8_5 :
    (∑ q : Fin 9, y4_2337 q * rowA 8 5 q) ≤ db_2337 8 5 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8_6 :
    (∑ q : Fin 9, y4_2337 q * rowA 8 6 q) ≤ db_2337 8 6 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8_7 :
    (∑ q : Fin 9, y4_2337 q * rowA 8 7 q) ≤ db_2337 8 7 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8_8 :
    (∑ q : Fin 9, y4_2337 q * rowA 8 8 q) ≤ db_2337 8 8 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_8_9 :
    (∑ q : Fin 9, y4_2337 q * rowA 8 9 q) ≤ db_2337 8 9 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9_0 :
    (∑ q : Fin 9, y4_2337 q * rowA 9 0 q) ≤ db_2337 9 0 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9_1 :
    (∑ q : Fin 9, y4_2337 q * rowA 9 1 q) ≤ db_2337 9 1 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9_2 :
    (∑ q : Fin 9, y4_2337 q * rowA 9 2 q) ≤ db_2337 9 2 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9_3 :
    (∑ q : Fin 9, y4_2337 q * rowA 9 3 q) ≤ db_2337 9 3 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9_4 :
    (∑ q : Fin 9, y4_2337 q * rowA 9 4 q) ≤ db_2337 9 4 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9_5 :
    (∑ q : Fin 9, y4_2337 q * rowA 9 5 q) ≤ db_2337 9 5 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9_6 :
    (∑ q : Fin 9, y4_2337 q * rowA 9 6 q) ≤ db_2337 9 6 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9_7 :
    (∑ q : Fin 9, y4_2337 q * rowA 9 7 q) ≤ db_2337 9 7 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9_8 :
    (∑ q : Fin 9, y4_2337 q * rowA 9 8 q) ≤ db_2337 9 8 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_9_9 :
    (∑ q : Fin 9, y4_2337 q * rowA 9 9 q) ≤ db_2337 9 9 := by
  norm_num [y4_2337, rowA, db_2337, Fin.sum_univ_succ]

theorem row_cap_2337_0 (j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA 0 j q) ≤ db_2337 0 j := by
  fin_cases j
  · exact row_cap_2337_0_0
  · exact row_cap_2337_0_1
  · exact row_cap_2337_0_2
  · exact row_cap_2337_0_3
  · exact row_cap_2337_0_4
  · exact row_cap_2337_0_5
  · exact row_cap_2337_0_6
  · exact row_cap_2337_0_7
  · exact row_cap_2337_0_8
  · exact row_cap_2337_0_9

theorem row_cap_2337_1 (j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA 1 j q) ≤ db_2337 1 j := by
  fin_cases j
  · exact row_cap_2337_1_0
  · exact row_cap_2337_1_1
  · exact row_cap_2337_1_2
  · exact row_cap_2337_1_3
  · exact row_cap_2337_1_4
  · exact row_cap_2337_1_5
  · exact row_cap_2337_1_6
  · exact row_cap_2337_1_7
  · exact row_cap_2337_1_8
  · exact row_cap_2337_1_9

theorem row_cap_2337_2 (j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA 2 j q) ≤ db_2337 2 j := by
  fin_cases j
  · exact row_cap_2337_2_0
  · exact row_cap_2337_2_1
  · exact row_cap_2337_2_2
  · exact row_cap_2337_2_3
  · exact row_cap_2337_2_4
  · exact row_cap_2337_2_5
  · exact row_cap_2337_2_6
  · exact row_cap_2337_2_7
  · exact row_cap_2337_2_8
  · exact row_cap_2337_2_9

theorem row_cap_2337_3 (j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA 3 j q) ≤ db_2337 3 j := by
  fin_cases j
  · exact row_cap_2337_3_0
  · exact row_cap_2337_3_1
  · exact row_cap_2337_3_2
  · exact row_cap_2337_3_3
  · exact row_cap_2337_3_4
  · exact row_cap_2337_3_5
  · exact row_cap_2337_3_6
  · exact row_cap_2337_3_7
  · exact row_cap_2337_3_8
  · exact row_cap_2337_3_9

theorem row_cap_2337_4 (j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA 4 j q) ≤ db_2337 4 j := by
  fin_cases j
  · exact row_cap_2337_4_0
  · exact row_cap_2337_4_1
  · exact row_cap_2337_4_2
  · exact row_cap_2337_4_3
  · exact row_cap_2337_4_4
  · exact row_cap_2337_4_5
  · exact row_cap_2337_4_6
  · exact row_cap_2337_4_7
  · exact row_cap_2337_4_8
  · exact row_cap_2337_4_9

theorem row_cap_2337_5 (j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA 5 j q) ≤ db_2337 5 j := by
  fin_cases j
  · exact row_cap_2337_5_0
  · exact row_cap_2337_5_1
  · exact row_cap_2337_5_2
  · exact row_cap_2337_5_3
  · exact row_cap_2337_5_4
  · exact row_cap_2337_5_5
  · exact row_cap_2337_5_6
  · exact row_cap_2337_5_7
  · exact row_cap_2337_5_8
  · exact row_cap_2337_5_9

theorem row_cap_2337_6 (j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA 6 j q) ≤ db_2337 6 j := by
  fin_cases j
  · exact row_cap_2337_6_0
  · exact row_cap_2337_6_1
  · exact row_cap_2337_6_2
  · exact row_cap_2337_6_3
  · exact row_cap_2337_6_4
  · exact row_cap_2337_6_5
  · exact row_cap_2337_6_6
  · exact row_cap_2337_6_7
  · exact row_cap_2337_6_8
  · exact row_cap_2337_6_9

theorem row_cap_2337_7 (j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA 7 j q) ≤ db_2337 7 j := by
  fin_cases j
  · exact row_cap_2337_7_0
  · exact row_cap_2337_7_1
  · exact row_cap_2337_7_2
  · exact row_cap_2337_7_3
  · exact row_cap_2337_7_4
  · exact row_cap_2337_7_5
  · exact row_cap_2337_7_6
  · exact row_cap_2337_7_7
  · exact row_cap_2337_7_8
  · exact row_cap_2337_7_9

theorem row_cap_2337_8 (j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA 8 j q) ≤ db_2337 8 j := by
  fin_cases j
  · exact row_cap_2337_8_0
  · exact row_cap_2337_8_1
  · exact row_cap_2337_8_2
  · exact row_cap_2337_8_3
  · exact row_cap_2337_8_4
  · exact row_cap_2337_8_5
  · exact row_cap_2337_8_6
  · exact row_cap_2337_8_7
  · exact row_cap_2337_8_8
  · exact row_cap_2337_8_9

theorem row_cap_2337_9 (j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA 9 j q) ≤ db_2337 9 j := by
  fin_cases j
  · exact row_cap_2337_9_0
  · exact row_cap_2337_9_1
  · exact row_cap_2337_9_2
  · exact row_cap_2337_9_3
  · exact row_cap_2337_9_4
  · exact row_cap_2337_9_5
  · exact row_cap_2337_9_6
  · exact row_cap_2337_9_7
  · exact row_cap_2337_9_8
  · exact row_cap_2337_9_9

theorem row_cap_2337 (i j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA i j q) ≤ db_2337 i j := by
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

def db_2341 : Fin 10 → Fin 10 → ℚ
  | ⟨0, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : ℚ) / 8
  | ⟨0, _⟩, ⟨2, _⟩ => (1 : ℚ) / 8
  | ⟨0, _⟩, ⟨3, _⟩ => (1 : ℚ) / 8
  | ⟨0, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨0, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨0, _⟩, ⟨6, _⟩ => (3 : ℚ) / 4
  | ⟨0, _⟩, ⟨7, _⟩ => (3 : ℚ) / 4
  | ⟨0, _⟩, ⟨8, _⟩ => (3 : ℚ) / 4
  | ⟨0, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨1, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨1, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨1, _⟩, ⟨2, _⟩ => (1 : ℚ) / 8
  | ⟨1, _⟩, ⟨3, _⟩ => (1 : ℚ) / 8
  | ⟨1, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨1, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨1, _⟩, ⟨6, _⟩ => (3 : ℚ) / 4
  | ⟨1, _⟩, ⟨7, _⟩ => (3 : ℚ) / 4
  | ⟨1, _⟩, ⟨8, _⟩ => (3 : ℚ) / 4
  | ⟨1, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨2, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨3, _⟩ => (1 : ℚ) / 8
  | ⟨2, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨2, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨2, _⟩, ⟨6, _⟩ => (3 : ℚ) / 4
  | ⟨2, _⟩, ⟨7, _⟩ => (3 : ℚ) / 4
  | ⟨2, _⟩, ⟨8, _⟩ => (3 : ℚ) / 4
  | ⟨2, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨3, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨3, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨3, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨3, _⟩, ⟨6, _⟩ => (5 : ℚ) / 8
  | ⟨3, _⟩, ⟨7, _⟩ => (5 : ℚ) / 8
  | ⟨3, _⟩, ⟨8, _⟩ => (5 : ℚ) / 8
  | ⟨3, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨4, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 4
  | ⟨4, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 8
  | ⟨4, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 8
  | ⟨4, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 8
  | ⟨4, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨4, _⟩, ⟨5, _⟩ => (1 : ℚ) / 4
  | ⟨4, _⟩, ⟨6, _⟩ => (3 : ℚ) / 8
  | ⟨4, _⟩, ⟨7, _⟩ => (3 : ℚ) / 8
  | ⟨4, _⟩, ⟨8, _⟩ => (3 : ℚ) / 8
  | ⟨4, _⟩, ⟨9, _⟩ => (3 : ℚ) / 4
  | ⟨5, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨6, _⟩ => (1 : ℚ) / 4
  | ⟨5, _⟩, ⟨7, _⟩ => (1 : ℚ) / 4
  | ⟨5, _⟩, ⟨8, _⟩ => (1 : ℚ) / 4
  | ⟨5, _⟩, ⟨9, _⟩ => (3 : ℚ) / 4
  | ⟨6, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 2
  | ⟨6, _⟩, ⟨1, _⟩ => (-3 : ℚ) / 8
  | ⟨6, _⟩, ⟨2, _⟩ => (-3 : ℚ) / 8
  | ⟨6, _⟩, ⟨3, _⟩ => (-3 : ℚ) / 8
  | ⟨6, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 8
  | ⟨6, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨7, _⟩ => (1 : ℚ) / 4
  | ⟨6, _⟩, ⟨8, _⟩ => (1 : ℚ) / 4
  | ⟨6, _⟩, ⟨9, _⟩ => (1 : ℚ) / 2
  | ⟨7, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 4
  | ⟨7, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨7, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨8, _⟩ => (1 : ℚ) / 8
  | ⟨7, _⟩, ⟨9, _⟩ => (1 : ℚ) / 2
  | ⟨8, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 4
  | ⟨8, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 8
  | ⟨8, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨7, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨8, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨9, _⟩ => (1 : ℚ) / 2
  | ⟨9, _⟩, ⟨0, _⟩ => (-1 : ℚ)
  | ⟨9, _⟩, ⟨1, _⟩ => (-7 : ℚ) / 8
  | ⟨9, _⟩, ⟨2, _⟩ => (-7 : ℚ) / 8
  | ⟨9, _⟩, ⟨3, _⟩ => (-7 : ℚ) / 8
  | ⟨9, _⟩, ⟨4, _⟩ => (-5 : ℚ) / 8
  | ⟨9, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 2
  | ⟨9, _⟩, ⟨6, _⟩ => (-1 : ℚ) / 4
  | ⟨9, _⟩, ⟨7, _⟩ => (-1 : ℚ) / 4
  | ⟨9, _⟩, ⟨8, _⟩ => (-1 : ℚ) / 4
  | ⟨9, _⟩, ⟨9, _⟩ => (0 : ℚ)

theorem row_cap_2341_0_0 :
    (∑ q : Fin 9, y4_2341 q * rowA 0 0 q) ≤ db_2341 0 0 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_0_1 :
    (∑ q : Fin 9, y4_2341 q * rowA 0 1 q) ≤ db_2341 0 1 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_0_2 :
    (∑ q : Fin 9, y4_2341 q * rowA 0 2 q) ≤ db_2341 0 2 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_0_3 :
    (∑ q : Fin 9, y4_2341 q * rowA 0 3 q) ≤ db_2341 0 3 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_0_4 :
    (∑ q : Fin 9, y4_2341 q * rowA 0 4 q) ≤ db_2341 0 4 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_0_5 :
    (∑ q : Fin 9, y4_2341 q * rowA 0 5 q) ≤ db_2341 0 5 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_0_6 :
    (∑ q : Fin 9, y4_2341 q * rowA 0 6 q) ≤ db_2341 0 6 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_0_7 :
    (∑ q : Fin 9, y4_2341 q * rowA 0 7 q) ≤ db_2341 0 7 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_0_8 :
    (∑ q : Fin 9, y4_2341 q * rowA 0 8 q) ≤ db_2341 0 8 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_0_9 :
    (∑ q : Fin 9, y4_2341 q * rowA 0 9 q) ≤ db_2341 0 9 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1_0 :
    (∑ q : Fin 9, y4_2341 q * rowA 1 0 q) ≤ db_2341 1 0 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1_1 :
    (∑ q : Fin 9, y4_2341 q * rowA 1 1 q) ≤ db_2341 1 1 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1_2 :
    (∑ q : Fin 9, y4_2341 q * rowA 1 2 q) ≤ db_2341 1 2 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1_3 :
    (∑ q : Fin 9, y4_2341 q * rowA 1 3 q) ≤ db_2341 1 3 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1_4 :
    (∑ q : Fin 9, y4_2341 q * rowA 1 4 q) ≤ db_2341 1 4 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1_5 :
    (∑ q : Fin 9, y4_2341 q * rowA 1 5 q) ≤ db_2341 1 5 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1_6 :
    (∑ q : Fin 9, y4_2341 q * rowA 1 6 q) ≤ db_2341 1 6 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1_7 :
    (∑ q : Fin 9, y4_2341 q * rowA 1 7 q) ≤ db_2341 1 7 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1_8 :
    (∑ q : Fin 9, y4_2341 q * rowA 1 8 q) ≤ db_2341 1 8 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_1_9 :
    (∑ q : Fin 9, y4_2341 q * rowA 1 9 q) ≤ db_2341 1 9 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2_0 :
    (∑ q : Fin 9, y4_2341 q * rowA 2 0 q) ≤ db_2341 2 0 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2_1 :
    (∑ q : Fin 9, y4_2341 q * rowA 2 1 q) ≤ db_2341 2 1 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2_2 :
    (∑ q : Fin 9, y4_2341 q * rowA 2 2 q) ≤ db_2341 2 2 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2_3 :
    (∑ q : Fin 9, y4_2341 q * rowA 2 3 q) ≤ db_2341 2 3 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2_4 :
    (∑ q : Fin 9, y4_2341 q * rowA 2 4 q) ≤ db_2341 2 4 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2_5 :
    (∑ q : Fin 9, y4_2341 q * rowA 2 5 q) ≤ db_2341 2 5 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2_6 :
    (∑ q : Fin 9, y4_2341 q * rowA 2 6 q) ≤ db_2341 2 6 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2_7 :
    (∑ q : Fin 9, y4_2341 q * rowA 2 7 q) ≤ db_2341 2 7 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2_8 :
    (∑ q : Fin 9, y4_2341 q * rowA 2 8 q) ≤ db_2341 2 8 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_2_9 :
    (∑ q : Fin 9, y4_2341 q * rowA 2 9 q) ≤ db_2341 2 9 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3_0 :
    (∑ q : Fin 9, y4_2341 q * rowA 3 0 q) ≤ db_2341 3 0 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3_1 :
    (∑ q : Fin 9, y4_2341 q * rowA 3 1 q) ≤ db_2341 3 1 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3_2 :
    (∑ q : Fin 9, y4_2341 q * rowA 3 2 q) ≤ db_2341 3 2 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3_3 :
    (∑ q : Fin 9, y4_2341 q * rowA 3 3 q) ≤ db_2341 3 3 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3_4 :
    (∑ q : Fin 9, y4_2341 q * rowA 3 4 q) ≤ db_2341 3 4 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3_5 :
    (∑ q : Fin 9, y4_2341 q * rowA 3 5 q) ≤ db_2341 3 5 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3_6 :
    (∑ q : Fin 9, y4_2341 q * rowA 3 6 q) ≤ db_2341 3 6 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3_7 :
    (∑ q : Fin 9, y4_2341 q * rowA 3 7 q) ≤ db_2341 3 7 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3_8 :
    (∑ q : Fin 9, y4_2341 q * rowA 3 8 q) ≤ db_2341 3 8 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_3_9 :
    (∑ q : Fin 9, y4_2341 q * rowA 3 9 q) ≤ db_2341 3 9 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4_0 :
    (∑ q : Fin 9, y4_2341 q * rowA 4 0 q) ≤ db_2341 4 0 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4_1 :
    (∑ q : Fin 9, y4_2341 q * rowA 4 1 q) ≤ db_2341 4 1 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4_2 :
    (∑ q : Fin 9, y4_2341 q * rowA 4 2 q) ≤ db_2341 4 2 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4_3 :
    (∑ q : Fin 9, y4_2341 q * rowA 4 3 q) ≤ db_2341 4 3 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4_4 :
    (∑ q : Fin 9, y4_2341 q * rowA 4 4 q) ≤ db_2341 4 4 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4_5 :
    (∑ q : Fin 9, y4_2341 q * rowA 4 5 q) ≤ db_2341 4 5 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4_6 :
    (∑ q : Fin 9, y4_2341 q * rowA 4 6 q) ≤ db_2341 4 6 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4_7 :
    (∑ q : Fin 9, y4_2341 q * rowA 4 7 q) ≤ db_2341 4 7 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4_8 :
    (∑ q : Fin 9, y4_2341 q * rowA 4 8 q) ≤ db_2341 4 8 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_4_9 :
    (∑ q : Fin 9, y4_2341 q * rowA 4 9 q) ≤ db_2341 4 9 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5_0 :
    (∑ q : Fin 9, y4_2341 q * rowA 5 0 q) ≤ db_2341 5 0 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5_1 :
    (∑ q : Fin 9, y4_2341 q * rowA 5 1 q) ≤ db_2341 5 1 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5_2 :
    (∑ q : Fin 9, y4_2341 q * rowA 5 2 q) ≤ db_2341 5 2 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5_3 :
    (∑ q : Fin 9, y4_2341 q * rowA 5 3 q) ≤ db_2341 5 3 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5_4 :
    (∑ q : Fin 9, y4_2341 q * rowA 5 4 q) ≤ db_2341 5 4 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5_5 :
    (∑ q : Fin 9, y4_2341 q * rowA 5 5 q) ≤ db_2341 5 5 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5_6 :
    (∑ q : Fin 9, y4_2341 q * rowA 5 6 q) ≤ db_2341 5 6 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5_7 :
    (∑ q : Fin 9, y4_2341 q * rowA 5 7 q) ≤ db_2341 5 7 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5_8 :
    (∑ q : Fin 9, y4_2341 q * rowA 5 8 q) ≤ db_2341 5 8 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_5_9 :
    (∑ q : Fin 9, y4_2341 q * rowA 5 9 q) ≤ db_2341 5 9 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6_0 :
    (∑ q : Fin 9, y4_2341 q * rowA 6 0 q) ≤ db_2341 6 0 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6_1 :
    (∑ q : Fin 9, y4_2341 q * rowA 6 1 q) ≤ db_2341 6 1 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6_2 :
    (∑ q : Fin 9, y4_2341 q * rowA 6 2 q) ≤ db_2341 6 2 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6_3 :
    (∑ q : Fin 9, y4_2341 q * rowA 6 3 q) ≤ db_2341 6 3 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6_4 :
    (∑ q : Fin 9, y4_2341 q * rowA 6 4 q) ≤ db_2341 6 4 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6_5 :
    (∑ q : Fin 9, y4_2341 q * rowA 6 5 q) ≤ db_2341 6 5 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6_6 :
    (∑ q : Fin 9, y4_2341 q * rowA 6 6 q) ≤ db_2341 6 6 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6_7 :
    (∑ q : Fin 9, y4_2341 q * rowA 6 7 q) ≤ db_2341 6 7 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6_8 :
    (∑ q : Fin 9, y4_2341 q * rowA 6 8 q) ≤ db_2341 6 8 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_6_9 :
    (∑ q : Fin 9, y4_2341 q * rowA 6 9 q) ≤ db_2341 6 9 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7_0 :
    (∑ q : Fin 9, y4_2341 q * rowA 7 0 q) ≤ db_2341 7 0 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7_1 :
    (∑ q : Fin 9, y4_2341 q * rowA 7 1 q) ≤ db_2341 7 1 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7_2 :
    (∑ q : Fin 9, y4_2341 q * rowA 7 2 q) ≤ db_2341 7 2 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7_3 :
    (∑ q : Fin 9, y4_2341 q * rowA 7 3 q) ≤ db_2341 7 3 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7_4 :
    (∑ q : Fin 9, y4_2341 q * rowA 7 4 q) ≤ db_2341 7 4 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7_5 :
    (∑ q : Fin 9, y4_2341 q * rowA 7 5 q) ≤ db_2341 7 5 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7_6 :
    (∑ q : Fin 9, y4_2341 q * rowA 7 6 q) ≤ db_2341 7 6 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7_7 :
    (∑ q : Fin 9, y4_2341 q * rowA 7 7 q) ≤ db_2341 7 7 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7_8 :
    (∑ q : Fin 9, y4_2341 q * rowA 7 8 q) ≤ db_2341 7 8 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_7_9 :
    (∑ q : Fin 9, y4_2341 q * rowA 7 9 q) ≤ db_2341 7 9 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8_0 :
    (∑ q : Fin 9, y4_2341 q * rowA 8 0 q) ≤ db_2341 8 0 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8_1 :
    (∑ q : Fin 9, y4_2341 q * rowA 8 1 q) ≤ db_2341 8 1 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8_2 :
    (∑ q : Fin 9, y4_2341 q * rowA 8 2 q) ≤ db_2341 8 2 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8_3 :
    (∑ q : Fin 9, y4_2341 q * rowA 8 3 q) ≤ db_2341 8 3 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8_4 :
    (∑ q : Fin 9, y4_2341 q * rowA 8 4 q) ≤ db_2341 8 4 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8_5 :
    (∑ q : Fin 9, y4_2341 q * rowA 8 5 q) ≤ db_2341 8 5 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8_6 :
    (∑ q : Fin 9, y4_2341 q * rowA 8 6 q) ≤ db_2341 8 6 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8_7 :
    (∑ q : Fin 9, y4_2341 q * rowA 8 7 q) ≤ db_2341 8 7 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8_8 :
    (∑ q : Fin 9, y4_2341 q * rowA 8 8 q) ≤ db_2341 8 8 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_8_9 :
    (∑ q : Fin 9, y4_2341 q * rowA 8 9 q) ≤ db_2341 8 9 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9_0 :
    (∑ q : Fin 9, y4_2341 q * rowA 9 0 q) ≤ db_2341 9 0 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9_1 :
    (∑ q : Fin 9, y4_2341 q * rowA 9 1 q) ≤ db_2341 9 1 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9_2 :
    (∑ q : Fin 9, y4_2341 q * rowA 9 2 q) ≤ db_2341 9 2 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9_3 :
    (∑ q : Fin 9, y4_2341 q * rowA 9 3 q) ≤ db_2341 9 3 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9_4 :
    (∑ q : Fin 9, y4_2341 q * rowA 9 4 q) ≤ db_2341 9 4 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9_5 :
    (∑ q : Fin 9, y4_2341 q * rowA 9 5 q) ≤ db_2341 9 5 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9_6 :
    (∑ q : Fin 9, y4_2341 q * rowA 9 6 q) ≤ db_2341 9 6 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9_7 :
    (∑ q : Fin 9, y4_2341 q * rowA 9 7 q) ≤ db_2341 9 7 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9_8 :
    (∑ q : Fin 9, y4_2341 q * rowA 9 8 q) ≤ db_2341 9 8 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_9_9 :
    (∑ q : Fin 9, y4_2341 q * rowA 9 9 q) ≤ db_2341 9 9 := by
  norm_num [y4_2341, rowA, db_2341, Fin.sum_univ_succ]

theorem row_cap_2341_0 (j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA 0 j q) ≤ db_2341 0 j := by
  fin_cases j
  · exact row_cap_2341_0_0
  · exact row_cap_2341_0_1
  · exact row_cap_2341_0_2
  · exact row_cap_2341_0_3
  · exact row_cap_2341_0_4
  · exact row_cap_2341_0_5
  · exact row_cap_2341_0_6
  · exact row_cap_2341_0_7
  · exact row_cap_2341_0_8
  · exact row_cap_2341_0_9

theorem row_cap_2341_1 (j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA 1 j q) ≤ db_2341 1 j := by
  fin_cases j
  · exact row_cap_2341_1_0
  · exact row_cap_2341_1_1
  · exact row_cap_2341_1_2
  · exact row_cap_2341_1_3
  · exact row_cap_2341_1_4
  · exact row_cap_2341_1_5
  · exact row_cap_2341_1_6
  · exact row_cap_2341_1_7
  · exact row_cap_2341_1_8
  · exact row_cap_2341_1_9

theorem row_cap_2341_2 (j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA 2 j q) ≤ db_2341 2 j := by
  fin_cases j
  · exact row_cap_2341_2_0
  · exact row_cap_2341_2_1
  · exact row_cap_2341_2_2
  · exact row_cap_2341_2_3
  · exact row_cap_2341_2_4
  · exact row_cap_2341_2_5
  · exact row_cap_2341_2_6
  · exact row_cap_2341_2_7
  · exact row_cap_2341_2_8
  · exact row_cap_2341_2_9

theorem row_cap_2341_3 (j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA 3 j q) ≤ db_2341 3 j := by
  fin_cases j
  · exact row_cap_2341_3_0
  · exact row_cap_2341_3_1
  · exact row_cap_2341_3_2
  · exact row_cap_2341_3_3
  · exact row_cap_2341_3_4
  · exact row_cap_2341_3_5
  · exact row_cap_2341_3_6
  · exact row_cap_2341_3_7
  · exact row_cap_2341_3_8
  · exact row_cap_2341_3_9

theorem row_cap_2341_4 (j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA 4 j q) ≤ db_2341 4 j := by
  fin_cases j
  · exact row_cap_2341_4_0
  · exact row_cap_2341_4_1
  · exact row_cap_2341_4_2
  · exact row_cap_2341_4_3
  · exact row_cap_2341_4_4
  · exact row_cap_2341_4_5
  · exact row_cap_2341_4_6
  · exact row_cap_2341_4_7
  · exact row_cap_2341_4_8
  · exact row_cap_2341_4_9

theorem row_cap_2341_5 (j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA 5 j q) ≤ db_2341 5 j := by
  fin_cases j
  · exact row_cap_2341_5_0
  · exact row_cap_2341_5_1
  · exact row_cap_2341_5_2
  · exact row_cap_2341_5_3
  · exact row_cap_2341_5_4
  · exact row_cap_2341_5_5
  · exact row_cap_2341_5_6
  · exact row_cap_2341_5_7
  · exact row_cap_2341_5_8
  · exact row_cap_2341_5_9

theorem row_cap_2341_6 (j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA 6 j q) ≤ db_2341 6 j := by
  fin_cases j
  · exact row_cap_2341_6_0
  · exact row_cap_2341_6_1
  · exact row_cap_2341_6_2
  · exact row_cap_2341_6_3
  · exact row_cap_2341_6_4
  · exact row_cap_2341_6_5
  · exact row_cap_2341_6_6
  · exact row_cap_2341_6_7
  · exact row_cap_2341_6_8
  · exact row_cap_2341_6_9

theorem row_cap_2341_7 (j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA 7 j q) ≤ db_2341 7 j := by
  fin_cases j
  · exact row_cap_2341_7_0
  · exact row_cap_2341_7_1
  · exact row_cap_2341_7_2
  · exact row_cap_2341_7_3
  · exact row_cap_2341_7_4
  · exact row_cap_2341_7_5
  · exact row_cap_2341_7_6
  · exact row_cap_2341_7_7
  · exact row_cap_2341_7_8
  · exact row_cap_2341_7_9

theorem row_cap_2341_8 (j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA 8 j q) ≤ db_2341 8 j := by
  fin_cases j
  · exact row_cap_2341_8_0
  · exact row_cap_2341_8_1
  · exact row_cap_2341_8_2
  · exact row_cap_2341_8_3
  · exact row_cap_2341_8_4
  · exact row_cap_2341_8_5
  · exact row_cap_2341_8_6
  · exact row_cap_2341_8_7
  · exact row_cap_2341_8_8
  · exact row_cap_2341_8_9

theorem row_cap_2341_9 (j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA 9 j q) ≤ db_2341 9 j := by
  fin_cases j
  · exact row_cap_2341_9_0
  · exact row_cap_2341_9_1
  · exact row_cap_2341_9_2
  · exact row_cap_2341_9_3
  · exact row_cap_2341_9_4
  · exact row_cap_2341_9_5
  · exact row_cap_2341_9_6
  · exact row_cap_2341_9_7
  · exact row_cap_2341_9_8
  · exact row_cap_2341_9_9

theorem row_cap_2341 (i j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA i j q) ≤ db_2341 i j := by
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

def db_2368 : Fin 10 → Fin 10 → ℚ
  | ⟨0, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : ℚ) / 8
  | ⟨0, _⟩, ⟨2, _⟩ => (1 : ℚ) / 8
  | ⟨0, _⟩, ⟨3, _⟩ => (1 : ℚ) / 8
  | ⟨0, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨0, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨0, _⟩, ⟨6, _⟩ => (5 : ℚ) / 8
  | ⟨0, _⟩, ⟨7, _⟩ => (3 : ℚ) / 4
  | ⟨0, _⟩, ⟨8, _⟩ => (3 : ℚ) / 4
  | ⟨0, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨1, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨1, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨1, _⟩, ⟨2, _⟩ => (1 : ℚ) / 8
  | ⟨1, _⟩, ⟨3, _⟩ => (1 : ℚ) / 8
  | ⟨1, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨1, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨1, _⟩, ⟨6, _⟩ => (5 : ℚ) / 8
  | ⟨1, _⟩, ⟨7, _⟩ => (3 : ℚ) / 4
  | ⟨1, _⟩, ⟨8, _⟩ => (3 : ℚ) / 4
  | ⟨1, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨2, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨3, _⟩ => (1 : ℚ) / 8
  | ⟨2, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨2, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨2, _⟩, ⟨6, _⟩ => (5 : ℚ) / 8
  | ⟨2, _⟩, ⟨7, _⟩ => (3 : ℚ) / 4
  | ⟨2, _⟩, ⟨8, _⟩ => (3 : ℚ) / 4
  | ⟨2, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨3, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨3, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨3, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨3, _⟩, ⟨6, _⟩ => (5 : ℚ) / 8
  | ⟨3, _⟩, ⟨7, _⟩ => (3 : ℚ) / 4
  | ⟨3, _⟩, ⟨8, _⟩ => (3 : ℚ) / 4
  | ⟨3, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨4, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 4
  | ⟨4, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 4
  | ⟨4, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 4
  | ⟨4, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 4
  | ⟨4, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨4, _⟩, ⟨5, _⟩ => (1 : ℚ) / 8
  | ⟨4, _⟩, ⟨6, _⟩ => (3 : ℚ) / 8
  | ⟨4, _⟩, ⟨7, _⟩ => (3 : ℚ) / 8
  | ⟨4, _⟩, ⟨8, _⟩ => (3 : ℚ) / 8
  | ⟨4, _⟩, ⟨9, _⟩ => (3 : ℚ) / 4
  | ⟨5, _⟩, ⟨0, _⟩ => (-3 : ℚ) / 8
  | ⟨5, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨6, _⟩ => (1 : ℚ) / 4
  | ⟨5, _⟩, ⟨7, _⟩ => (3 : ℚ) / 8
  | ⟨5, _⟩, ⟨8, _⟩ => (3 : ℚ) / 8
  | ⟨5, _⟩, ⟨9, _⟩ => (5 : ℚ) / 8
  | ⟨6, _⟩, ⟨0, _⟩ => (-3 : ℚ) / 8
  | ⟨6, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 4
  | ⟨6, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 4
  | ⟨6, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 4
  | ⟨6, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨7, _⟩ => (3 : ℚ) / 8
  | ⟨6, _⟩, ⟨8, _⟩ => (3 : ℚ) / 8
  | ⟨6, _⟩, ⟨9, _⟩ => (5 : ℚ) / 8
  | ⟨7, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 4
  | ⟨7, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 8
  | ⟨7, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨7, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨8, _⟩ => (1 : ℚ) / 8
  | ⟨7, _⟩, ⟨9, _⟩ => (1 : ℚ) / 2
  | ⟨8, _⟩, ⟨0, _⟩ => (-5 : ℚ) / 8
  | ⟨8, _⟩, ⟨1, _⟩ => (-5 : ℚ) / 8
  | ⟨8, _⟩, ⟨2, _⟩ => (-5 : ℚ) / 8
  | ⟨8, _⟩, ⟨3, _⟩ => (-5 : ℚ) / 8
  | ⟨8, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 4
  | ⟨8, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 4
  | ⟨8, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨7, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨8, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨9, _⟩ => (3 : ℚ) / 8
  | ⟨9, _⟩, ⟨0, _⟩ => (-1 : ℚ)
  | ⟨9, _⟩, ⟨1, _⟩ => (-7 : ℚ) / 8
  | ⟨9, _⟩, ⟨2, _⟩ => (-7 : ℚ) / 8
  | ⟨9, _⟩, ⟨3, _⟩ => (-7 : ℚ) / 8
  | ⟨9, _⟩, ⟨4, _⟩ => (-5 : ℚ) / 8
  | ⟨9, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 2
  | ⟨9, _⟩, ⟨6, _⟩ => (-3 : ℚ) / 8
  | ⟨9, _⟩, ⟨7, _⟩ => (-1 : ℚ) / 4
  | ⟨9, _⟩, ⟨8, _⟩ => (-1 : ℚ) / 4
  | ⟨9, _⟩, ⟨9, _⟩ => (0 : ℚ)

theorem row_cap_2368_0_0 :
    (∑ q : Fin 9, y4_2368 q * rowA 0 0 q) ≤ db_2368 0 0 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_0_1 :
    (∑ q : Fin 9, y4_2368 q * rowA 0 1 q) ≤ db_2368 0 1 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_0_2 :
    (∑ q : Fin 9, y4_2368 q * rowA 0 2 q) ≤ db_2368 0 2 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_0_3 :
    (∑ q : Fin 9, y4_2368 q * rowA 0 3 q) ≤ db_2368 0 3 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_0_4 :
    (∑ q : Fin 9, y4_2368 q * rowA 0 4 q) ≤ db_2368 0 4 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_0_5 :
    (∑ q : Fin 9, y4_2368 q * rowA 0 5 q) ≤ db_2368 0 5 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_0_6 :
    (∑ q : Fin 9, y4_2368 q * rowA 0 6 q) ≤ db_2368 0 6 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_0_7 :
    (∑ q : Fin 9, y4_2368 q * rowA 0 7 q) ≤ db_2368 0 7 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_0_8 :
    (∑ q : Fin 9, y4_2368 q * rowA 0 8 q) ≤ db_2368 0 8 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_0_9 :
    (∑ q : Fin 9, y4_2368 q * rowA 0 9 q) ≤ db_2368 0 9 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1_0 :
    (∑ q : Fin 9, y4_2368 q * rowA 1 0 q) ≤ db_2368 1 0 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1_1 :
    (∑ q : Fin 9, y4_2368 q * rowA 1 1 q) ≤ db_2368 1 1 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1_2 :
    (∑ q : Fin 9, y4_2368 q * rowA 1 2 q) ≤ db_2368 1 2 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1_3 :
    (∑ q : Fin 9, y4_2368 q * rowA 1 3 q) ≤ db_2368 1 3 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1_4 :
    (∑ q : Fin 9, y4_2368 q * rowA 1 4 q) ≤ db_2368 1 4 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1_5 :
    (∑ q : Fin 9, y4_2368 q * rowA 1 5 q) ≤ db_2368 1 5 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1_6 :
    (∑ q : Fin 9, y4_2368 q * rowA 1 6 q) ≤ db_2368 1 6 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1_7 :
    (∑ q : Fin 9, y4_2368 q * rowA 1 7 q) ≤ db_2368 1 7 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1_8 :
    (∑ q : Fin 9, y4_2368 q * rowA 1 8 q) ≤ db_2368 1 8 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_1_9 :
    (∑ q : Fin 9, y4_2368 q * rowA 1 9 q) ≤ db_2368 1 9 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2_0 :
    (∑ q : Fin 9, y4_2368 q * rowA 2 0 q) ≤ db_2368 2 0 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2_1 :
    (∑ q : Fin 9, y4_2368 q * rowA 2 1 q) ≤ db_2368 2 1 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2_2 :
    (∑ q : Fin 9, y4_2368 q * rowA 2 2 q) ≤ db_2368 2 2 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2_3 :
    (∑ q : Fin 9, y4_2368 q * rowA 2 3 q) ≤ db_2368 2 3 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2_4 :
    (∑ q : Fin 9, y4_2368 q * rowA 2 4 q) ≤ db_2368 2 4 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2_5 :
    (∑ q : Fin 9, y4_2368 q * rowA 2 5 q) ≤ db_2368 2 5 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2_6 :
    (∑ q : Fin 9, y4_2368 q * rowA 2 6 q) ≤ db_2368 2 6 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2_7 :
    (∑ q : Fin 9, y4_2368 q * rowA 2 7 q) ≤ db_2368 2 7 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2_8 :
    (∑ q : Fin 9, y4_2368 q * rowA 2 8 q) ≤ db_2368 2 8 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_2_9 :
    (∑ q : Fin 9, y4_2368 q * rowA 2 9 q) ≤ db_2368 2 9 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3_0 :
    (∑ q : Fin 9, y4_2368 q * rowA 3 0 q) ≤ db_2368 3 0 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3_1 :
    (∑ q : Fin 9, y4_2368 q * rowA 3 1 q) ≤ db_2368 3 1 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3_2 :
    (∑ q : Fin 9, y4_2368 q * rowA 3 2 q) ≤ db_2368 3 2 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3_3 :
    (∑ q : Fin 9, y4_2368 q * rowA 3 3 q) ≤ db_2368 3 3 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3_4 :
    (∑ q : Fin 9, y4_2368 q * rowA 3 4 q) ≤ db_2368 3 4 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3_5 :
    (∑ q : Fin 9, y4_2368 q * rowA 3 5 q) ≤ db_2368 3 5 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3_6 :
    (∑ q : Fin 9, y4_2368 q * rowA 3 6 q) ≤ db_2368 3 6 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3_7 :
    (∑ q : Fin 9, y4_2368 q * rowA 3 7 q) ≤ db_2368 3 7 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3_8 :
    (∑ q : Fin 9, y4_2368 q * rowA 3 8 q) ≤ db_2368 3 8 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_3_9 :
    (∑ q : Fin 9, y4_2368 q * rowA 3 9 q) ≤ db_2368 3 9 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4_0 :
    (∑ q : Fin 9, y4_2368 q * rowA 4 0 q) ≤ db_2368 4 0 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4_1 :
    (∑ q : Fin 9, y4_2368 q * rowA 4 1 q) ≤ db_2368 4 1 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4_2 :
    (∑ q : Fin 9, y4_2368 q * rowA 4 2 q) ≤ db_2368 4 2 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4_3 :
    (∑ q : Fin 9, y4_2368 q * rowA 4 3 q) ≤ db_2368 4 3 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4_4 :
    (∑ q : Fin 9, y4_2368 q * rowA 4 4 q) ≤ db_2368 4 4 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4_5 :
    (∑ q : Fin 9, y4_2368 q * rowA 4 5 q) ≤ db_2368 4 5 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4_6 :
    (∑ q : Fin 9, y4_2368 q * rowA 4 6 q) ≤ db_2368 4 6 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4_7 :
    (∑ q : Fin 9, y4_2368 q * rowA 4 7 q) ≤ db_2368 4 7 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4_8 :
    (∑ q : Fin 9, y4_2368 q * rowA 4 8 q) ≤ db_2368 4 8 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_4_9 :
    (∑ q : Fin 9, y4_2368 q * rowA 4 9 q) ≤ db_2368 4 9 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5_0 :
    (∑ q : Fin 9, y4_2368 q * rowA 5 0 q) ≤ db_2368 5 0 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5_1 :
    (∑ q : Fin 9, y4_2368 q * rowA 5 1 q) ≤ db_2368 5 1 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5_2 :
    (∑ q : Fin 9, y4_2368 q * rowA 5 2 q) ≤ db_2368 5 2 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5_3 :
    (∑ q : Fin 9, y4_2368 q * rowA 5 3 q) ≤ db_2368 5 3 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5_4 :
    (∑ q : Fin 9, y4_2368 q * rowA 5 4 q) ≤ db_2368 5 4 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5_5 :
    (∑ q : Fin 9, y4_2368 q * rowA 5 5 q) ≤ db_2368 5 5 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5_6 :
    (∑ q : Fin 9, y4_2368 q * rowA 5 6 q) ≤ db_2368 5 6 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5_7 :
    (∑ q : Fin 9, y4_2368 q * rowA 5 7 q) ≤ db_2368 5 7 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5_8 :
    (∑ q : Fin 9, y4_2368 q * rowA 5 8 q) ≤ db_2368 5 8 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_5_9 :
    (∑ q : Fin 9, y4_2368 q * rowA 5 9 q) ≤ db_2368 5 9 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6_0 :
    (∑ q : Fin 9, y4_2368 q * rowA 6 0 q) ≤ db_2368 6 0 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6_1 :
    (∑ q : Fin 9, y4_2368 q * rowA 6 1 q) ≤ db_2368 6 1 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6_2 :
    (∑ q : Fin 9, y4_2368 q * rowA 6 2 q) ≤ db_2368 6 2 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6_3 :
    (∑ q : Fin 9, y4_2368 q * rowA 6 3 q) ≤ db_2368 6 3 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6_4 :
    (∑ q : Fin 9, y4_2368 q * rowA 6 4 q) ≤ db_2368 6 4 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6_5 :
    (∑ q : Fin 9, y4_2368 q * rowA 6 5 q) ≤ db_2368 6 5 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6_6 :
    (∑ q : Fin 9, y4_2368 q * rowA 6 6 q) ≤ db_2368 6 6 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6_7 :
    (∑ q : Fin 9, y4_2368 q * rowA 6 7 q) ≤ db_2368 6 7 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6_8 :
    (∑ q : Fin 9, y4_2368 q * rowA 6 8 q) ≤ db_2368 6 8 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_6_9 :
    (∑ q : Fin 9, y4_2368 q * rowA 6 9 q) ≤ db_2368 6 9 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7_0 :
    (∑ q : Fin 9, y4_2368 q * rowA 7 0 q) ≤ db_2368 7 0 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7_1 :
    (∑ q : Fin 9, y4_2368 q * rowA 7 1 q) ≤ db_2368 7 1 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7_2 :
    (∑ q : Fin 9, y4_2368 q * rowA 7 2 q) ≤ db_2368 7 2 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7_3 :
    (∑ q : Fin 9, y4_2368 q * rowA 7 3 q) ≤ db_2368 7 3 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7_4 :
    (∑ q : Fin 9, y4_2368 q * rowA 7 4 q) ≤ db_2368 7 4 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7_5 :
    (∑ q : Fin 9, y4_2368 q * rowA 7 5 q) ≤ db_2368 7 5 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7_6 :
    (∑ q : Fin 9, y4_2368 q * rowA 7 6 q) ≤ db_2368 7 6 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7_7 :
    (∑ q : Fin 9, y4_2368 q * rowA 7 7 q) ≤ db_2368 7 7 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7_8 :
    (∑ q : Fin 9, y4_2368 q * rowA 7 8 q) ≤ db_2368 7 8 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_7_9 :
    (∑ q : Fin 9, y4_2368 q * rowA 7 9 q) ≤ db_2368 7 9 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8_0 :
    (∑ q : Fin 9, y4_2368 q * rowA 8 0 q) ≤ db_2368 8 0 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8_1 :
    (∑ q : Fin 9, y4_2368 q * rowA 8 1 q) ≤ db_2368 8 1 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8_2 :
    (∑ q : Fin 9, y4_2368 q * rowA 8 2 q) ≤ db_2368 8 2 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8_3 :
    (∑ q : Fin 9, y4_2368 q * rowA 8 3 q) ≤ db_2368 8 3 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8_4 :
    (∑ q : Fin 9, y4_2368 q * rowA 8 4 q) ≤ db_2368 8 4 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8_5 :
    (∑ q : Fin 9, y4_2368 q * rowA 8 5 q) ≤ db_2368 8 5 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8_6 :
    (∑ q : Fin 9, y4_2368 q * rowA 8 6 q) ≤ db_2368 8 6 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8_7 :
    (∑ q : Fin 9, y4_2368 q * rowA 8 7 q) ≤ db_2368 8 7 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8_8 :
    (∑ q : Fin 9, y4_2368 q * rowA 8 8 q) ≤ db_2368 8 8 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_8_9 :
    (∑ q : Fin 9, y4_2368 q * rowA 8 9 q) ≤ db_2368 8 9 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9_0 :
    (∑ q : Fin 9, y4_2368 q * rowA 9 0 q) ≤ db_2368 9 0 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9_1 :
    (∑ q : Fin 9, y4_2368 q * rowA 9 1 q) ≤ db_2368 9 1 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9_2 :
    (∑ q : Fin 9, y4_2368 q * rowA 9 2 q) ≤ db_2368 9 2 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9_3 :
    (∑ q : Fin 9, y4_2368 q * rowA 9 3 q) ≤ db_2368 9 3 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9_4 :
    (∑ q : Fin 9, y4_2368 q * rowA 9 4 q) ≤ db_2368 9 4 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9_5 :
    (∑ q : Fin 9, y4_2368 q * rowA 9 5 q) ≤ db_2368 9 5 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9_6 :
    (∑ q : Fin 9, y4_2368 q * rowA 9 6 q) ≤ db_2368 9 6 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9_7 :
    (∑ q : Fin 9, y4_2368 q * rowA 9 7 q) ≤ db_2368 9 7 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9_8 :
    (∑ q : Fin 9, y4_2368 q * rowA 9 8 q) ≤ db_2368 9 8 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_9_9 :
    (∑ q : Fin 9, y4_2368 q * rowA 9 9 q) ≤ db_2368 9 9 := by
  norm_num [y4_2368, rowA, db_2368, Fin.sum_univ_succ]

theorem row_cap_2368_0 (j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA 0 j q) ≤ db_2368 0 j := by
  fin_cases j
  · exact row_cap_2368_0_0
  · exact row_cap_2368_0_1
  · exact row_cap_2368_0_2
  · exact row_cap_2368_0_3
  · exact row_cap_2368_0_4
  · exact row_cap_2368_0_5
  · exact row_cap_2368_0_6
  · exact row_cap_2368_0_7
  · exact row_cap_2368_0_8
  · exact row_cap_2368_0_9

theorem row_cap_2368_1 (j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA 1 j q) ≤ db_2368 1 j := by
  fin_cases j
  · exact row_cap_2368_1_0
  · exact row_cap_2368_1_1
  · exact row_cap_2368_1_2
  · exact row_cap_2368_1_3
  · exact row_cap_2368_1_4
  · exact row_cap_2368_1_5
  · exact row_cap_2368_1_6
  · exact row_cap_2368_1_7
  · exact row_cap_2368_1_8
  · exact row_cap_2368_1_9

theorem row_cap_2368_2 (j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA 2 j q) ≤ db_2368 2 j := by
  fin_cases j
  · exact row_cap_2368_2_0
  · exact row_cap_2368_2_1
  · exact row_cap_2368_2_2
  · exact row_cap_2368_2_3
  · exact row_cap_2368_2_4
  · exact row_cap_2368_2_5
  · exact row_cap_2368_2_6
  · exact row_cap_2368_2_7
  · exact row_cap_2368_2_8
  · exact row_cap_2368_2_9

theorem row_cap_2368_3 (j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA 3 j q) ≤ db_2368 3 j := by
  fin_cases j
  · exact row_cap_2368_3_0
  · exact row_cap_2368_3_1
  · exact row_cap_2368_3_2
  · exact row_cap_2368_3_3
  · exact row_cap_2368_3_4
  · exact row_cap_2368_3_5
  · exact row_cap_2368_3_6
  · exact row_cap_2368_3_7
  · exact row_cap_2368_3_8
  · exact row_cap_2368_3_9

theorem row_cap_2368_4 (j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA 4 j q) ≤ db_2368 4 j := by
  fin_cases j
  · exact row_cap_2368_4_0
  · exact row_cap_2368_4_1
  · exact row_cap_2368_4_2
  · exact row_cap_2368_4_3
  · exact row_cap_2368_4_4
  · exact row_cap_2368_4_5
  · exact row_cap_2368_4_6
  · exact row_cap_2368_4_7
  · exact row_cap_2368_4_8
  · exact row_cap_2368_4_9

theorem row_cap_2368_5 (j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA 5 j q) ≤ db_2368 5 j := by
  fin_cases j
  · exact row_cap_2368_5_0
  · exact row_cap_2368_5_1
  · exact row_cap_2368_5_2
  · exact row_cap_2368_5_3
  · exact row_cap_2368_5_4
  · exact row_cap_2368_5_5
  · exact row_cap_2368_5_6
  · exact row_cap_2368_5_7
  · exact row_cap_2368_5_8
  · exact row_cap_2368_5_9

theorem row_cap_2368_6 (j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA 6 j q) ≤ db_2368 6 j := by
  fin_cases j
  · exact row_cap_2368_6_0
  · exact row_cap_2368_6_1
  · exact row_cap_2368_6_2
  · exact row_cap_2368_6_3
  · exact row_cap_2368_6_4
  · exact row_cap_2368_6_5
  · exact row_cap_2368_6_6
  · exact row_cap_2368_6_7
  · exact row_cap_2368_6_8
  · exact row_cap_2368_6_9

theorem row_cap_2368_7 (j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA 7 j q) ≤ db_2368 7 j := by
  fin_cases j
  · exact row_cap_2368_7_0
  · exact row_cap_2368_7_1
  · exact row_cap_2368_7_2
  · exact row_cap_2368_7_3
  · exact row_cap_2368_7_4
  · exact row_cap_2368_7_5
  · exact row_cap_2368_7_6
  · exact row_cap_2368_7_7
  · exact row_cap_2368_7_8
  · exact row_cap_2368_7_9

theorem row_cap_2368_8 (j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA 8 j q) ≤ db_2368 8 j := by
  fin_cases j
  · exact row_cap_2368_8_0
  · exact row_cap_2368_8_1
  · exact row_cap_2368_8_2
  · exact row_cap_2368_8_3
  · exact row_cap_2368_8_4
  · exact row_cap_2368_8_5
  · exact row_cap_2368_8_6
  · exact row_cap_2368_8_7
  · exact row_cap_2368_8_8
  · exact row_cap_2368_8_9

theorem row_cap_2368_9 (j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA 9 j q) ≤ db_2368 9 j := by
  fin_cases j
  · exact row_cap_2368_9_0
  · exact row_cap_2368_9_1
  · exact row_cap_2368_9_2
  · exact row_cap_2368_9_3
  · exact row_cap_2368_9_4
  · exact row_cap_2368_9_5
  · exact row_cap_2368_9_6
  · exact row_cap_2368_9_7
  · exact row_cap_2368_9_8
  · exact row_cap_2368_9_9

theorem row_cap_2368 (i j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA i j q) ≤ db_2368 i j := by
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

def db_2370 : Fin 10 → Fin 10 → ℚ
  | ⟨0, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : ℚ) / 4
  | ⟨0, _⟩, ⟨2, _⟩ => (1 : ℚ) / 4
  | ⟨0, _⟩, ⟨3, _⟩ => (1 : ℚ) / 4
  | ⟨0, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨0, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨0, _⟩, ⟨6, _⟩ => (5 : ℚ) / 8
  | ⟨0, _⟩, ⟨7, _⟩ => (7 : ℚ) / 8
  | ⟨0, _⟩, ⟨8, _⟩ => (7 : ℚ) / 8
  | ⟨0, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨1, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨1, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨1, _⟩, ⟨2, _⟩ => (1 : ℚ) / 4
  | ⟨1, _⟩, ⟨3, _⟩ => (1 : ℚ) / 4
  | ⟨1, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨1, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨1, _⟩, ⟨6, _⟩ => (5 : ℚ) / 8
  | ⟨1, _⟩, ⟨7, _⟩ => (7 : ℚ) / 8
  | ⟨1, _⟩, ⟨8, _⟩ => (7 : ℚ) / 8
  | ⟨1, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨2, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨2, _⟩, ⟨3, _⟩ => (1 : ℚ) / 4
  | ⟨2, _⟩, ⟨4, _⟩ => (3 : ℚ) / 8
  | ⟨2, _⟩, ⟨5, _⟩ => (1 : ℚ) / 2
  | ⟨2, _⟩, ⟨6, _⟩ => (5 : ℚ) / 8
  | ⟨2, _⟩, ⟨7, _⟩ => (7 : ℚ) / 8
  | ⟨2, _⟩, ⟨8, _⟩ => (7 : ℚ) / 8
  | ⟨2, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨3, _⟩, ⟨0, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨3, _⟩ => (0 : ℚ)
  | ⟨3, _⟩, ⟨4, _⟩ => (1 : ℚ) / 4
  | ⟨3, _⟩, ⟨5, _⟩ => (3 : ℚ) / 8
  | ⟨3, _⟩, ⟨6, _⟩ => (5 : ℚ) / 8
  | ⟨3, _⟩, ⟨7, _⟩ => (5 : ℚ) / 8
  | ⟨3, _⟩, ⟨8, _⟩ => (5 : ℚ) / 8
  | ⟨3, _⟩, ⟨9, _⟩ => (1 : ℚ)
  | ⟨4, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 4
  | ⟨4, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨4, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨4, _⟩, ⟨3, _⟩ => (0 : ℚ)
  | ⟨4, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨4, _⟩, ⟨5, _⟩ => (1 : ℚ) / 4
  | ⟨4, _⟩, ⟨6, _⟩ => (3 : ℚ) / 8
  | ⟨4, _⟩, ⟨7, _⟩ => (1 : ℚ) / 2
  | ⟨4, _⟩, ⟨8, _⟩ => (1 : ℚ) / 2
  | ⟨4, _⟩, ⟨9, _⟩ => (3 : ℚ) / 4
  | ⟨5, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 4
  | ⟨5, _⟩, ⟨1, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨2, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨3, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨4, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨5, _⟩, ⟨6, _⟩ => (3 : ℚ) / 8
  | ⟨5, _⟩, ⟨7, _⟩ => (1 : ℚ) / 2
  | ⟨5, _⟩, ⟨8, _⟩ => (1 : ℚ) / 2
  | ⟨5, _⟩, ⟨9, _⟩ => (3 : ℚ) / 4
  | ⟨6, _⟩, ⟨0, _⟩ => (-5 : ℚ) / 16
  | ⟨6, _⟩, ⟨1, _⟩ => (-5 : ℚ) / 16
  | ⟨6, _⟩, ⟨2, _⟩ => (-5 : ℚ) / 16
  | ⟨6, _⟩, ⟨3, _⟩ => (-5 : ℚ) / 16
  | ⟨6, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 16
  | ⟨6, _⟩, ⟨5, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨6, _⟩, ⟨7, _⟩ => (5 : ℚ) / 16
  | ⟨6, _⟩, ⟨8, _⟩ => (5 : ℚ) / 16
  | ⟨6, _⟩, ⟨9, _⟩ => (11 : ℚ) / 16
  | ⟨7, _⟩, ⟨0, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 2
  | ⟨7, _⟩, ⟨4, _⟩ => (-1 : ℚ) / 4
  | ⟨7, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 8
  | ⟨7, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨7, _⟩ => (0 : ℚ)
  | ⟨7, _⟩, ⟨8, _⟩ => (1 : ℚ) / 8
  | ⟨7, _⟩, ⟨9, _⟩ => (1 : ℚ) / 2
  | ⟨8, _⟩, ⟨0, _⟩ => (-5 : ℚ) / 8
  | ⟨8, _⟩, ⟨1, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨2, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨3, _⟩ => (-1 : ℚ) / 2
  | ⟨8, _⟩, ⟨4, _⟩ => (-3 : ℚ) / 8
  | ⟨8, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 4
  | ⟨8, _⟩, ⟨6, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨7, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨8, _⟩ => (0 : ℚ)
  | ⟨8, _⟩, ⟨9, _⟩ => (3 : ℚ) / 8
  | ⟨9, _⟩, ⟨0, _⟩ => (-1 : ℚ)
  | ⟨9, _⟩, ⟨1, _⟩ => (-3 : ℚ) / 4
  | ⟨9, _⟩, ⟨2, _⟩ => (-3 : ℚ) / 4
  | ⟨9, _⟩, ⟨3, _⟩ => (-3 : ℚ) / 4
  | ⟨9, _⟩, ⟨4, _⟩ => (-5 : ℚ) / 8
  | ⟨9, _⟩, ⟨5, _⟩ => (-1 : ℚ) / 2
  | ⟨9, _⟩, ⟨6, _⟩ => (-3 : ℚ) / 8
  | ⟨9, _⟩, ⟨7, _⟩ => (-1 : ℚ) / 8
  | ⟨9, _⟩, ⟨8, _⟩ => (-1 : ℚ) / 8
  | ⟨9, _⟩, ⟨9, _⟩ => (0 : ℚ)

theorem row_cap_2370_0_0 :
    (∑ q : Fin 9, y4_2370 q * rowA 0 0 q) ≤ db_2370 0 0 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_0_1 :
    (∑ q : Fin 9, y4_2370 q * rowA 0 1 q) ≤ db_2370 0 1 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_0_2 :
    (∑ q : Fin 9, y4_2370 q * rowA 0 2 q) ≤ db_2370 0 2 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_0_3 :
    (∑ q : Fin 9, y4_2370 q * rowA 0 3 q) ≤ db_2370 0 3 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_0_4 :
    (∑ q : Fin 9, y4_2370 q * rowA 0 4 q) ≤ db_2370 0 4 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_0_5 :
    (∑ q : Fin 9, y4_2370 q * rowA 0 5 q) ≤ db_2370 0 5 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_0_6 :
    (∑ q : Fin 9, y4_2370 q * rowA 0 6 q) ≤ db_2370 0 6 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_0_7 :
    (∑ q : Fin 9, y4_2370 q * rowA 0 7 q) ≤ db_2370 0 7 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_0_8 :
    (∑ q : Fin 9, y4_2370 q * rowA 0 8 q) ≤ db_2370 0 8 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_0_9 :
    (∑ q : Fin 9, y4_2370 q * rowA 0 9 q) ≤ db_2370 0 9 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1_0 :
    (∑ q : Fin 9, y4_2370 q * rowA 1 0 q) ≤ db_2370 1 0 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1_1 :
    (∑ q : Fin 9, y4_2370 q * rowA 1 1 q) ≤ db_2370 1 1 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1_2 :
    (∑ q : Fin 9, y4_2370 q * rowA 1 2 q) ≤ db_2370 1 2 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1_3 :
    (∑ q : Fin 9, y4_2370 q * rowA 1 3 q) ≤ db_2370 1 3 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1_4 :
    (∑ q : Fin 9, y4_2370 q * rowA 1 4 q) ≤ db_2370 1 4 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1_5 :
    (∑ q : Fin 9, y4_2370 q * rowA 1 5 q) ≤ db_2370 1 5 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1_6 :
    (∑ q : Fin 9, y4_2370 q * rowA 1 6 q) ≤ db_2370 1 6 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1_7 :
    (∑ q : Fin 9, y4_2370 q * rowA 1 7 q) ≤ db_2370 1 7 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1_8 :
    (∑ q : Fin 9, y4_2370 q * rowA 1 8 q) ≤ db_2370 1 8 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_1_9 :
    (∑ q : Fin 9, y4_2370 q * rowA 1 9 q) ≤ db_2370 1 9 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2_0 :
    (∑ q : Fin 9, y4_2370 q * rowA 2 0 q) ≤ db_2370 2 0 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2_1 :
    (∑ q : Fin 9, y4_2370 q * rowA 2 1 q) ≤ db_2370 2 1 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2_2 :
    (∑ q : Fin 9, y4_2370 q * rowA 2 2 q) ≤ db_2370 2 2 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2_3 :
    (∑ q : Fin 9, y4_2370 q * rowA 2 3 q) ≤ db_2370 2 3 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2_4 :
    (∑ q : Fin 9, y4_2370 q * rowA 2 4 q) ≤ db_2370 2 4 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2_5 :
    (∑ q : Fin 9, y4_2370 q * rowA 2 5 q) ≤ db_2370 2 5 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2_6 :
    (∑ q : Fin 9, y4_2370 q * rowA 2 6 q) ≤ db_2370 2 6 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2_7 :
    (∑ q : Fin 9, y4_2370 q * rowA 2 7 q) ≤ db_2370 2 7 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2_8 :
    (∑ q : Fin 9, y4_2370 q * rowA 2 8 q) ≤ db_2370 2 8 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_2_9 :
    (∑ q : Fin 9, y4_2370 q * rowA 2 9 q) ≤ db_2370 2 9 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3_0 :
    (∑ q : Fin 9, y4_2370 q * rowA 3 0 q) ≤ db_2370 3 0 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3_1 :
    (∑ q : Fin 9, y4_2370 q * rowA 3 1 q) ≤ db_2370 3 1 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3_2 :
    (∑ q : Fin 9, y4_2370 q * rowA 3 2 q) ≤ db_2370 3 2 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3_3 :
    (∑ q : Fin 9, y4_2370 q * rowA 3 3 q) ≤ db_2370 3 3 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3_4 :
    (∑ q : Fin 9, y4_2370 q * rowA 3 4 q) ≤ db_2370 3 4 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3_5 :
    (∑ q : Fin 9, y4_2370 q * rowA 3 5 q) ≤ db_2370 3 5 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3_6 :
    (∑ q : Fin 9, y4_2370 q * rowA 3 6 q) ≤ db_2370 3 6 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3_7 :
    (∑ q : Fin 9, y4_2370 q * rowA 3 7 q) ≤ db_2370 3 7 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3_8 :
    (∑ q : Fin 9, y4_2370 q * rowA 3 8 q) ≤ db_2370 3 8 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_3_9 :
    (∑ q : Fin 9, y4_2370 q * rowA 3 9 q) ≤ db_2370 3 9 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4_0 :
    (∑ q : Fin 9, y4_2370 q * rowA 4 0 q) ≤ db_2370 4 0 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4_1 :
    (∑ q : Fin 9, y4_2370 q * rowA 4 1 q) ≤ db_2370 4 1 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4_2 :
    (∑ q : Fin 9, y4_2370 q * rowA 4 2 q) ≤ db_2370 4 2 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4_3 :
    (∑ q : Fin 9, y4_2370 q * rowA 4 3 q) ≤ db_2370 4 3 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4_4 :
    (∑ q : Fin 9, y4_2370 q * rowA 4 4 q) ≤ db_2370 4 4 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4_5 :
    (∑ q : Fin 9, y4_2370 q * rowA 4 5 q) ≤ db_2370 4 5 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4_6 :
    (∑ q : Fin 9, y4_2370 q * rowA 4 6 q) ≤ db_2370 4 6 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4_7 :
    (∑ q : Fin 9, y4_2370 q * rowA 4 7 q) ≤ db_2370 4 7 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4_8 :
    (∑ q : Fin 9, y4_2370 q * rowA 4 8 q) ≤ db_2370 4 8 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_4_9 :
    (∑ q : Fin 9, y4_2370 q * rowA 4 9 q) ≤ db_2370 4 9 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5_0 :
    (∑ q : Fin 9, y4_2370 q * rowA 5 0 q) ≤ db_2370 5 0 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5_1 :
    (∑ q : Fin 9, y4_2370 q * rowA 5 1 q) ≤ db_2370 5 1 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5_2 :
    (∑ q : Fin 9, y4_2370 q * rowA 5 2 q) ≤ db_2370 5 2 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5_3 :
    (∑ q : Fin 9, y4_2370 q * rowA 5 3 q) ≤ db_2370 5 3 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5_4 :
    (∑ q : Fin 9, y4_2370 q * rowA 5 4 q) ≤ db_2370 5 4 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5_5 :
    (∑ q : Fin 9, y4_2370 q * rowA 5 5 q) ≤ db_2370 5 5 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5_6 :
    (∑ q : Fin 9, y4_2370 q * rowA 5 6 q) ≤ db_2370 5 6 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5_7 :
    (∑ q : Fin 9, y4_2370 q * rowA 5 7 q) ≤ db_2370 5 7 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5_8 :
    (∑ q : Fin 9, y4_2370 q * rowA 5 8 q) ≤ db_2370 5 8 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_5_9 :
    (∑ q : Fin 9, y4_2370 q * rowA 5 9 q) ≤ db_2370 5 9 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6_0 :
    (∑ q : Fin 9, y4_2370 q * rowA 6 0 q) ≤ db_2370 6 0 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6_1 :
    (∑ q : Fin 9, y4_2370 q * rowA 6 1 q) ≤ db_2370 6 1 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6_2 :
    (∑ q : Fin 9, y4_2370 q * rowA 6 2 q) ≤ db_2370 6 2 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6_3 :
    (∑ q : Fin 9, y4_2370 q * rowA 6 3 q) ≤ db_2370 6 3 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6_4 :
    (∑ q : Fin 9, y4_2370 q * rowA 6 4 q) ≤ db_2370 6 4 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6_5 :
    (∑ q : Fin 9, y4_2370 q * rowA 6 5 q) ≤ db_2370 6 5 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6_6 :
    (∑ q : Fin 9, y4_2370 q * rowA 6 6 q) ≤ db_2370 6 6 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6_7 :
    (∑ q : Fin 9, y4_2370 q * rowA 6 7 q) ≤ db_2370 6 7 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6_8 :
    (∑ q : Fin 9, y4_2370 q * rowA 6 8 q) ≤ db_2370 6 8 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_6_9 :
    (∑ q : Fin 9, y4_2370 q * rowA 6 9 q) ≤ db_2370 6 9 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7_0 :
    (∑ q : Fin 9, y4_2370 q * rowA 7 0 q) ≤ db_2370 7 0 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7_1 :
    (∑ q : Fin 9, y4_2370 q * rowA 7 1 q) ≤ db_2370 7 1 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7_2 :
    (∑ q : Fin 9, y4_2370 q * rowA 7 2 q) ≤ db_2370 7 2 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7_3 :
    (∑ q : Fin 9, y4_2370 q * rowA 7 3 q) ≤ db_2370 7 3 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7_4 :
    (∑ q : Fin 9, y4_2370 q * rowA 7 4 q) ≤ db_2370 7 4 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7_5 :
    (∑ q : Fin 9, y4_2370 q * rowA 7 5 q) ≤ db_2370 7 5 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7_6 :
    (∑ q : Fin 9, y4_2370 q * rowA 7 6 q) ≤ db_2370 7 6 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7_7 :
    (∑ q : Fin 9, y4_2370 q * rowA 7 7 q) ≤ db_2370 7 7 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7_8 :
    (∑ q : Fin 9, y4_2370 q * rowA 7 8 q) ≤ db_2370 7 8 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_7_9 :
    (∑ q : Fin 9, y4_2370 q * rowA 7 9 q) ≤ db_2370 7 9 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8_0 :
    (∑ q : Fin 9, y4_2370 q * rowA 8 0 q) ≤ db_2370 8 0 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8_1 :
    (∑ q : Fin 9, y4_2370 q * rowA 8 1 q) ≤ db_2370 8 1 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8_2 :
    (∑ q : Fin 9, y4_2370 q * rowA 8 2 q) ≤ db_2370 8 2 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8_3 :
    (∑ q : Fin 9, y4_2370 q * rowA 8 3 q) ≤ db_2370 8 3 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8_4 :
    (∑ q : Fin 9, y4_2370 q * rowA 8 4 q) ≤ db_2370 8 4 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8_5 :
    (∑ q : Fin 9, y4_2370 q * rowA 8 5 q) ≤ db_2370 8 5 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8_6 :
    (∑ q : Fin 9, y4_2370 q * rowA 8 6 q) ≤ db_2370 8 6 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8_7 :
    (∑ q : Fin 9, y4_2370 q * rowA 8 7 q) ≤ db_2370 8 7 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8_8 :
    (∑ q : Fin 9, y4_2370 q * rowA 8 8 q) ≤ db_2370 8 8 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_8_9 :
    (∑ q : Fin 9, y4_2370 q * rowA 8 9 q) ≤ db_2370 8 9 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9_0 :
    (∑ q : Fin 9, y4_2370 q * rowA 9 0 q) ≤ db_2370 9 0 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9_1 :
    (∑ q : Fin 9, y4_2370 q * rowA 9 1 q) ≤ db_2370 9 1 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9_2 :
    (∑ q : Fin 9, y4_2370 q * rowA 9 2 q) ≤ db_2370 9 2 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9_3 :
    (∑ q : Fin 9, y4_2370 q * rowA 9 3 q) ≤ db_2370 9 3 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9_4 :
    (∑ q : Fin 9, y4_2370 q * rowA 9 4 q) ≤ db_2370 9 4 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9_5 :
    (∑ q : Fin 9, y4_2370 q * rowA 9 5 q) ≤ db_2370 9 5 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9_6 :
    (∑ q : Fin 9, y4_2370 q * rowA 9 6 q) ≤ db_2370 9 6 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9_7 :
    (∑ q : Fin 9, y4_2370 q * rowA 9 7 q) ≤ db_2370 9 7 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9_8 :
    (∑ q : Fin 9, y4_2370 q * rowA 9 8 q) ≤ db_2370 9 8 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_9_9 :
    (∑ q : Fin 9, y4_2370 q * rowA 9 9 q) ≤ db_2370 9 9 := by
  norm_num [y4_2370, rowA, db_2370, Fin.sum_univ_succ]

theorem row_cap_2370_0 (j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA 0 j q) ≤ db_2370 0 j := by
  fin_cases j
  · exact row_cap_2370_0_0
  · exact row_cap_2370_0_1
  · exact row_cap_2370_0_2
  · exact row_cap_2370_0_3
  · exact row_cap_2370_0_4
  · exact row_cap_2370_0_5
  · exact row_cap_2370_0_6
  · exact row_cap_2370_0_7
  · exact row_cap_2370_0_8
  · exact row_cap_2370_0_9

theorem row_cap_2370_1 (j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA 1 j q) ≤ db_2370 1 j := by
  fin_cases j
  · exact row_cap_2370_1_0
  · exact row_cap_2370_1_1
  · exact row_cap_2370_1_2
  · exact row_cap_2370_1_3
  · exact row_cap_2370_1_4
  · exact row_cap_2370_1_5
  · exact row_cap_2370_1_6
  · exact row_cap_2370_1_7
  · exact row_cap_2370_1_8
  · exact row_cap_2370_1_9

theorem row_cap_2370_2 (j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA 2 j q) ≤ db_2370 2 j := by
  fin_cases j
  · exact row_cap_2370_2_0
  · exact row_cap_2370_2_1
  · exact row_cap_2370_2_2
  · exact row_cap_2370_2_3
  · exact row_cap_2370_2_4
  · exact row_cap_2370_2_5
  · exact row_cap_2370_2_6
  · exact row_cap_2370_2_7
  · exact row_cap_2370_2_8
  · exact row_cap_2370_2_9

theorem row_cap_2370_3 (j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA 3 j q) ≤ db_2370 3 j := by
  fin_cases j
  · exact row_cap_2370_3_0
  · exact row_cap_2370_3_1
  · exact row_cap_2370_3_2
  · exact row_cap_2370_3_3
  · exact row_cap_2370_3_4
  · exact row_cap_2370_3_5
  · exact row_cap_2370_3_6
  · exact row_cap_2370_3_7
  · exact row_cap_2370_3_8
  · exact row_cap_2370_3_9

theorem row_cap_2370_4 (j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA 4 j q) ≤ db_2370 4 j := by
  fin_cases j
  · exact row_cap_2370_4_0
  · exact row_cap_2370_4_1
  · exact row_cap_2370_4_2
  · exact row_cap_2370_4_3
  · exact row_cap_2370_4_4
  · exact row_cap_2370_4_5
  · exact row_cap_2370_4_6
  · exact row_cap_2370_4_7
  · exact row_cap_2370_4_8
  · exact row_cap_2370_4_9

theorem row_cap_2370_5 (j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA 5 j q) ≤ db_2370 5 j := by
  fin_cases j
  · exact row_cap_2370_5_0
  · exact row_cap_2370_5_1
  · exact row_cap_2370_5_2
  · exact row_cap_2370_5_3
  · exact row_cap_2370_5_4
  · exact row_cap_2370_5_5
  · exact row_cap_2370_5_6
  · exact row_cap_2370_5_7
  · exact row_cap_2370_5_8
  · exact row_cap_2370_5_9

theorem row_cap_2370_6 (j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA 6 j q) ≤ db_2370 6 j := by
  fin_cases j
  · exact row_cap_2370_6_0
  · exact row_cap_2370_6_1
  · exact row_cap_2370_6_2
  · exact row_cap_2370_6_3
  · exact row_cap_2370_6_4
  · exact row_cap_2370_6_5
  · exact row_cap_2370_6_6
  · exact row_cap_2370_6_7
  · exact row_cap_2370_6_8
  · exact row_cap_2370_6_9

theorem row_cap_2370_7 (j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA 7 j q) ≤ db_2370 7 j := by
  fin_cases j
  · exact row_cap_2370_7_0
  · exact row_cap_2370_7_1
  · exact row_cap_2370_7_2
  · exact row_cap_2370_7_3
  · exact row_cap_2370_7_4
  · exact row_cap_2370_7_5
  · exact row_cap_2370_7_6
  · exact row_cap_2370_7_7
  · exact row_cap_2370_7_8
  · exact row_cap_2370_7_9

theorem row_cap_2370_8 (j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA 8 j q) ≤ db_2370 8 j := by
  fin_cases j
  · exact row_cap_2370_8_0
  · exact row_cap_2370_8_1
  · exact row_cap_2370_8_2
  · exact row_cap_2370_8_3
  · exact row_cap_2370_8_4
  · exact row_cap_2370_8_5
  · exact row_cap_2370_8_6
  · exact row_cap_2370_8_7
  · exact row_cap_2370_8_8
  · exact row_cap_2370_8_9

theorem row_cap_2370_9 (j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA 9 j q) ≤ db_2370 9 j := by
  fin_cases j
  · exact row_cap_2370_9_0
  · exact row_cap_2370_9_1
  · exact row_cap_2370_9_2
  · exact row_cap_2370_9_3
  · exact row_cap_2370_9_4
  · exact row_cap_2370_9_5
  · exact row_cap_2370_9_6
  · exact row_cap_2370_9_7
  · exact row_cap_2370_9_8
  · exact row_cap_2370_9_9

theorem row_cap_2370 (i j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA i j q) ≤ db_2370 i j := by
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
end N11Formalization.FrozenCapFourFieldRowCaps

#check @N11Formalization.FrozenCapFourFieldRowCaps.row_cap_1409
#check @N11Formalization.FrozenCapFourFieldRowCaps.row_cap_2370
