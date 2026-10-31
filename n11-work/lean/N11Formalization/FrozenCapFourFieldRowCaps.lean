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
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_0_1 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_0_2 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_0_3 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_0_4 :
    (1 : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_0_5 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_0_6 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_0_7 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_0_8 :
    (3 : ℚ) / 4 ≤ (7 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_0_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_1409_1_0 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_1_1 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_1_2 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_1_3 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_1_4 :
    (1 : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_1_5 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_1_6 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_1_7 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_1_8 :
    (3 : ℚ) / 4 ≤ (7 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_1_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_1409_2_0 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_2_1 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_2_2 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_2_3 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_2_4 :
    (1 : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_2_5 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_2_6 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_2_7 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_2_8 :
    (3 : ℚ) / 4 ≤ (7 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_2_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_1409_3_0 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_3_1 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_3_2 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_3_3 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_3_4 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_3_5 :
    (1 : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_3_6 :
    (1 : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_3_7 :
    (1 : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_3_8 :
    (1 : ℚ) / 2 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_3_9 :
    (3 : ℚ) / 4 ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_1409_4_0 :
    (-1 : ℚ) / 2 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_4_1 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_4_2 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_4_3 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_4_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_4_5 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_4_6 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_4_7 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_4_8 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_4_9 :
    (1 : ℚ) / 2 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_5_0 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_5_1 :
    (-3 : ℚ) / 4 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_5_2 :
    (-3 : ℚ) / 4 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_5_3 :
    (-1 : ℚ) / 2 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_5_4 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_5_5 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_5_6 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_5_7 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_5_8 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_5_9 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_6_0 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_6_1 :
    (-3 : ℚ) / 4 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_6_2 :
    (-3 : ℚ) / 4 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_6_3 :
    (-1 : ℚ) / 2 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_6_4 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_6_5 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_6_6 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_6_7 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_6_8 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_6_9 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_7_0 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_7_1 :
    (-3 : ℚ) / 4 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_7_2 :
    (-3 : ℚ) / 4 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_7_3 :
    (-1 : ℚ) / 2 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_7_4 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_7_5 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_7_6 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_7_7 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_7_8 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_7_9 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_8_0 :
    (-3 : ℚ) / 4 ≤ (-5 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_8_1 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_8_2 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_8_3 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_8_4 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_8_5 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_8_6 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_8_7 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_8_8 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409_8_9 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_9_0 :
    (-1 : ℚ) ≤ (-1 : ℚ) := by
  norm_num

theorem row_cap_1409_9_1 :
    (-1 : ℚ) ≤ (-3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_9_2 :
    (-1 : ℚ) ≤ (-3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_9_3 :
    (-3 : ℚ) / 4 ≤ (-3 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_9_4 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_1409_9_5 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_9_6 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_9_7 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_1409_9_8 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_1409_9_9 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_1409 (i j : Fin 10) :
    (∑ q : Fin 9, y4_1409 q * rowA i j q) ≤ db_1409 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [rowA, y4_1409, db_1409, Fin.sum_univ_succ]

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
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_0_1 :
    (0 : ℚ) ≤ (3 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_0_2 :
    (1 : ℚ) / 16 ≤ (3 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_0_3 :
    (1 : ℚ) / 16 ≤ (3 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_0_4 :
    (5 : ℚ) / 16 ≤ (5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_0_5 :
    (5 : ℚ) / 16 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_0_6 :
    (5 : ℚ) / 16 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_0_7 :
    (9 : ℚ) / 16 ≤ (11 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_0_8 :
    (9 : ℚ) / 16 ≤ (11 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_0_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2337_1_0 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_1_1 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_1_2 :
    (1 : ℚ) / 16 ≤ (3 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_1_3 :
    (1 : ℚ) / 16 ≤ (3 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_1_4 :
    (5 : ℚ) / 16 ≤ (5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_1_5 :
    (5 : ℚ) / 16 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_1_6 :
    (5 : ℚ) / 16 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_1_7 :
    (9 : ℚ) / 16 ≤ (11 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_1_8 :
    (9 : ℚ) / 16 ≤ (11 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_1_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2337_2_0 :
    (-1 : ℚ) / 16 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_2_1 :
    (-1 : ℚ) / 16 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_2_2 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_2_3 :
    (0 : ℚ) ≤ (3 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_2_4 :
    (1 : ℚ) / 4 ≤ (5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_2_5 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_2_6 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_2_7 :
    (1 : ℚ) / 2 ≤ (11 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_2_8 :
    (1 : ℚ) / 2 ≤ (11 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_2_9 :
    (15 : ℚ) / 16 ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2337_3_0 :
    (-1 : ℚ) / 16 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_3_1 :
    (-1 : ℚ) / 16 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_3_2 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_3_3 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_3_4 :
    (1 : ℚ) / 4 ≤ (5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_3_5 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_3_6 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_3_7 :
    (1 : ℚ) / 2 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2337_3_8 :
    (1 : ℚ) / 2 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2337_3_9 :
    (15 : ℚ) / 16 ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2337_4_0 :
    (-5 : ℚ) / 16 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_4_1 :
    (-5 : ℚ) / 16 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2337_4_2 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2337_4_3 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2337_4_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_4_5 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_4_6 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_4_7 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2337_4_8 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2337_4_9 :
    (11 : ℚ) / 16 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_5_0 :
    (-5 : ℚ) / 16 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_5_1 :
    (-5 : ℚ) / 16 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_5_2 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_5_3 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_5_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_5_5 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_5_6 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_5_7 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_5_8 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_5_9 :
    (11 : ℚ) / 16 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_6_0 :
    (-5 : ℚ) / 16 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_6_1 :
    (-5 : ℚ) / 16 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_6_2 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_6_3 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_6_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_6_5 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_6_6 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_6_7 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_6_8 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_6_9 :
    (11 : ℚ) / 16 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_7_0 :
    (-9 : ℚ) / 16 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_7_1 :
    (-9 : ℚ) / 16 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_7_2 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_7_3 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_7_4 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_7_5 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_7_6 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_7_7 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_7_8 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2337_7_9 :
    (7 : ℚ) / 16 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_8_0 :
    (-9 : ℚ) / 16 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_8_1 :
    (-9 : ℚ) / 16 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_8_2 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_8_3 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_8_4 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2337_8_5 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2337_8_6 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_8_7 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_8_8 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337_8_9 :
    (7 : ℚ) / 16 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_9_0 :
    (-1 : ℚ) ≤ (-1 : ℚ) := by
  norm_num

theorem row_cap_2337_9_1 :
    (-1 : ℚ) ≤ (-13 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_9_2 :
    (-15 : ℚ) / 16 ≤ (-13 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_9_3 :
    (-15 : ℚ) / 16 ≤ (-13 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_9_4 :
    (-11 : ℚ) / 16 ≤ (-11 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_9_5 :
    (-11 : ℚ) / 16 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_9_6 :
    (-11 : ℚ) / 16 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2337_9_7 :
    (-7 : ℚ) / 16 ≤ (-5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_9_8 :
    (-7 : ℚ) / 16 ≤ (-5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2337_9_9 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2337 (i j : Fin 10) :
    (∑ q : Fin 9, y4_2337 q * rowA i j q) ≤ db_2337 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [rowA, y4_2337, db_2337, Fin.sum_univ_succ]

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
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_0_1 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_0_2 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_0_3 :
    (1 : ℚ) / 8 ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_0_4 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_0_5 :
    (3 : ℚ) / 8 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_0_6 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_0_7 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_0_8 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_0_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2341_1_0 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_1_1 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_1_2 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_1_3 :
    (1 : ℚ) / 8 ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_1_4 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_1_5 :
    (3 : ℚ) / 8 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_1_6 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_1_7 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_1_8 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_1_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2341_2_0 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_2_1 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_2_2 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_2_3 :
    (1 : ℚ) / 8 ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_2_4 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_2_5 :
    (3 : ℚ) / 8 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_2_6 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_2_7 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_2_8 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_2_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2341_3_0 :
    (-1 : ℚ) / 8 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_3_1 :
    (-1 : ℚ) / 8 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_3_2 :
    (-1 : ℚ) / 8 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_3_3 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_3_4 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_3_5 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_3_6 :
    (1 : ℚ) / 2 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_3_7 :
    (1 : ℚ) / 2 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_3_8 :
    (1 : ℚ) / 2 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_3_9 :
    (7 : ℚ) / 8 ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2341_4_0 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_4_1 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_4_2 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_4_3 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_4_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_4_5 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_4_6 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_4_7 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_4_8 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_4_9 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_5_0 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_5_1 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_5_2 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_5_3 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_5_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_5_5 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_5_6 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_5_7 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_5_8 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_5_9 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_6_0 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_6_1 :
    (-5 : ℚ) / 8 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_6_2 :
    (-5 : ℚ) / 8 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_6_3 :
    (-1 : ℚ) / 2 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_6_4 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_6_5 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_6_6 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_6_7 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_6_8 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_6_9 :
    (3 : ℚ) / 8 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_7_0 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_7_1 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_7_2 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_7_3 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_7_4 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_7_5 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_7_6 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_7_7 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_7_8 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_7_9 :
    (3 : ℚ) / 8 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_8_0 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_8_1 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_8_2 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_8_3 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_8_4 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_8_5 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_8_6 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_8_7 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_8_8 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341_8_9 :
    (3 : ℚ) / 8 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_9_0 :
    (-1 : ℚ) ≤ (-1 : ℚ) := by
  norm_num

theorem row_cap_2341_9_1 :
    (-1 : ℚ) ≤ (-7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_9_2 :
    (-1 : ℚ) ≤ (-7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_9_3 :
    (-7 : ℚ) / 8 ≤ (-7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_9_4 :
    (-5 : ℚ) / 8 ≤ (-5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2341_9_5 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2341_9_6 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_9_7 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_9_8 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2341_9_9 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2341 (i j : Fin 10) :
    (∑ q : Fin 9, y4_2341 q * rowA i j q) ≤ db_2341 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [rowA, y4_2341, db_2341, Fin.sum_univ_succ]

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
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_0_1 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_0_2 :
    (1 : ℚ) / 8 ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_0_3 :
    (1 : ℚ) / 8 ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_0_4 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_0_5 :
    (3 : ℚ) / 8 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2368_0_6 :
    (3 : ℚ) / 8 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_0_7 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_0_8 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_0_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2368_1_0 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_1_1 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_1_2 :
    (1 : ℚ) / 8 ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_1_3 :
    (1 : ℚ) / 8 ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_1_4 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_1_5 :
    (3 : ℚ) / 8 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2368_1_6 :
    (3 : ℚ) / 8 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_1_7 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_1_8 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_1_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2368_2_0 :
    (-1 : ℚ) / 8 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_2_1 :
    (-1 : ℚ) / 8 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_2_2 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_2_3 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_2_4 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_2_5 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2368_2_6 :
    (1 : ℚ) / 4 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_2_7 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_2_8 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_2_9 :
    (7 : ℚ) / 8 ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2368_3_0 :
    (-1 : ℚ) / 8 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_3_1 :
    (-1 : ℚ) / 8 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_3_2 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_3_3 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_3_4 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_3_5 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2368_3_6 :
    (1 : ℚ) / 4 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_3_7 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_3_8 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_3_9 :
    (7 : ℚ) / 8 ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2368_4_0 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_4_1 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_4_2 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_4_3 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_4_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_4_5 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_4_6 :
    (0 : ℚ) ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_4_7 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_4_8 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_4_9 :
    (5 : ℚ) / 8 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_5_0 :
    (-3 : ℚ) / 8 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_5_1 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_5_2 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_5_3 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_5_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_5_5 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_5_6 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_5_7 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_5_8 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_5_9 :
    (5 : ℚ) / 8 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_6_0 :
    (-3 : ℚ) / 8 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_6_1 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_6_2 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_6_3 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_6_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_6_5 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_6_6 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_6_7 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_6_8 :
    (3 : ℚ) / 8 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_6_9 :
    (5 : ℚ) / 8 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_7_0 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2368_7_1 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2368_7_2 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2368_7_3 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2368_7_4 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_7_5 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_7_6 :
    (-3 : ℚ) / 8 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_7_7 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_7_8 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_7_9 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2368_8_0 :
    (-3 : ℚ) / 4 ≤ (-5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_8_1 :
    (-3 : ℚ) / 4 ≤ (-5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_8_2 :
    (-5 : ℚ) / 8 ≤ (-5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_8_3 :
    (-5 : ℚ) / 8 ≤ (-5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_8_4 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_8_5 :
    (-3 : ℚ) / 8 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_8_6 :
    (-3 : ℚ) / 8 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_8_7 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_8_8 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368_8_9 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_9_0 :
    (-1 : ℚ) ≤ (-1 : ℚ) := by
  norm_num

theorem row_cap_2368_9_1 :
    (-1 : ℚ) ≤ (-7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_9_2 :
    (-7 : ℚ) / 8 ≤ (-7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_9_3 :
    (-7 : ℚ) / 8 ≤ (-7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_9_4 :
    (-5 : ℚ) / 8 ≤ (-5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_9_5 :
    (-5 : ℚ) / 8 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2368_9_6 :
    (-5 : ℚ) / 8 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2368_9_7 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_9_8 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2368_9_9 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2368 (i j : Fin 10) :
    (∑ q : Fin 9, y4_2368 q * rowA i j q) ≤ db_2368 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [rowA, y4_2368, db_2368, Fin.sum_univ_succ]

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
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_0_1 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_0_2 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_0_3 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_0_4 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_0_5 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_0_6 :
    (9 : ℚ) / 16 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_0_7 :
    (3 : ℚ) / 4 ≤ (7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_0_8 :
    (3 : ℚ) / 4 ≤ (7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_0_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2370_1_0 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_1_1 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_1_2 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_1_3 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_1_4 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_1_5 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_1_6 :
    (9 : ℚ) / 16 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_1_7 :
    (3 : ℚ) / 4 ≤ (7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_1_8 :
    (3 : ℚ) / 4 ≤ (7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_1_9 :
    (1 : ℚ) ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2370_2_0 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_2_1 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_2_2 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_2_3 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_2_4 :
    (0 : ℚ) ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_2_5 :
    (0 : ℚ) ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_2_6 :
    (5 : ℚ) / 16 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_2_7 :
    (1 : ℚ) / 2 ≤ (7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_2_8 :
    (1 : ℚ) / 2 ≤ (7 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_2_9 :
    (3 : ℚ) / 4 ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2370_3_0 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_3_1 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_3_2 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_3_3 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_3_4 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_3_5 :
    (0 : ℚ) ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_3_6 :
    (5 : ℚ) / 16 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_3_7 :
    (1 : ℚ) / 2 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_3_8 :
    (1 : ℚ) / 2 ≤ (5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_3_9 :
    (3 : ℚ) / 4 ≤ (1 : ℚ) := by
  norm_num

theorem row_cap_2370_4_0 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_4_1 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_4_2 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_4_3 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_4_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_4_5 :
    (0 : ℚ) ≤ (1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_4_6 :
    (5 : ℚ) / 16 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_4_7 :
    (1 : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_4_8 :
    (1 : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_4_9 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_5_0 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_5_1 :
    (-1 : ℚ) / 4 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_5_2 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_5_3 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_5_4 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_5_5 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_5_6 :
    (5 : ℚ) / 16 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_5_7 :
    (1 : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_5_8 :
    (1 : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_5_9 :
    (3 : ℚ) / 4 ≤ (3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_6_0 :
    (-9 : ℚ) / 16 ≤ (-5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2370_6_1 :
    (-9 : ℚ) / 16 ≤ (-5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2370_6_2 :
    (-5 : ℚ) / 16 ≤ (-5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2370_6_3 :
    (-5 : ℚ) / 16 ≤ (-5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2370_6_4 :
    (-5 : ℚ) / 16 ≤ (-1 : ℚ) / 16 := by
  norm_num

theorem row_cap_2370_6_5 :
    (-5 : ℚ) / 16 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_6_6 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_6_7 :
    (3 : ℚ) / 16 ≤ (5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2370_6_8 :
    (3 : ℚ) / 16 ≤ (5 : ℚ) / 16 := by
  norm_num

theorem row_cap_2370_6_9 :
    (7 : ℚ) / 16 ≤ (11 : ℚ) / 16 := by
  norm_num

theorem row_cap_2370_7_0 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_7_1 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_7_2 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_7_3 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_7_4 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_7_5 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_7_6 :
    (-3 : ℚ) / 16 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_7_7 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_7_8 :
    (0 : ℚ) ≤ (1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_7_9 :
    (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_8_0 :
    (-3 : ℚ) / 4 ≤ (-5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_8_1 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_8_2 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_8_3 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_8_4 :
    (-1 : ℚ) / 2 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_8_5 :
    (-1 : ℚ) / 2 ≤ (-1 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_8_6 :
    (-3 : ℚ) / 16 ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_8_7 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_8_8 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370_8_9 :
    (1 : ℚ) / 4 ≤ (3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_9_0 :
    (-1 : ℚ) ≤ (-1 : ℚ) := by
  norm_num

theorem row_cap_2370_9_1 :
    (-1 : ℚ) ≤ (-3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_9_2 :
    (-3 : ℚ) / 4 ≤ (-3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_9_3 :
    (-3 : ℚ) / 4 ≤ (-3 : ℚ) / 4 := by
  norm_num

theorem row_cap_2370_9_4 :
    (-3 : ℚ) / 4 ≤ (-5 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_9_5 :
    (-3 : ℚ) / 4 ≤ (-1 : ℚ) / 2 := by
  norm_num

theorem row_cap_2370_9_6 :
    (-7 : ℚ) / 16 ≤ (-3 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_9_7 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_9_8 :
    (-1 : ℚ) / 4 ≤ (-1 : ℚ) / 8 := by
  norm_num

theorem row_cap_2370_9_9 :
    (0 : ℚ) ≤ (0 : ℚ) := by
  norm_num

theorem row_cap_2370 (i j : Fin 10) :
    (∑ q : Fin 9, y4_2370 q * rowA i j q) ≤ db_2370 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [rowA, y4_2370, db_2370, Fin.sum_univ_succ]

end
end N11Formalization.FrozenCapFourFieldRowCaps

#check @N11Formalization.FrozenCapFourFieldRowCaps.row_cap_1409
#check @N11Formalization.FrozenCapFourFieldRowCaps.row_cap_2370
