import N11Formalization.FrozenCapRationalCore
import N11Formalization.FrozenCapRowCap2370

/-! Exact five-field rescue witness for residual node 2370, with all 100
row caps against the frozen `DBMSourceTree` matrix. Generated deterministically
by `ops/lanes/C/emit_five_field_2370.py`; this does not claim packet existence. -/
set_option autoImplicit false
namespace N11Formalization.FrozenCapFiveField2370
open Finset ConvexMinorantCore DBMMinorantDual
open scoped BigOperators
noncomputable section
open FrozenCapRationalCore

def y5_2370 : Fin 9 → ℚ := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (1 : ℚ) / 4, (1 : ℚ) / 8, (1 : ℚ) / 8, (0 : ℚ), (1 : ℚ) / 8, (3 : ℚ) / 8]

theorem nonneg_2370 : ∀ q, 0 ≤ y5_2370 q := by
  intro q; fin_cases q <;> norm_num [y5_2370]

theorem sum_2370 : (∑ q : Fin 9, y5_2370 q) = 1 := by
  norm_num [y5_2370, Fin.sum_univ_succ]

theorem endpoint_2370 (q : Fin 9) :
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2370 q) = E_2370 q := by
  fin_cases q <;> norm_num [G_2370, E_2370, endpointLo,
    N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.DQ,
    N11Formalization.FlashCosine.Lq, N11Formalization.FlashCosine.LQ,
    N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]

def H5_2370 : Fin 9 → ℚ := ![(0 : ℚ), (0 : ℚ), (0 : ℚ), (-135811126358392648161780382120252451096092386913271037883371670634701 : ℚ) / 450359962736148880074525900800000000000000000000000000000000000000000000, (-135811126359392562946913168186882085154321465581763669496940544964259 : ℚ) / 900719925472297760149051801600000000000000000000000000000000000000000000, (495026871942298517319921173713923825259661743329706308573416940452481 : ℚ) / 1801439850944595520298103603200000000000000000000000000000000000000000000, (0 : ℚ), (-381460841296599939974831130681947503830398079821492352184942502065327 : ℚ) / 1801439850944595520298103603200000000000000000000000000000000000000000000, (0 : ℚ)]

theorem weighted_terms_2370 (q : Fin 9) : y5_2370 q * E_2370 q = H5_2370 q := by
  fin_cases q <;> norm_num [y5_2370, E_2370, H5_2370]

theorem strict_gain_2370 : F0_2370 + ∑ q : Fin 9, y5_2370 q *
    endpointLo N11Formalization.FlashCosine.Dq N11Formalization.FlashCosine.DQ (G_2370 q) <
      N11Formalization.FlashCosineLeaf284Bridge.T ^ 2 := by
  simp only [endpoint_2370]
  have hsum : (∑ q : Fin 9, y5_2370 q * E_2370 q) = ∑ q : Fin 9, H5_2370 q := by
    apply Finset.sum_congr rfl
    intro q _
    exact weighted_terms_2370 q
  rw [hsum]
  norm_num [F0_2370, H5_2370, N11Formalization.FlashCosineLeaf284Bridge.T,
    Fin.sum_univ_succ]

theorem row_cap_0_0 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 0 q) ≤
      FrozenCapRowCap2370.db 0 0 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_0_1 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 1 q) ≤
      FrozenCapRowCap2370.db 0 1 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_0_2 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 2 q) ≤
      FrozenCapRowCap2370.db 0 2 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_0_3 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 3 q) ≤
      FrozenCapRowCap2370.db 0 3 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_0_4 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 4 q) ≤
      FrozenCapRowCap2370.db 0 4 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_0_5 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 5 q) ≤
      FrozenCapRowCap2370.db 0 5 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_0_6 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 6 q) ≤
      FrozenCapRowCap2370.db 0 6 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_0_7 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 7 q) ≤
      FrozenCapRowCap2370.db 0 7 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_0_8 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 8 q) ≤
      FrozenCapRowCap2370.db 0 8 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_0_9 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 9 q) ≤
      FrozenCapRowCap2370.db 0 9 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_1_0 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 0 q) ≤
      FrozenCapRowCap2370.db 1 0 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_1_1 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 1 q) ≤
      FrozenCapRowCap2370.db 1 1 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_1_2 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 2 q) ≤
      FrozenCapRowCap2370.db 1 2 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_1_3 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 3 q) ≤
      FrozenCapRowCap2370.db 1 3 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_1_4 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 4 q) ≤
      FrozenCapRowCap2370.db 1 4 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_1_5 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 5 q) ≤
      FrozenCapRowCap2370.db 1 5 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_1_6 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 6 q) ≤
      FrozenCapRowCap2370.db 1 6 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_1_7 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 7 q) ≤
      FrozenCapRowCap2370.db 1 7 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_1_8 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 8 q) ≤
      FrozenCapRowCap2370.db 1 8 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_1_9 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 9 q) ≤
      FrozenCapRowCap2370.db 1 9 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_2_0 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 0 q) ≤
      FrozenCapRowCap2370.db 2 0 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_2_1 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 1 q) ≤
      FrozenCapRowCap2370.db 2 1 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_2_2 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 2 q) ≤
      FrozenCapRowCap2370.db 2 2 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_2_3 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 3 q) ≤
      FrozenCapRowCap2370.db 2 3 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_2_4 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 4 q) ≤
      FrozenCapRowCap2370.db 2 4 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_2_5 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 5 q) ≤
      FrozenCapRowCap2370.db 2 5 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_2_6 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 6 q) ≤
      FrozenCapRowCap2370.db 2 6 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_2_7 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 7 q) ≤
      FrozenCapRowCap2370.db 2 7 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_2_8 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 8 q) ≤
      FrozenCapRowCap2370.db 2 8 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_2_9 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 9 q) ≤
      FrozenCapRowCap2370.db 2 9 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_3_0 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 0 q) ≤
      FrozenCapRowCap2370.db 3 0 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_3_1 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 1 q) ≤
      FrozenCapRowCap2370.db 3 1 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_3_2 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 2 q) ≤
      FrozenCapRowCap2370.db 3 2 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_3_3 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 3 q) ≤
      FrozenCapRowCap2370.db 3 3 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_3_4 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 4 q) ≤
      FrozenCapRowCap2370.db 3 4 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_3_5 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 5 q) ≤
      FrozenCapRowCap2370.db 3 5 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_3_6 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 6 q) ≤
      FrozenCapRowCap2370.db 3 6 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_3_7 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 7 q) ≤
      FrozenCapRowCap2370.db 3 7 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_3_8 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 8 q) ≤
      FrozenCapRowCap2370.db 3 8 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_3_9 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 9 q) ≤
      FrozenCapRowCap2370.db 3 9 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_4_0 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 0 q) ≤
      FrozenCapRowCap2370.db 4 0 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_4_1 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 1 q) ≤
      FrozenCapRowCap2370.db 4 1 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_4_2 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 2 q) ≤
      FrozenCapRowCap2370.db 4 2 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_4_3 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 3 q) ≤
      FrozenCapRowCap2370.db 4 3 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_4_4 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 4 q) ≤
      FrozenCapRowCap2370.db 4 4 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_4_5 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 5 q) ≤
      FrozenCapRowCap2370.db 4 5 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_4_6 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 6 q) ≤
      FrozenCapRowCap2370.db 4 6 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_4_7 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 7 q) ≤
      FrozenCapRowCap2370.db 4 7 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_4_8 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 8 q) ≤
      FrozenCapRowCap2370.db 4 8 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_4_9 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 9 q) ≤
      FrozenCapRowCap2370.db 4 9 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_5_0 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 0 q) ≤
      FrozenCapRowCap2370.db 5 0 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_5_1 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 1 q) ≤
      FrozenCapRowCap2370.db 5 1 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_5_2 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 2 q) ≤
      FrozenCapRowCap2370.db 5 2 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_5_3 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 3 q) ≤
      FrozenCapRowCap2370.db 5 3 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_5_4 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 4 q) ≤
      FrozenCapRowCap2370.db 5 4 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_5_5 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 5 q) ≤
      FrozenCapRowCap2370.db 5 5 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_5_6 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 6 q) ≤
      FrozenCapRowCap2370.db 5 6 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_5_7 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 7 q) ≤
      FrozenCapRowCap2370.db 5 7 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_5_8 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 8 q) ≤
      FrozenCapRowCap2370.db 5 8 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_5_9 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 9 q) ≤
      FrozenCapRowCap2370.db 5 9 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_6_0 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 0 q) ≤
      FrozenCapRowCap2370.db 6 0 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_6_1 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 1 q) ≤
      FrozenCapRowCap2370.db 6 1 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_6_2 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 2 q) ≤
      FrozenCapRowCap2370.db 6 2 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_6_3 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 3 q) ≤
      FrozenCapRowCap2370.db 6 3 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_6_4 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 4 q) ≤
      FrozenCapRowCap2370.db 6 4 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_6_5 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 5 q) ≤
      FrozenCapRowCap2370.db 6 5 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_6_6 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 6 q) ≤
      FrozenCapRowCap2370.db 6 6 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_6_7 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 7 q) ≤
      FrozenCapRowCap2370.db 6 7 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_6_8 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 8 q) ≤
      FrozenCapRowCap2370.db 6 8 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_6_9 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 9 q) ≤
      FrozenCapRowCap2370.db 6 9 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_7_0 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 0 q) ≤
      FrozenCapRowCap2370.db 7 0 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_7_1 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 1 q) ≤
      FrozenCapRowCap2370.db 7 1 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_7_2 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 2 q) ≤
      FrozenCapRowCap2370.db 7 2 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_7_3 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 3 q) ≤
      FrozenCapRowCap2370.db 7 3 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_7_4 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 4 q) ≤
      FrozenCapRowCap2370.db 7 4 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_7_5 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 5 q) ≤
      FrozenCapRowCap2370.db 7 5 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_7_6 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 6 q) ≤
      FrozenCapRowCap2370.db 7 6 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_7_7 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 7 q) ≤
      FrozenCapRowCap2370.db 7 7 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_7_8 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 8 q) ≤
      FrozenCapRowCap2370.db 7 8 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_7_9 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 9 q) ≤
      FrozenCapRowCap2370.db 7 9 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_8_0 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 0 q) ≤
      FrozenCapRowCap2370.db 8 0 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_8_1 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 1 q) ≤
      FrozenCapRowCap2370.db 8 1 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_8_2 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 2 q) ≤
      FrozenCapRowCap2370.db 8 2 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_8_3 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 3 q) ≤
      FrozenCapRowCap2370.db 8 3 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_8_4 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 4 q) ≤
      FrozenCapRowCap2370.db 8 4 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_8_5 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 5 q) ≤
      FrozenCapRowCap2370.db 8 5 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_8_6 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 6 q) ≤
      FrozenCapRowCap2370.db 8 6 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_8_7 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 7 q) ≤
      FrozenCapRowCap2370.db 8 7 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_8_8 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 8 q) ≤
      FrozenCapRowCap2370.db 8 8 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_8_9 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 9 q) ≤
      FrozenCapRowCap2370.db 8 9 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_9_0 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 0 q) ≤
      FrozenCapRowCap2370.db 9 0 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_9_1 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 1 q) ≤
      FrozenCapRowCap2370.db 9 1 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_9_2 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 2 q) ≤
      FrozenCapRowCap2370.db 9 2 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_9_3 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 3 q) ≤
      FrozenCapRowCap2370.db 9 3 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_9_4 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 4 q) ≤
      FrozenCapRowCap2370.db 9 4 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_9_5 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 5 q) ≤
      FrozenCapRowCap2370.db 9 5 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_9_6 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 6 q) ≤
      FrozenCapRowCap2370.db 9 6 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_9_7 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 7 q) ≤
      FrozenCapRowCap2370.db 9 7 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_9_8 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 8 q) ≤
      FrozenCapRowCap2370.db 9 8 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]
theorem row_cap_9_9 :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 9 q) ≤
      FrozenCapRowCap2370.db 9 9 := by
  norm_num [y5_2370, FrozenCapRowCap2370.rowA, FrozenCapRowCap2370.db,
    Fin.sum_univ_succ]

theorem row_cap_0 (j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 0 j q) ≤
      FrozenCapRowCap2370.db 0 j := by
  fin_cases j
  · exact row_cap_0_0
  · exact row_cap_0_1
  · exact row_cap_0_2
  · exact row_cap_0_3
  · exact row_cap_0_4
  · exact row_cap_0_5
  · exact row_cap_0_6
  · exact row_cap_0_7
  · exact row_cap_0_8
  · exact row_cap_0_9
theorem row_cap_1 (j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 1 j q) ≤
      FrozenCapRowCap2370.db 1 j := by
  fin_cases j
  · exact row_cap_1_0
  · exact row_cap_1_1
  · exact row_cap_1_2
  · exact row_cap_1_3
  · exact row_cap_1_4
  · exact row_cap_1_5
  · exact row_cap_1_6
  · exact row_cap_1_7
  · exact row_cap_1_8
  · exact row_cap_1_9
theorem row_cap_2 (j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 2 j q) ≤
      FrozenCapRowCap2370.db 2 j := by
  fin_cases j
  · exact row_cap_2_0
  · exact row_cap_2_1
  · exact row_cap_2_2
  · exact row_cap_2_3
  · exact row_cap_2_4
  · exact row_cap_2_5
  · exact row_cap_2_6
  · exact row_cap_2_7
  · exact row_cap_2_8
  · exact row_cap_2_9
theorem row_cap_3 (j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 3 j q) ≤
      FrozenCapRowCap2370.db 3 j := by
  fin_cases j
  · exact row_cap_3_0
  · exact row_cap_3_1
  · exact row_cap_3_2
  · exact row_cap_3_3
  · exact row_cap_3_4
  · exact row_cap_3_5
  · exact row_cap_3_6
  · exact row_cap_3_7
  · exact row_cap_3_8
  · exact row_cap_3_9
theorem row_cap_4 (j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 4 j q) ≤
      FrozenCapRowCap2370.db 4 j := by
  fin_cases j
  · exact row_cap_4_0
  · exact row_cap_4_1
  · exact row_cap_4_2
  · exact row_cap_4_3
  · exact row_cap_4_4
  · exact row_cap_4_5
  · exact row_cap_4_6
  · exact row_cap_4_7
  · exact row_cap_4_8
  · exact row_cap_4_9
theorem row_cap_5 (j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 5 j q) ≤
      FrozenCapRowCap2370.db 5 j := by
  fin_cases j
  · exact row_cap_5_0
  · exact row_cap_5_1
  · exact row_cap_5_2
  · exact row_cap_5_3
  · exact row_cap_5_4
  · exact row_cap_5_5
  · exact row_cap_5_6
  · exact row_cap_5_7
  · exact row_cap_5_8
  · exact row_cap_5_9
theorem row_cap_6 (j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 6 j q) ≤
      FrozenCapRowCap2370.db 6 j := by
  fin_cases j
  · exact row_cap_6_0
  · exact row_cap_6_1
  · exact row_cap_6_2
  · exact row_cap_6_3
  · exact row_cap_6_4
  · exact row_cap_6_5
  · exact row_cap_6_6
  · exact row_cap_6_7
  · exact row_cap_6_8
  · exact row_cap_6_9
theorem row_cap_7 (j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 7 j q) ≤
      FrozenCapRowCap2370.db 7 j := by
  fin_cases j
  · exact row_cap_7_0
  · exact row_cap_7_1
  · exact row_cap_7_2
  · exact row_cap_7_3
  · exact row_cap_7_4
  · exact row_cap_7_5
  · exact row_cap_7_6
  · exact row_cap_7_7
  · exact row_cap_7_8
  · exact row_cap_7_9
theorem row_cap_8 (j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 8 j q) ≤
      FrozenCapRowCap2370.db 8 j := by
  fin_cases j
  · exact row_cap_8_0
  · exact row_cap_8_1
  · exact row_cap_8_2
  · exact row_cap_8_3
  · exact row_cap_8_4
  · exact row_cap_8_5
  · exact row_cap_8_6
  · exact row_cap_8_7
  · exact row_cap_8_8
  · exact row_cap_8_9
theorem row_cap_9 (j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA 9 j q) ≤
      FrozenCapRowCap2370.db 9 j := by
  fin_cases j
  · exact row_cap_9_0
  · exact row_cap_9_1
  · exact row_cap_9_2
  · exact row_cap_9_3
  · exact row_cap_9_4
  · exact row_cap_9_5
  · exact row_cap_9_6
  · exact row_cap_9_7
  · exact row_cap_9_8
  · exact row_cap_9_9

theorem row_cap_2370 (i j : Fin 10) :
    (∑ q : Fin 9, y5_2370 q * FrozenCapRowCap2370.rowA i j q) ≤
      FrozenCapRowCap2370.db i j := by
  fin_cases i
  · exact row_cap_0 j
  · exact row_cap_1 j
  · exact row_cap_2 j
  · exact row_cap_3 j
  · exact row_cap_4 j
  · exact row_cap_5 j
  · exact row_cap_6 j
  · exact row_cap_7 j
  · exact row_cap_8 j
  · exact row_cap_9 j

end
end N11Formalization.FrozenCapFiveField2370

#check @N11Formalization.FrozenCapFiveField2370.strict_gain_2370
#check @N11Formalization.FrozenCapFiveField2370.row_cap_2370
#print axioms N11Formalization.FrozenCapFiveField2370.strict_gain_2370
#print axioms N11Formalization.FrozenCapFiveField2370.row_cap_2370
