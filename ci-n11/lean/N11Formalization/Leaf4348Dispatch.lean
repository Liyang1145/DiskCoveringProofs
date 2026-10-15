import Mathlib
import N11Formalization.Leaf4348Oracle
import N11Formalization.Leaf4348Pairs_s1
import N11Formalization.Leaf4348Pairs_s2
import N11Formalization.Leaf4348Pairs_s3
import N11Formalization.Leaf4348Pairs_s4
import N11Formalization.Leaf4348Pairs_s5
import N11Formalization.Leaf4348Pairs_s6

/-!
  **Leaf 4348 dispatch: the per-pair safe minorants, from the six pairs stages.**

  DRAFT for the Lead's serial slot.  No `sorry`, no custom `axiom`, no `native_decide`.

  `hsafe_all` has exactly the type of the single hypothesis of
  `Leaf4348Oracle.leaf4348_oracle_gt`, so combining them yields the unconditional
  whole-cell statement.  Each of the 36 cases: two DBM rows by `norm_num` on `Leaf4348LP.dbm`,
  the pair's `cell<i><j>` (template V5), the literal identities `sl = S`, `cc - dd = C`
  (pre-checked for all 36 pairs), and `mul_le_mul_of_nonneg_left` with `wt >= 0`.
-/

namespace N11Formalization.Leaf4348Dispatch

open Finset
open N11Formalization.FlashCosine (Lq LQ Dq DQ Lc Dc tval zval zval_eq tval_sub)
open N11Formalization.FlashCosineLeaf284Bridge (tval_eq_tlift)

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 400000000

/-- The leaf's per-pair safe minorants (the payload's only remaining hypothesis). -/
theorem hsafe_all (y : Fin 9 → ℝ)
    (hcell : N11Formalization.FlashLeafSplit.Cell
      (fun i j => (N11Formalization.Leaf4348LP.dbm i j : ℝ))
      (N11Formalization.FlashLeafSplit.tlift y)) :
    ∀ k : Fin 36,
      (N11Formalization.Leaf4348Bridge.wt k : ℝ) *
        ((N11Formalization.Leaf4348Bridge.sl k : ℝ) *
            zval y (N11Formalization.FlashCosineLeaf284Bridge.iOf k)
              (N11Formalization.FlashCosineLeaf284Bridge.jOf k)
          + ((N11Formalization.Leaf4348Bridge.cc k : ℝ)
             - (N11Formalization.Leaf4348Assembly.dd k : ℝ)))
      ≤ (N11Formalization.Leaf4348Bridge.wt k : ℝ) *
        (1 - Real.cos (zval y (N11Formalization.FlashCosineLeaf284Bridge.iOf k)
          (N11Formalization.FlashCosineLeaf284Bridge.jOf k))) := by
  intro k
  fin_cases k
  · -- pair (0, 1) [inc]
    have hlo : ((((5 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 1) (Fin.castSucc 0)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((11 : ℚ) / 512) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 0) (Fin.castSucc 1)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell01 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨0, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨0, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨0, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S01 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S01]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨0, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨0, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C01 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨0, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨0, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C01 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C01]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨0, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨0, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C01 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (0, 2) [inc]
    have hlo : ((((5 : ℚ) / 256) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 2) (Fin.castSucc 0)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((3 : ℚ) / 128) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 0) (Fin.castSucc 2)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell02 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨1, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨1, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨1, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S02 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S02]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨1, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨1, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C02 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨1, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨1, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C02 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C02]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨1, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨1, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C02 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (0, 3) [dec]
    have hlo : ((((21 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 3) (Fin.castSucc 0)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((11 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 0) (Fin.castSucc 3)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell03 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨2, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨2, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨2, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S03 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S03]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨2, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨2, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C03 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨2, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨2, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C03 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C03]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨2, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨2, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C03 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (0, 4) [dec]
    have hlo : ((((173 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 4) (Fin.castSucc 0)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((87 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 0) (Fin.castSucc 4)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell04 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨3, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨3, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨3, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S04 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S04]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨3, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨3, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C04 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨3, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨3, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C04 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C04]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨3, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨3, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C04 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (0, 5) [dec]
    have hlo : ((((121 : ℚ) / 256) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 5) (Fin.castSucc 0)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((61 : ℚ) / 128) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 0) (Fin.castSucc 5)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell05 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨4, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨4, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨4, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S05 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S05]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨4, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨4, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C05 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨4, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨4, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C05 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C05]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨4, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨4, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C05 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (0, 6) [dec]
    have hlo : ((((133 : ℚ) / 256) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 6) (Fin.castSucc 0)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((67 : ℚ) / 128) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 0) (Fin.castSucc 6)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell06 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨5, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨5, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨5, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S06 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S06]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨5, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨5, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C06 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨5, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨5, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C06 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C06]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨5, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨5, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C06 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (0, 7) [inc]
    have hlo : ((((291 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 7) (Fin.castSucc 0)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((73 : ℚ) / 128) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 0) (Fin.castSucc 7)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell07 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨6, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨6, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨6, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S07 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S07]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨6, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨6, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C07 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨6, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨6, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C07 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C07]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨6, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨6, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C07 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (0, 8) [inc]
    have hlo : ((((359 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 8) (Fin.castSucc 0)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((45 : ℚ) / 64) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 0) (Fin.castSucc 8)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell08 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨7, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨7, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨7, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S08 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S08]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨7, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨7, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C08 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨7, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨7, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C08 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C08]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨7, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨7, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C08 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (1, 2) [inc]
    have hlo : ((((1 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 2) (Fin.castSucc 1)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((3 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 1) (Fin.castSucc 2)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell12 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨8, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨8, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨8, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S12 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S12]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨8, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨8, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C12 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨8, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨8, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C12 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C12]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨8, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨8, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C12 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (1, 3) [inc]
    have hlo : ((((5 : ℚ) / 256) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 3) (Fin.castSucc 1)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((1 : ℚ) / 32) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 1) (Fin.castSucc 3)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell13 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨9, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨9, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨9, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S13 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S13]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨9, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨9, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C13 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨9, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨9, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C13 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C13]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨9, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨9, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C13 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (1, 4) [dec]
    have hlo : ((((163 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 4) (Fin.castSucc 1)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((21 : ℚ) / 64) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 1) (Fin.castSucc 4)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell14 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨10, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨10, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨10, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S14 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S14]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨10, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨10, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C14 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨10, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨10, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C14 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C14]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨10, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨10, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C14 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (1, 5) [dec]
    have hlo : ((((231 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 5) (Fin.castSucc 1)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((119 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 1) (Fin.castSucc 5)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell15 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨11, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨11, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨11, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S15 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S15]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨11, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨11, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C15 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨11, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨11, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C15 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C15]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨11, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨11, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C15 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (1, 6) [dec]
    have hlo : ((((257 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 6) (Fin.castSucc 1)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((131 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 1) (Fin.castSucc 6)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell16 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨12, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨12, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨12, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S16 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S16]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨12, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨12, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C16 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨12, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨12, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C16 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C16]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨12, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨12, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C16 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (1, 7) [dec]
    have hlo : ((((35 : ℚ) / 64) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 7) (Fin.castSucc 1)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((143 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 1) (Fin.castSucc 7)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell17 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨13, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨13, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨13, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S17 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S17]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨13, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨13, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C17 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨13, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨13, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C17 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C17]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨13, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨13, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C17 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (1, 8) [inc]
    have hlo : ((((349 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 8) (Fin.castSucc 1)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((177 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 1) (Fin.castSucc 8)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell18 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨14, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨14, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨14, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S18 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S18]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨14, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨14, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C18 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨14, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨14, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C18 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C18]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨14, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨14, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C18 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (2, 3) [inc]
    have hlo : ((((9 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 3) (Fin.castSucc 2)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((11 : ℚ) / 512) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 2) (Fin.castSucc 3)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell23 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨15, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨15, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨15, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S23 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S23]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨15, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨15, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C23 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨15, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨15, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C23 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C23]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨15, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨15, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C23 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (2, 4) [inc]
    have hlo : ((((81 : ℚ) / 256) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 4) (Fin.castSucc 2)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((41 : ℚ) / 128) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 2) (Fin.castSucc 4)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell24 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨16, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨16, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨16, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S24 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S24]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨16, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨16, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C24 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨16, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨16, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C24 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C24]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨16, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨16, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C24 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (2, 5) [dec]
    have hlo : ((((115 : ℚ) / 256) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 5) (Fin.castSucc 2)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((117 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 2) (Fin.castSucc 5)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell25 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨17, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨17, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨17, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S25 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S25]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨17, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨17, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C25 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨17, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨17, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C25 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C25]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨17, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨17, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C25 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (2, 6) [dec]
    have hlo : ((((127 : ℚ) / 256) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 6) (Fin.castSucc 2)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((1 : ℚ) / 2) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 2) (Fin.castSucc 6)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell26 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨18, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨18, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨18, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S26 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S26]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨18, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨18, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C26 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨18, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨18, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C26 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C26]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨18, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨18, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C26 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (2, 7) [dec]
    have hlo : ((((279 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 7) (Fin.castSucc 2)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((141 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 2) (Fin.castSucc 7)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell27 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨19, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨19, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨19, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S27 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S27]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨19, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨19, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C27 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨19, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨19, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C27 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C27]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨19, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨19, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C27 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (2, 8) [dec]
    have hlo : ((((87 : ℚ) / 128) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 8) (Fin.castSucc 2)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((175 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 2) (Fin.castSucc 8)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell28 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨20, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨20, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨20, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S28 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S28]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨20, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨20, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C28 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨20, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨20, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C28 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C28]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨20, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨20, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C28 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (3, 4) [inc]
    have hlo : ((((19 : ℚ) / 64) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 4) (Fin.castSucc 3)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((153 : ℚ) / 512) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 3) (Fin.castSucc 4)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell34 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨21, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨21, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨21, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S34 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S34]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨21, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨21, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C34 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨21, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨21, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C34 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C34]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨21, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨21, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C34 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (3, 5) [inc]
    have hlo : ((((55 : ℚ) / 128) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 5) (Fin.castSucc 3)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((223 : ℚ) / 512) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 3) (Fin.castSucc 5)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell35 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨22, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨22, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨22, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S35 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S35]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨22, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨22, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C35 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨22, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨22, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C35 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C35]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨22, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨22, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C35 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (3, 6) [dec]
    have hlo : ((((245 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 6) (Fin.castSucc 3)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((247 : ℚ) / 512) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 3) (Fin.castSucc 6)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell36 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨23, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨23, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨23, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S36 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S36]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨23, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨23, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C36 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨23, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨23, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C36 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C36]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨23, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨23, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C36 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (3, 7) [dec]
    have hlo : ((((135 : ℚ) / 256) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 7) (Fin.castSucc 3)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((271 : ℚ) / 512) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 3) (Fin.castSucc 7)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell37 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨24, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨24, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨24, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S37 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S37]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨24, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨24, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C37 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨24, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨24, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C37 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C37]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨24, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨24, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C37 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (3, 8) [dec]
    have hlo : ((((169 : ℚ) / 256) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 8) (Fin.castSucc 3)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((339 : ℚ) / 512) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 3) (Fin.castSucc 8)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell38 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨25, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨25, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨25, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S38 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S38]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨25, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨25, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C38 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨25, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨25, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C38 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C38]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨25, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨25, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C38 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (4, 5) [inc]
    have hlo : ((((17 : ℚ) / 128) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 5) (Fin.castSucc 4)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((35 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 4) (Fin.castSucc 5)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell45 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨26, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨26, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨26, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S45 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S45]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨26, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨26, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C45 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨26, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨26, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C45 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C45]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨26, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨26, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C45 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (4, 6) [inc]
    have hlo : ((((23 : ℚ) / 128) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 6) (Fin.castSucc 4)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((47 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 4) (Fin.castSucc 6)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell46 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨27, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨27, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨27, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S46 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S46]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨27, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨27, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C46 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨27, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨27, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C46 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C46]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨27, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨27, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C46 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (4, 7) [dec]
    have hlo : ((((117 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 7) (Fin.castSucc 4)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((59 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 4) (Fin.castSucc 7)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell47 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨28, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨28, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨28, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S47 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S47]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨28, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨28, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C47 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨28, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨28, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C47 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C47]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨28, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨28, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C47 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (4, 8) [dec]
    have hlo : ((((185 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 8) (Fin.castSucc 4)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((93 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 4) (Fin.castSucc 8)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell48 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨29, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨29, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨29, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S48 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S48]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨29, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨29, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C48 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨29, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨29, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C48 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C48]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨29, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨29, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C48 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (5, 6) [inc]
    have hlo : ((((11 : ℚ) / 256) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 6) (Fin.castSucc 5)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((13 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 5) (Fin.castSucc 6)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell56 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨30, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨30, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨30, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S56 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S56]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨30, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨30, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C56 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨30, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨30, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C56 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C56]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨30, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨30, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C56 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (5, 7) [inc]
    have hlo : ((((47 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 7) (Fin.castSucc 5)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((25 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 5) (Fin.castSucc 7)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell57 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨31, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨31, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨31, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S57 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S57]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨31, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨31, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C57 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨31, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨31, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C57 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C57]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨31, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨31, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C57 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (5, 8) [dec]
    have hlo : ((((29 : ℚ) / 128) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 8) (Fin.castSucc 5)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((59 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 5) (Fin.castSucc 8)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell58 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨32, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨32, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨32, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S58 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S58]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨32, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨32, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C58 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨32, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨32, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C58 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C58]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨32, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨32, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C58 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (6, 7) [inc]
    have hlo : ((((23 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 7) (Fin.castSucc 6)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((13 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 6) (Fin.castSucc 7)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell67 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨33, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨33, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨33, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S67 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S67]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨33, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨33, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C67 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨33, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨33, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C67 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C67]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨33, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨33, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C67 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (6, 8) [inc]
    have hlo : ((((23 : ℚ) / 128) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 8) (Fin.castSucc 6)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((47 : ℚ) / 256) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 6) (Fin.castSucc 8)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell68 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨34, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨34, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨34, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S68 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S68]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨34, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨34, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C68 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨34, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨34, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C68 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C68]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨34, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨34, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C68 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain
  · -- pair (7, 8) [inc]
    have hlo : ((((67 : ℚ) / 512) : ℚ) = -N11Formalization.Leaf4348LP.dbm (Fin.castSucc 8) (Fin.castSucc 7)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hhi : ((((69 : ℚ) / 512) : ℚ) = N11Formalization.Leaf4348LP.dbm (Fin.castSucc 7) (Fin.castSucc 8)) := by
      norm_num [N11Formalization.Leaf4348LP.dbm]
    have hcell' := N11Formalization.Leaf4348Pairs.cell78 y hlo hhi hcell
    have hwt : (0 : ℝ) ≤ (N11Formalization.Leaf4348Bridge.wt ⟨35, by norm_num⟩ : ℝ) := N11Formalization.Leaf4348Assembly.wt_nonneg ⟨35, by norm_num⟩
    have hsln : (N11Formalization.Leaf4348Bridge.sl ⟨35, by norm_num⟩ : ℝ) = (N11Formalization.Leaf4348Pairs.S78 : ℝ) := by
      norm_num [N11Formalization.Leaf4348Bridge.sl, N11Formalization.Leaf4348Pairs.S78]
    have hccn : ((N11Formalization.Leaf4348Bridge.cc ⟨35, by norm_num⟩ : ℝ) - (N11Formalization.Leaf4348Assembly.dd ⟨35, by norm_num⟩ : ℝ)) = (N11Formalization.Leaf4348Pairs.C78 : ℝ) := by
      have hq : ((N11Formalization.Leaf4348Bridge.cc ⟨35, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨35, by norm_num⟩ : ℚ)) = N11Formalization.Leaf4348Pairs.C78 := by
        norm_num [N11Formalization.Leaf4348Bridge.cc, N11Formalization.Leaf4348Assembly.dd, N11Formalization.Leaf4348Pairs.C78]
      have hR : (((N11Formalization.Leaf4348Bridge.cc ⟨35, by norm_num⟩ : ℚ) - (N11Formalization.Leaf4348Assembly.dd ⟨35, by norm_num⟩ : ℚ) : ℚ) : ℝ)
          = (((N11Formalization.Leaf4348Pairs.C78 : ℚ)) : ℝ) := by
        exact_mod_cast hq
      simpa only [Rat.cast_sub] using hR
    have hmain := mul_le_mul_of_nonneg_left hcell' hwt
    rw [hsln, hccn]
    exact hmain

/-- **The unconditional payload**: whole DBM cell => `T^2 < V2 (circleMap o N11Formalization.FlashCosine.theta)`.

`hsafe_all` has exactly the type of `Leaf4348Oracle.leaf4348_oracle_gt`'s last hypothesis, so the
payload now has no remaining hypothesis. -/
theorem leaf4348_oracle_gt (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : N11Formalization.FlashLeafSplit.Cell
      (fun i j => (N11Formalization.Leaf4348LP.dbm i j : ℝ))
      (N11Formalization.FlashLeafSplit.tlift y)) :
    (N11Formalization.Leaf4348LP.T : ℝ) ^ 2
      < ResumeNetwork.V2 (fun j => N11Formalization.circleMap (N11Formalization.FlashCosine.theta y j)) :=
  N11Formalization.Leaf4348Oracle.leaf4348_oracle_gt y hy0 hy1 hcell (hsafe_all y hcell)

#print axioms N11Formalization.Leaf4348Dispatch.hsafe_all
#print axioms N11Formalization.Leaf4348Dispatch.leaf4348_oracle_gt

end N11Formalization.Leaf4348Dispatch
