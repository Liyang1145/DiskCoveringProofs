/-
  **FlashCosineLP — stage 3 of the leaf-318 energy lower bound (standalone; imports the frozen
  green module `FlashCosineLeaf318`).**

  Fixes vs `FlashCosineLP.draft.lean.txt` (gate `scratch/lp-gate7.log`: 4 errors, 1 warning):
  (a) `lamB_eq`: full `simp` + the trimmed default-set expansion (the probe-green recipe), not
      `simp only`;
  (b) `redcost`: `fin_cases q` branch bullets moved to the tactic-block column (the emitter had
      indented the focus bullets one level too deep, which was the parse error at gate line 50),
      plus a per-branch `show` restating the goal at the branch literal, because `fin_cases`
      leaves the goal in a beta-redex form `((fun i => i) ⟨k, _⟩)` whose atoms linarith cannot
      match against the `(k : Fin 9)`-shaped `have`s;
  (c) `stage3` `hnum`: full `simp` (evaluates the `if` conditions) before `norm_num`;
  (d) every imported data name is fully qualified `N11Formalization.FlashCosine.*` (root-namespace
      shadowing, HANDOFF 6h).
  Landing state: the identical body gated green from `evidence/flash-cosine/FlashCosineLP.WIP.lean.txt`
  (`scratch/lp-gate9.log`, exit 0, 0 error, 0 warning).
  Discipline: no `sorry`, no custom `axiom`, no `native_decide`.
-/
import N11Formalization.FlashCosineLeaf318

namespace N11Formalization.FlashCosineLP

open Finset
open N11Formalization.FlashCosine
open N11Formalization.ResumeGlobal.C911Weights

def rowb : Fin 6 → ℚ
  | 0 => ((-1 : ℚ) / 4)
  | 1 => (-1 : ℚ)
  | 2 => ((1 : ℚ) / 4)
  | 3 => ((-1 : ℚ) / 4)
  | 4 => ((1 : ℚ) / 4)
  | 5 => ((1 : ℚ) / 4)

def zhatLo : Fin 9 → ℚ
  | 0 => ((41865381882303894633103108657 : ℚ) / 1000000000000000000000000000000)
  | 1 => ((41865381882303894633103108657 : ℚ) / 1000000000000000000000000000000)
  | 2 => ((41865381882303894633103108657 : ℚ) / 1000000000000000000000000000000)
  | 3 => ((372233300421273176636861053 : ℚ) / 125000000000000000000000000000)
  | 4 => ((1426534005362666936978911399 : ℚ) / 500000000000000000000000000000)
  | 5 => ((31279487441961609157225498867 : ℚ) / 1000000000000000000000000000000)
  | 6 => ((31279487441961609157225498867 : ℚ) / 1000000000000000000000000000000)
  | 7 => ((657779400076542951048666053 : ℚ) / 500000000000000000000000000000)
  | 8 => (0 : ℚ)

def rowS (q : Fin 9) : ℚ :=
  ∑ r : Fin 6, N11Formalization.FlashCosine.lamVal r * N11Formalization.FlashCosine.rowA r q

theorem zhatLo_le (q : Fin 9) : (zhatLo q : ℚ) ≤ N11Formalization.FlashCosine.zhat q := by
  fin_cases q <;>
    (simp [N11Formalization.FlashCosine.zhat, N11Formalization.FlashCosine.wlo,
      N11Formalization.FlashCosine.sq, N11Formalization.FlashCosine.iOf,
      N11Formalization.FlashCosine.jOf, Fin.sum_univ_succ];
      norm_num [zhatLo])

theorem rowS_cast (q : Fin 9) :
    ((rowS q : ℚ) : ℝ) =
      ∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) *
        (N11Formalization.FlashCosine.rowA r q : ℝ) := by
  rw [rowS]; push_cast; rfl

theorem lamB_eq :
    (∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) * (rowb r : ℝ))
      = (((-55717737991 : ℚ) / 4000000000000) : ℝ) := by
  simp [N11Formalization.FlashCosine.lamVal, rowb, Fin.sum_univ_succ]
  norm_num

set_option maxHeartbeats 1000000 in
theorem redcost (Dc' : ℝ)
    (hD : (N11Formalization.FlashCosine.Dq : ℝ) ≤ Dc' ∧ Dc' ≤ (N11Formalization.FlashCosine.DQ : ℝ)) :
    ∀ q : Fin 9,
      ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        Dc' * ((N11Formalization.FlashCosine.zhat q : ℚ) : ℝ) + ((rowS q : ℚ) : ℝ) := by
  intro q
  fin_cases q
  · -- q = 0
    show ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        Dc' * ((N11Formalization.FlashCosine.zhat (0 : Fin 9) : ℚ) : ℝ) +
          ((rowS (0 : Fin 9) : ℚ) : ℝ)
    have hz : (zhatLo (0 : Fin 9) : ℚ) ≤ N11Formalization.FlashCosine.zhat (0 : Fin 9) :=
      zhatLo_le (0 : Fin 9)
    have hzv : ((zhatLo (0 : Fin 9) : ℚ) : ℝ) ≤
        ((N11Formalization.FlashCosine.zhat (0 : Fin 9) : ℚ) : ℝ) :=
      by exact_mod_cast hz
    have hS : ((rowS (0 : Fin 9) : ℚ) : ℝ)
        = ∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) *
            (N11Formalization.FlashCosine.rowA r (0 : Fin 9) : ℝ) :=
      rowS_cast (0 : Fin 9)
    have hnum : ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (0 : Fin 9) : ℚ) : ℝ) +
          ((rowS (0 : Fin 9) : ℚ) : ℝ) := by
      rw [hS]
      simp [zhatLo, N11Formalization.FlashCosine.lamVal, N11Formalization.FlashCosine.rowA,
        N11Formalization.FlashCosine.lamIJ, N11Formalization.FlashCosine.lamSgn,
        N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.Lq,
        N11Formalization.RatInterval.piHi, Fin.sum_univ_succ]
      norm_num
    have hpos : (0 : ℝ) ≤ (zhatLo (0 : Fin 9) : ℚ) := by norm_num [zhatLo]
    have hstep : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (0 : Fin 9) : ℚ) : ℝ)
        ≤ Dc' * ((N11Formalization.FlashCosine.zhat (0 : Fin 9) : ℚ) : ℝ) := by
      have hDq0 : (0 : ℝ) ≤ (N11Formalization.FlashCosine.Dq : ℝ) :=
        N11Formalization.FlashCosine.Dq_pos.le
      have hDc0 : (0 : ℝ) ≤ Dc' := le_trans hDq0 hD.1
      have hm1 : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (0 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((zhatLo (0 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hD.1 hpos
      have hm2 : Dc' * ((zhatLo (0 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((N11Formalization.FlashCosine.zhat (0 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hzv hDc0
      linarith [hm1, hm2]
    linarith [hnum, hstep]
  · -- q = 1
    show ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        Dc' * ((N11Formalization.FlashCosine.zhat (1 : Fin 9) : ℚ) : ℝ) +
          ((rowS (1 : Fin 9) : ℚ) : ℝ)
    have hz : (zhatLo (1 : Fin 9) : ℚ) ≤ N11Formalization.FlashCosine.zhat (1 : Fin 9) :=
      zhatLo_le (1 : Fin 9)
    have hzv : ((zhatLo (1 : Fin 9) : ℚ) : ℝ) ≤
        ((N11Formalization.FlashCosine.zhat (1 : Fin 9) : ℚ) : ℝ) :=
      by exact_mod_cast hz
    have hS : ((rowS (1 : Fin 9) : ℚ) : ℝ)
        = ∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) *
            (N11Formalization.FlashCosine.rowA r (1 : Fin 9) : ℝ) :=
      rowS_cast (1 : Fin 9)
    have hnum : ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (1 : Fin 9) : ℚ) : ℝ) +
          ((rowS (1 : Fin 9) : ℚ) : ℝ) := by
      rw [hS]
      simp [zhatLo, N11Formalization.FlashCosine.lamVal, N11Formalization.FlashCosine.rowA,
        N11Formalization.FlashCosine.lamIJ, N11Formalization.FlashCosine.lamSgn,
        N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.Lq,
        N11Formalization.RatInterval.piHi, Fin.sum_univ_succ]
      norm_num
    have hpos : (0 : ℝ) ≤ (zhatLo (1 : Fin 9) : ℚ) := by norm_num [zhatLo]
    have hstep : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (1 : Fin 9) : ℚ) : ℝ)
        ≤ Dc' * ((N11Formalization.FlashCosine.zhat (1 : Fin 9) : ℚ) : ℝ) := by
      have hDq0 : (0 : ℝ) ≤ (N11Formalization.FlashCosine.Dq : ℝ) :=
        N11Formalization.FlashCosine.Dq_pos.le
      have hDc0 : (0 : ℝ) ≤ Dc' := le_trans hDq0 hD.1
      have hm1 : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (1 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((zhatLo (1 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hD.1 hpos
      have hm2 : Dc' * ((zhatLo (1 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((N11Formalization.FlashCosine.zhat (1 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hzv hDc0
      linarith [hm1, hm2]
    linarith [hnum, hstep]
  · -- q = 2
    show ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        Dc' * ((N11Formalization.FlashCosine.zhat (2 : Fin 9) : ℚ) : ℝ) +
          ((rowS (2 : Fin 9) : ℚ) : ℝ)
    have hz : (zhatLo (2 : Fin 9) : ℚ) ≤ N11Formalization.FlashCosine.zhat (2 : Fin 9) :=
      zhatLo_le (2 : Fin 9)
    have hzv : ((zhatLo (2 : Fin 9) : ℚ) : ℝ) ≤
        ((N11Formalization.FlashCosine.zhat (2 : Fin 9) : ℚ) : ℝ) :=
      by exact_mod_cast hz
    have hS : ((rowS (2 : Fin 9) : ℚ) : ℝ)
        = ∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) *
            (N11Formalization.FlashCosine.rowA r (2 : Fin 9) : ℝ) :=
      rowS_cast (2 : Fin 9)
    have hnum : ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (2 : Fin 9) : ℚ) : ℝ) +
          ((rowS (2 : Fin 9) : ℚ) : ℝ) := by
      rw [hS]
      simp [zhatLo, N11Formalization.FlashCosine.lamVal, N11Formalization.FlashCosine.rowA,
        N11Formalization.FlashCosine.lamIJ, N11Formalization.FlashCosine.lamSgn,
        N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.Lq,
        N11Formalization.RatInterval.piHi, Fin.sum_univ_succ]
      norm_num
    have hpos : (0 : ℝ) ≤ (zhatLo (2 : Fin 9) : ℚ) := by norm_num [zhatLo]
    have hstep : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (2 : Fin 9) : ℚ) : ℝ)
        ≤ Dc' * ((N11Formalization.FlashCosine.zhat (2 : Fin 9) : ℚ) : ℝ) := by
      have hDq0 : (0 : ℝ) ≤ (N11Formalization.FlashCosine.Dq : ℝ) :=
        N11Formalization.FlashCosine.Dq_pos.le
      have hDc0 : (0 : ℝ) ≤ Dc' := le_trans hDq0 hD.1
      have hm1 : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (2 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((zhatLo (2 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hD.1 hpos
      have hm2 : Dc' * ((zhatLo (2 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((N11Formalization.FlashCosine.zhat (2 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hzv hDc0
      linarith [hm1, hm2]
    linarith [hnum, hstep]
  · -- q = 3
    show ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        Dc' * ((N11Formalization.FlashCosine.zhat (3 : Fin 9) : ℚ) : ℝ) +
          ((rowS (3 : Fin 9) : ℚ) : ℝ)
    have hz : (zhatLo (3 : Fin 9) : ℚ) ≤ N11Formalization.FlashCosine.zhat (3 : Fin 9) :=
      zhatLo_le (3 : Fin 9)
    have hzv : ((zhatLo (3 : Fin 9) : ℚ) : ℝ) ≤
        ((N11Formalization.FlashCosine.zhat (3 : Fin 9) : ℚ) : ℝ) :=
      by exact_mod_cast hz
    have hS : ((rowS (3 : Fin 9) : ℚ) : ℝ)
        = ∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) *
            (N11Formalization.FlashCosine.rowA r (3 : Fin 9) : ℝ) :=
      rowS_cast (3 : Fin 9)
    have hnum : ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (3 : Fin 9) : ℚ) : ℝ) +
          ((rowS (3 : Fin 9) : ℚ) : ℝ) := by
      rw [hS]
      simp [zhatLo, N11Formalization.FlashCosine.lamVal, N11Formalization.FlashCosine.rowA,
        N11Formalization.FlashCosine.lamIJ, N11Formalization.FlashCosine.lamSgn,
        N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.Lq,
        N11Formalization.RatInterval.piHi, Fin.sum_univ_succ]
      norm_num
    have hpos : (0 : ℝ) ≤ (zhatLo (3 : Fin 9) : ℚ) := by norm_num [zhatLo]
    have hstep : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (3 : Fin 9) : ℚ) : ℝ)
        ≤ Dc' * ((N11Formalization.FlashCosine.zhat (3 : Fin 9) : ℚ) : ℝ) := by
      have hDq0 : (0 : ℝ) ≤ (N11Formalization.FlashCosine.Dq : ℝ) :=
        N11Formalization.FlashCosine.Dq_pos.le
      have hDc0 : (0 : ℝ) ≤ Dc' := le_trans hDq0 hD.1
      have hm1 : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (3 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((zhatLo (3 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hD.1 hpos
      have hm2 : Dc' * ((zhatLo (3 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((N11Formalization.FlashCosine.zhat (3 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hzv hDc0
      linarith [hm1, hm2]
    linarith [hnum, hstep]
  · -- q = 4
    show ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        Dc' * ((N11Formalization.FlashCosine.zhat (4 : Fin 9) : ℚ) : ℝ) +
          ((rowS (4 : Fin 9) : ℚ) : ℝ)
    have hz : (zhatLo (4 : Fin 9) : ℚ) ≤ N11Formalization.FlashCosine.zhat (4 : Fin 9) :=
      zhatLo_le (4 : Fin 9)
    have hzv : ((zhatLo (4 : Fin 9) : ℚ) : ℝ) ≤
        ((N11Formalization.FlashCosine.zhat (4 : Fin 9) : ℚ) : ℝ) :=
      by exact_mod_cast hz
    have hS : ((rowS (4 : Fin 9) : ℚ) : ℝ)
        = ∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) *
            (N11Formalization.FlashCosine.rowA r (4 : Fin 9) : ℝ) :=
      rowS_cast (4 : Fin 9)
    have hnum : ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (4 : Fin 9) : ℚ) : ℝ) +
          ((rowS (4 : Fin 9) : ℚ) : ℝ) := by
      rw [hS]
      simp [zhatLo, N11Formalization.FlashCosine.lamVal, N11Formalization.FlashCosine.rowA,
        N11Formalization.FlashCosine.lamIJ, N11Formalization.FlashCosine.lamSgn,
        N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.Lq,
        N11Formalization.RatInterval.piHi, Fin.sum_univ_succ]
      norm_num
    have hpos : (0 : ℝ) ≤ (zhatLo (4 : Fin 9) : ℚ) := by norm_num [zhatLo]
    have hstep : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (4 : Fin 9) : ℚ) : ℝ)
        ≤ Dc' * ((N11Formalization.FlashCosine.zhat (4 : Fin 9) : ℚ) : ℝ) := by
      have hDq0 : (0 : ℝ) ≤ (N11Formalization.FlashCosine.Dq : ℝ) :=
        N11Formalization.FlashCosine.Dq_pos.le
      have hDc0 : (0 : ℝ) ≤ Dc' := le_trans hDq0 hD.1
      have hm1 : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (4 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((zhatLo (4 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hD.1 hpos
      have hm2 : Dc' * ((zhatLo (4 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((N11Formalization.FlashCosine.zhat (4 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hzv hDc0
      linarith [hm1, hm2]
    linarith [hnum, hstep]
  · -- q = 5
    show ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        Dc' * ((N11Formalization.FlashCosine.zhat (5 : Fin 9) : ℚ) : ℝ) +
          ((rowS (5 : Fin 9) : ℚ) : ℝ)
    have hz : (zhatLo (5 : Fin 9) : ℚ) ≤ N11Formalization.FlashCosine.zhat (5 : Fin 9) :=
      zhatLo_le (5 : Fin 9)
    have hzv : ((zhatLo (5 : Fin 9) : ℚ) : ℝ) ≤
        ((N11Formalization.FlashCosine.zhat (5 : Fin 9) : ℚ) : ℝ) :=
      by exact_mod_cast hz
    have hS : ((rowS (5 : Fin 9) : ℚ) : ℝ)
        = ∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) *
            (N11Formalization.FlashCosine.rowA r (5 : Fin 9) : ℝ) :=
      rowS_cast (5 : Fin 9)
    have hnum : ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (5 : Fin 9) : ℚ) : ℝ) +
          ((rowS (5 : Fin 9) : ℚ) : ℝ) := by
      rw [hS]
      simp [zhatLo, N11Formalization.FlashCosine.lamVal, N11Formalization.FlashCosine.rowA,
        N11Formalization.FlashCosine.lamIJ, N11Formalization.FlashCosine.lamSgn,
        N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.Lq,
        N11Formalization.RatInterval.piHi, Fin.sum_univ_succ]
      norm_num
    have hpos : (0 : ℝ) ≤ (zhatLo (5 : Fin 9) : ℚ) := by norm_num [zhatLo]
    have hstep : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (5 : Fin 9) : ℚ) : ℝ)
        ≤ Dc' * ((N11Formalization.FlashCosine.zhat (5 : Fin 9) : ℚ) : ℝ) := by
      have hDq0 : (0 : ℝ) ≤ (N11Formalization.FlashCosine.Dq : ℝ) :=
        N11Formalization.FlashCosine.Dq_pos.le
      have hDc0 : (0 : ℝ) ≤ Dc' := le_trans hDq0 hD.1
      have hm1 : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (5 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((zhatLo (5 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hD.1 hpos
      have hm2 : Dc' * ((zhatLo (5 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((N11Formalization.FlashCosine.zhat (5 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hzv hDc0
      linarith [hm1, hm2]
    linarith [hnum, hstep]
  · -- q = 6
    show ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        Dc' * ((N11Formalization.FlashCosine.zhat (6 : Fin 9) : ℚ) : ℝ) +
          ((rowS (6 : Fin 9) : ℚ) : ℝ)
    have hz : (zhatLo (6 : Fin 9) : ℚ) ≤ N11Formalization.FlashCosine.zhat (6 : Fin 9) :=
      zhatLo_le (6 : Fin 9)
    have hzv : ((zhatLo (6 : Fin 9) : ℚ) : ℝ) ≤
        ((N11Formalization.FlashCosine.zhat (6 : Fin 9) : ℚ) : ℝ) :=
      by exact_mod_cast hz
    have hS : ((rowS (6 : Fin 9) : ℚ) : ℝ)
        = ∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) *
            (N11Formalization.FlashCosine.rowA r (6 : Fin 9) : ℝ) :=
      rowS_cast (6 : Fin 9)
    have hnum : ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (6 : Fin 9) : ℚ) : ℝ) +
          ((rowS (6 : Fin 9) : ℚ) : ℝ) := by
      rw [hS]
      simp [zhatLo, N11Formalization.FlashCosine.lamVal, N11Formalization.FlashCosine.rowA,
        N11Formalization.FlashCosine.lamIJ, N11Formalization.FlashCosine.lamSgn,
        N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.Lq,
        N11Formalization.RatInterval.piHi, Fin.sum_univ_succ]
      norm_num
    have hpos : (0 : ℝ) ≤ (zhatLo (6 : Fin 9) : ℚ) := by norm_num [zhatLo]
    have hstep : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (6 : Fin 9) : ℚ) : ℝ)
        ≤ Dc' * ((N11Formalization.FlashCosine.zhat (6 : Fin 9) : ℚ) : ℝ) := by
      have hDq0 : (0 : ℝ) ≤ (N11Formalization.FlashCosine.Dq : ℝ) :=
        N11Formalization.FlashCosine.Dq_pos.le
      have hDc0 : (0 : ℝ) ≤ Dc' := le_trans hDq0 hD.1
      have hm1 : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (6 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((zhatLo (6 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hD.1 hpos
      have hm2 : Dc' * ((zhatLo (6 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((N11Formalization.FlashCosine.zhat (6 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hzv hDc0
      linarith [hm1, hm2]
    linarith [hnum, hstep]
  · -- q = 7
    show ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        Dc' * ((N11Formalization.FlashCosine.zhat (7 : Fin 9) : ℚ) : ℝ) +
          ((rowS (7 : Fin 9) : ℚ) : ℝ)
    have hz : (zhatLo (7 : Fin 9) : ℚ) ≤ N11Formalization.FlashCosine.zhat (7 : Fin 9) :=
      zhatLo_le (7 : Fin 9)
    have hzv : ((zhatLo (7 : Fin 9) : ℚ) : ℝ) ≤
        ((N11Formalization.FlashCosine.zhat (7 : Fin 9) : ℚ) : ℝ) :=
      by exact_mod_cast hz
    have hS : ((rowS (7 : Fin 9) : ℚ) : ℝ)
        = ∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) *
            (N11Formalization.FlashCosine.rowA r (7 : Fin 9) : ℝ) :=
      rowS_cast (7 : Fin 9)
    have hnum : ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (7 : Fin 9) : ℚ) : ℝ) +
          ((rowS (7 : Fin 9) : ℚ) : ℝ) := by
      rw [hS]
      simp [zhatLo, N11Formalization.FlashCosine.lamVal, N11Formalization.FlashCosine.rowA,
        N11Formalization.FlashCosine.lamIJ, N11Formalization.FlashCosine.lamSgn,
        N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.Lq,
        N11Formalization.RatInterval.piHi, Fin.sum_univ_succ]
      norm_num
    have hpos : (0 : ℝ) ≤ (zhatLo (7 : Fin 9) : ℚ) := by norm_num [zhatLo]
    have hstep : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (7 : Fin 9) : ℚ) : ℝ)
        ≤ Dc' * ((N11Formalization.FlashCosine.zhat (7 : Fin 9) : ℚ) : ℝ) := by
      have hDq0 : (0 : ℝ) ≤ (N11Formalization.FlashCosine.Dq : ℝ) :=
        N11Formalization.FlashCosine.Dq_pos.le
      have hDc0 : (0 : ℝ) ≤ Dc' := le_trans hDq0 hD.1
      have hm1 : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (7 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((zhatLo (7 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hD.1 hpos
      have hm2 : Dc' * ((zhatLo (7 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((N11Formalization.FlashCosine.zhat (7 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hzv hDc0
      linarith [hm1, hm2]
    linarith [hnum, hstep]
  · -- q = 8
    show ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        Dc' * ((N11Formalization.FlashCosine.zhat (8 : Fin 9) : ℚ) : ℝ) +
          ((rowS (8 : Fin 9) : ℚ) : ℝ)
    have hz : (zhatLo (8 : Fin 9) : ℚ) ≤ N11Formalization.FlashCosine.zhat (8 : Fin 9) :=
      zhatLo_le (8 : Fin 9)
    have hzv : ((zhatLo (8 : Fin 9) : ℚ) : ℝ) ≤
        ((N11Formalization.FlashCosine.zhat (8 : Fin 9) : ℚ) : ℝ) :=
      by exact_mod_cast hz
    have hS : ((rowS (8 : Fin 9) : ℚ) : ℝ)
        = ∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) *
            (N11Formalization.FlashCosine.rowA r (8 : Fin 9) : ℝ) :=
      rowS_cast (8 : Fin 9)
    have hnum : ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) ≤
        (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (8 : Fin 9) : ℚ) : ℝ) +
          ((rowS (8 : Fin 9) : ℚ) : ℝ) := by
      rw [hS]
      simp [zhatLo, N11Formalization.FlashCosine.lamVal, N11Formalization.FlashCosine.rowA,
        N11Formalization.FlashCosine.lamIJ, N11Formalization.FlashCosine.lamSgn,
        N11Formalization.FlashCosine.Dq, N11Formalization.FlashCosine.Lq,
        N11Formalization.RatInterval.piHi, Fin.sum_univ_succ]
      norm_num
    have hpos : (0 : ℝ) ≤ (zhatLo (8 : Fin 9) : ℚ) := by norm_num [zhatLo]
    have hstep : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (8 : Fin 9) : ℚ) : ℝ)
        ≤ Dc' * ((N11Formalization.FlashCosine.zhat (8 : Fin 9) : ℚ) : ℝ) := by
      have hDq0 : (0 : ℝ) ≤ (N11Formalization.FlashCosine.Dq : ℝ) :=
        N11Formalization.FlashCosine.Dq_pos.le
      have hDc0 : (0 : ℝ) ≤ Dc' := le_trans hDq0 hD.1
      have hm1 : (N11Formalization.FlashCosine.Dq : ℝ) * ((zhatLo (8 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((zhatLo (8 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_right hD.1 hpos
      have hm2 : Dc' * ((zhatLo (8 : Fin 9) : ℚ) : ℝ)
          ≤ Dc' * ((N11Formalization.FlashCosine.zhat (8 : Fin 9) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hzv hDc0
      linarith [hm1, hm2]
    linarith [hnum, hstep]

set_option maxHeartbeats 4000000 in
theorem stage3 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hdom : ∀ k : Fin 15,
        (N11Formalization.FlashCosine.sloB k : ℝ) ≤
          N11Formalization.FlashCosine.tval y (Fin.castSucc (N11Formalization.FlashCosine.jOf k)) -
            N11Formalization.FlashCosine.tval y (Fin.castSucc (N11Formalization.FlashCosine.iOf k)) ∧
        N11Formalization.FlashCosine.tval y (Fin.castSucc (N11Formalization.FlashCosine.jOf k)) -
          N11Formalization.FlashCosine.tval y (Fin.castSucc (N11Formalization.FlashCosine.iOf k)) ≤
          (N11Formalization.FlashCosine.shiB k : ℝ))
    (hrow : ∀ r : Fin 6, (∑ q : Fin 9, (N11Formalization.FlashCosine.rowA r q : ℝ) * y q) ≤
        (rowb r : ℝ)) :
    ((((1899919265599193545242591 : ℚ) / 5000000000000000000000000) : ℚ) : ℝ) ^ 2
      < ∑ k : Fin 15, (N11Formalization.FlashCosine.wlo k : ℝ) *
          ((N11Formalization.FlashCosine.sq k : ℝ) *
              N11Formalization.FlashCosine.zval y (N11Formalization.FlashCosine.iOf k)
                (N11Formalization.FlashCosine.jOf k) +
            (N11Formalization.FlashCosine.cq k : ℝ)) := by
  have _ := hdom
  have hWcoef : (N11Formalization.FlashCosine.Wcoef : ℝ) ≤ 0 := by
    simp [N11Formalization.FlashCosine.Wcoef, N11Formalization.FlashCosine.wlo,
      N11Formalization.FlashCosine.sq, N11Formalization.FlashCosine.iOf,
      N11Formalization.FlashCosine.jOf, Fin.sum_univ_succ]
    norm_num
  have hfac : (∑ q : Fin 9,
        (N11Formalization.FlashCosine.Dc * (N11Formalization.FlashCosine.zhat q : ℝ)) * y q)
      = N11Formalization.FlashCosine.Dc *
        (∑ q : Fin 9, (N11Formalization.FlashCosine.zhat q : ℝ) * y q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  have hlp := N11Formalization.FlashCosine.lp_step9
    (A := N11Formalization.FlashCosine.rowA) (bV := rowb)
    (lam := N11Formalization.FlashCosine.lamVal)
    (c := fun q => N11Formalization.FlashCosine.Dc * (N11Formalization.FlashCosine.zhat q : ℝ))
    (rmin := ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
        112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ)) (y := y)
    (fun r => by exact_mod_cast N11Formalization.FlashCosine.lamVal_nonneg r) hrow hy0 hy1 ?_
  · have hlp' : ((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
          112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) -
        (∑ r : Fin 6, (N11Formalization.FlashCosine.lamVal r : ℝ) * (rowb r : ℝ))
      ≤ N11Formalization.FlashCosine.Dc *
        (∑ q : Fin 9, (N11Formalization.FlashCosine.zhat q : ℝ) * y q) := by
      rw [hfac] at hlp; exact hlp
    rw [lamB_eq] at hlp'
    have hWL : (N11Formalization.FlashCosine.Wcoef : ℝ) * (N11Formalization.FlashCosine.LQ : ℝ) ≤
        (N11Formalization.FlashCosine.Wcoef : ℝ) * N11Formalization.FlashCosine.Lc :=
      mul_le_mul_of_nonpos_left N11Formalization.FlashCosine.L_mem.2 hWcoef
    have hnum : ((((1899919265599193545242591 : ℚ) / 5000000000000000000000000) : ℚ) : ℝ) ^ 2
        < (N11Formalization.FlashCosine.Wcoef : ℝ) * (N11Formalization.FlashCosine.LQ : ℝ) +
          (((((-18506337951167449716357909236406090684945576940786311 : ℚ) /
              112589990684262400000000000000000000000000000000000000000000000000) : ℚ) : ℝ) -
            (((-55717737991 : ℚ) / 4000000000000) : ℝ)) +
          (N11Formalization.FlashCosine.Cc : ℝ) := by
      simp [N11Formalization.FlashCosine.Wcoef, N11Formalization.FlashCosine.wlo,
        N11Formalization.FlashCosine.sq, N11Formalization.FlashCosine.cq,
        N11Formalization.FlashCosine.iOf, N11Formalization.FlashCosine.jOf,
        N11Formalization.FlashCosine.Cc, N11Formalization.FlashCosine.LQ,
        Fin.sum_univ_succ]
      norm_num
    rw [N11Formalization.FlashCosine.affine_id y]
    linarith [hlp', hWL, hnum]
  · intro q
    rw [← rowS_cast q]
    exact redcost N11Formalization.FlashCosine.Dc
      ⟨N11Formalization.FlashCosine.D_mem.1, N11Formalization.FlashCosine.D_mem.2⟩ q

theorem energy_v2 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hdom : ∀ k : Fin 15,
        (N11Formalization.FlashCosine.sloB k : ℝ) ≤
          N11Formalization.FlashCosine.tval y (Fin.castSucc (N11Formalization.FlashCosine.jOf k)) -
            N11Formalization.FlashCosine.tval y (Fin.castSucc (N11Formalization.FlashCosine.iOf k)) ∧
        N11Formalization.FlashCosine.tval y (Fin.castSucc (N11Formalization.FlashCosine.jOf k)) -
          N11Formalization.FlashCosine.tval y (Fin.castSucc (N11Formalization.FlashCosine.iOf k)) ≤
          (N11Formalization.FlashCosine.shiB k : ℝ))
    (hrow : ∀ r : Fin 6, (∑ q : Fin 9, (N11Formalization.FlashCosine.rowA r q : ℝ) * y q) ≤
        (rowb r : ℝ)) :
    ((((1899919265599193545242591 : ℚ) / 5000000000000000000000000) : ℚ) : ℝ) ^ 2
      < N11Formalization.ResumeNetwork.V2
        (fun j => N11Formalization.circleMap (N11Formalization.FlashCosine.theta y j)) := by
  have h1 := stage3 y hy0 hy1 hdom hrow
  have h2 := N11Formalization.FlashCosine.stage1 y hy0 hdom
  have h3 := N11Formalization.ResumeGlobal.C911Weights.c911_source_energy_le_oracle
    (fun j => N11Formalization.FlashCosine.theta y j)
  refine lt_of_lt_of_le h1 ?_
  exact le_trans h2 h3

#print axioms zhatLo_le
#print axioms rowS_cast
#print axioms lamB_eq
#print axioms redcost
#print axioms stage3
#print axioms energy_v2

end N11Formalization.FlashCosineLP
