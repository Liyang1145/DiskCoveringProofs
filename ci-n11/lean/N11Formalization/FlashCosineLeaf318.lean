/-
  STATUS: WORK IN PROGRESS - not in the root import graph, not for landing.
  The chart/data/helper layer below compiles; the 15 per-pair theorems are being debugged
  (current blocker class: endpoint normal form / tactic-block indentation in the arc steps).
  Numeric data is exact and independently verified (verify_pairs.py 15/15; assembled bound
  0.151727580238 > T^2, margin +7.340e-3) - see evidence/flash-cosine/HANDOFF.md §6.
-/
/-
  **FlashCosineLeaf318 — 15 per-pair kernel-checked whole-cell cosine minorants for ONE real
  C911 energy leaf (node #318 of `cosine_dbm_local920.json`, sha256 6706B426…).**

  Each pair theorem is exactly the interface `FlashCosineCore.minorant_of_sin_le/le_sin` consumes:
  a cell `[zq k, Zq k]` (outward rational bracket of the angular difference `z_k` on the leaf's
  DBM cell), a slope/intercept `(sq k, cq k)` and the two analytic side conditions, which here are
  closed rational inequalities discharged by `norm_num` against the kernel's own outward bounds
  `sinHiNLag/sinLoNLag/cosHiNLag` — no mpmath, no sampling, no precomputed energy bound.
  The chart/helper layer is the SOURCE caliber `theta_i = i*L − D*t_i` with `L = 2 arcsin(19/50)`
  (kernel bracket `ArcsinBracket.arc_L_mem`) and `D = 9L − 2 pi` (20-digit pi brackets).

  Domain: `y ≥ 0`, `Σ y = 1` (Fin 9, the SOURCE domain) plus the leaf's closed DBM rows
  (`t_j − t_i` bracketed by the recorded rationals). Conclusion of each pair theorem: on the cell,
  `s·z + c ≤ 1 − cos z` and `0 ≤ s·z + c` (the latter at both cell endpoints, hence throughout).

  Discipline: no `sorry`, no custom `axiom`, no `native_decide`.
-/
import Mathlib
import N11Formalization.FlashCosineCore
import N11Formalization.ResumeC911Weights
import N11Formalization.Interval.ArcsinBracket
import N11Formalization.G3ArcConstants

namespace N11Formalization.FlashCosine

open Finset
open N11Formalization.ResumeGlobal.C911Weights

/-! ## 1. Chart and helpers -/

noncomputable def Lc : ℝ := 2 * Real.arcsin (((19 : ℚ) / 50 : ℚ) : ℝ)

noncomputable def Dc : ℝ := 9 * Lc - 2 * Real.pi

def Lq : ℚ := 2 * (1150475603510479590494077 / 2951479051793528258560000)

def LQ : ℚ := 2 * (449404532622434011541355675101 / 1152921504606846976000000000000)

theorem L_mem : (Lq : ℝ) ≤ Lc ∧ Lc ≤ (LQ : ℝ) := by
  have h := N11Formalization.ArcsinBracket.arc_L_mem
  have h1 : (Lq : ℝ) = 2 * ((1150475603510479590494077 : ℝ) / 2951479051793528258560000) := by
    rw [Lq]; push_cast; ring
  have h2 : (LQ : ℝ) = 2 * ((449404532622434011541355675101 : ℝ) / 1152921504606846976000000000000) := by
    rw [LQ]; push_cast; ring
  constructor
  · rw [h1, Lc]; exact h.1
  · rw [h2, Lc]; exact h.2

def Dq : ℚ := 9 * Lq - 2 * N11Formalization.RatInterval.piHi

def DQ : ℚ := 9 * LQ - 2 * N11Formalization.RatInterval.piLo

theorem D_mem : (Dq : ℝ) ≤ Dc ∧ Dc ≤ (DQ : ℝ) := by
  have hL := L_mem
  have hpi := N11Formalization.RatInterval.pi_lt_piHi
  have hpi' := N11Formalization.RatInterval.piLo_lt_pi
  have hDq : (Dq : ℝ) = 9 * (Lq : ℝ) - 2 * ((N11Formalization.RatInterval.piHi : ℚ) : ℝ) := by
    rw [Dq]; push_cast; ring
  have hDQ : (DQ : ℝ) = 9 * (LQ : ℝ) - 2 * ((N11Formalization.RatInterval.piLo : ℚ) : ℝ) := by
    rw [DQ]; push_cast; ring
  constructor
  · rw [hDq, Dc]
    linarith [hL.1, hpi]
  · rw [hDQ, Dc]
    linarith [hL.2, hpi']
theorem Dq_pos : (0 : ℝ) < (Dq : ℝ) := by
  norm_num [Dq, Lq, N11Formalization.RatInterval.piHi]

def tval (y : Fin 9 → ℝ) (i : Fin 10) : ℝ := ∑ q : Fin 9, if (q : ℕ) < (i : ℕ) then y q else 0

noncomputable def theta (y : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  (i : ℕ) * Lc - Dc * tval y (Fin.castSucc i)

noncomputable def zval (y : Fin 9 → ℝ) (i j : Fin 9) : ℝ := theta y i - theta y j

theorem tval_sub (y : Fin 9 → ℝ) {i j : Fin 10} (hij : (i : ℕ) ≤ (j : ℕ)) :
    tval y j - tval y i = ∑ q : Fin 9, if (i : ℕ) ≤ (q : ℕ) ∧ (q : ℕ) < (j : ℕ) then y q else 0 := by
  rw [tval, tval, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h1 : (q : ℕ) < (i : ℕ)
  · have h2 : (q : ℕ) < (j : ℕ) := lt_of_lt_of_le h1 hij
    simp [h1, h2, not_le.mpr h1]
  · by_cases h2 : (q : ℕ) < (j : ℕ)
    · have h3 : (i : ℕ) ≤ (q : ℕ) := not_lt.mp h1
      simp [h1, h2, h3]
    · simp [h1, h2]

theorem zval_eq (y : Fin 9 → ℝ) (i j : Fin 9) :
    zval y i j = (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * Lc
      + Dc * (tval y (Fin.castSucc j) - tval y (Fin.castSucc i)) := by
  unfold zval theta; ring

/-- 角差 cell 的双侧界（由 L/D 括号与 DBM 的 `sigma` 括号得出）。 -/
theorem cell_bound {L D sig : ℝ} {i j : ℕ} (hij : i < j) {slo shi : ℚ}
    (hslo : (0 : ℚ) ≤ slo)
    (hLlo : (Lq : ℝ) ≤ L) (hLhi : L ≤ (LQ : ℝ)) (hDlo : (Dq : ℝ) ≤ D) (hDhi : D ≤ (DQ : ℝ))
    (hsig : (slo : ℝ) ≤ sig) (hsig2 : sig ≤ (shi : ℝ)) :
    ((((i : ℚ) - j) * LQ + Dq * slo : ℚ) : ℝ) ≤ ((i : ℝ) - j) * L + D * sig ∧
      ((i : ℝ) - j) * L + D * sig ≤ ((((i : ℚ) - j) * Lq + DQ * shi : ℚ) : ℝ) := by
  have hD0 : (0 : ℝ) < Dq := Dq_pos
  have hijR : ((i : ℝ) - j) ≤ 0 := by
    have : (i : ℝ) < j := by exact_mod_cast hij
    linarith
  have hslo0 : (0 : ℝ) ≤ (slo : ℝ) := by exact_mod_cast hslo
  constructor
  · have h1 : ((i : ℝ) - j) * ((LQ : ℚ) : ℝ) ≤ ((i : ℝ) - j) * L := by
      have hfac : ((i : ℝ) - j) ≤ 0 := hijR
      have hLQ : L ≤ ((LQ : ℚ) : ℝ) := hLhi
      have hprod : (0 : ℝ) ≤ (-((i : ℝ) - j)) * (((LQ : ℚ) : ℝ) - L) :=
        mul_nonneg (neg_nonneg.mpr hfac) (sub_nonneg.mpr hLQ)
      nlinarith [hprod]
    have h2 : (Dq : ℝ) * (slo : ℝ) ≤ D * sig := by
      have h3 : (Dq : ℝ) * (slo : ℝ) ≤ (Dq : ℝ) * sig := mul_le_mul_of_nonneg_left hsig hD0.le
      have h4 : (Dq : ℝ) * sig ≤ D * sig := mul_le_mul_of_nonneg_right hDlo (le_trans hslo0 hsig)
      linarith
    have hcast : ((((i : ℚ) - j) * LQ + Dq * slo : ℚ) : ℝ) = ((i : ℝ) - j) * ((LQ : ℚ) : ℝ)
        + (Dq : ℝ) * (slo : ℝ) := by push_cast; ring
    rw [hcast]; linarith
  · have h1 : ((i : ℝ) - j) * L ≤ ((i : ℝ) - j) * ((Lq : ℚ) : ℝ) := by
      have hfac : ((i : ℝ) - j) ≤ 0 := hijR
      have hLq : ((Lq : ℚ) : ℝ) ≤ L := hLlo
      have hprod : (0 : ℝ) ≤ (-((i : ℝ) - j)) * (L - ((Lq : ℚ) : ℝ)) :=
        mul_nonneg (neg_nonneg.mpr hfac) (sub_nonneg.mpr hLq)
      nlinarith [hprod]
    have h2 : D * sig ≤ (DQ : ℝ) * (shi : ℝ) := by
      have h3 : D * sig ≤ (DQ : ℝ) * sig := mul_le_mul_of_nonneg_right hDhi (le_trans hslo0 hsig)
      have h4 : (DQ : ℝ) * sig ≤ (DQ : ℝ) * (shi : ℝ) :=
        mul_le_mul_of_nonneg_left hsig2 (by linarith [hD0, hDlo])
      linarith
    have hcast : ((((i : ℚ) - j) * Lq + DQ * shi : ℚ) : ℝ) = ((i : ℝ) - j) * ((Lq : ℚ) : ℝ)
        + (DQ : ℝ) * (shi : ℝ) := by push_cast; ring
    rw [hcast]; linarith

theorem weight2_cast (i j : Fin 9) :
    (2 * weight i j : ℝ) = ((2 * (wNum i j / wDen i j) : ℚ) : ℝ) := by
  unfold weight
  push_cast
  ring

theorem wNum_nonneg : ∀ i j : Fin 9, (0 : ℤ) ≤ wNum i j := by decide

theorem weight_nonneg (i j : Fin 9) : (0 : ℝ) ≤ 2 * weight i j := by
  rw [weight2_cast]
  have h1 : (0 : ℚ) ≤ (wNum i j : ℚ) := by exact_mod_cast (wNum_nonneg i j)
  have h2 : (0 : ℚ) < (wDen i j : ℚ) := by exact_mod_cast (den_pos i j)
  have h3 : (0 : ℚ) ≤ 2 * (wNum i j / wDen i j) := by positivity
  exact_mod_cast h3


/-! ## 2. Leaf-318 data (match-defined: reduces at concrete indices) -/

def iOf : Fin 15 → Fin 9
  | 0 => (0 : Fin 9)
  | 1 => (0 : Fin 9)
  | 2 => (0 : Fin 9)
  | 3 => (0 : Fin 9)
  | 4 => (0 : Fin 9)
  | 5 => (3 : Fin 9)
  | 6 => (3 : Fin 9)
  | 7 => (3 : Fin 9)
  | 8 => (3 : Fin 9)
  | 9 => (4 : Fin 9)
  | 10 => (4 : Fin 9)
  | 11 => (4 : Fin 9)
  | 12 => (5 : Fin 9)
  | 13 => (5 : Fin 9)
  | 14 => (7 : Fin 9)

def jOf : Fin 15 → Fin 9
  | 0 => (3 : Fin 9)
  | 1 => (4 : Fin 9)
  | 2 => (5 : Fin 9)
  | 3 => (7 : Fin 9)
  | 4 => (8 : Fin 9)
  | 5 => (4 : Fin 9)
  | 6 => (5 : Fin 9)
  | 7 => (7 : Fin 9)
  | 8 => (8 : Fin 9)
  | 9 => (5 : Fin 9)
  | 10 => (7 : Fin 9)
  | 11 => (8 : Fin 9)
  | 12 => (7 : Fin 9)
  | 13 => (8 : Fin 9)
  | 14 => (8 : Fin 9)

def wlo : Fin 15 → ℚ
  | 0 => ((1574948903583 : ℚ) / 250000000000000)
  | 1 => ((425349101103 : ℚ) / 62500000000000)
  | 2 => ((4483646868437 : ℚ) / 1000000000000000)
  | 3 => ((11978106160769 : ℚ) / 1000000000000000)
  | 4 => ((31052389696227 : ℚ) / 500000000000000)
  | 5 => ((14349213499701 : ℚ) / 250000000000000)
  | 6 => ((11677961094779 : ℚ) / 1000000000000000)
  | 7 => ((4421568400769 : ℚ) / 1000000000000000)
  | 8 => ((1708494742773 : ℚ) / 250000000000000)
  | 9 => ((48015899351253 : ℚ) / 1000000000000000)
  | 10 => ((238828088513 : ℚ) / 50000000000000)
  | 11 => ((184566422579 : ℚ) / 25000000000000)
  | 12 => ((125875526881 : ℚ) / 40000000000000)
  | 13 => ((2431916118209 : ℚ) / 500000000000000)
  | 14 => ((49289522253343 : ℚ) / 1000000000000000)

def zq : Fin 15 → ℚ
  | 0 => ((-215549077151228746463 : ℚ) / 100000000000000000000)
  | 1 => ((-293508336446280859181 : ℚ) / 100000000000000000000)
  | 2 => ((-3714675957413329719 : ℚ) / 1000000000000000000)
  | 3 => ((-490728712863582013951 : ℚ) / 100000000000000000000)
  | 4 => ((-568687972158634126669 : ℚ) / 100000000000000000000)
  | 5 => ((-77959259295052112719 : ℚ) / 100000000000000000000)
  | 6 => ((-77959259295052112719 : ℚ) / 50000000000000000000)
  | 7 => ((-8599363616011039609 : ℚ) / 3125000000000000000)
  | 8 => ((-353138895007405380207 : ℚ) / 100000000000000000000)
  | 9 => ((-77959259295052112719 : ℚ) / 100000000000000000000)
  | 10 => ((-215549077151228746463 : ℚ) / 100000000000000000000)
  | 11 => ((-293508336446280859181 : ℚ) / 100000000000000000000)
  | 12 => ((-8599363616011039609 : ℚ) / 6250000000000000000)
  | 13 => ((-215549077151228746463 : ℚ) / 100000000000000000000)
  | 14 => ((-77959259295052112719 : ℚ) / 100000000000000000000)

def Zq : Fin 15 → ℚ
  | 0 => ((-12326273525987572173 : ℚ) / 6250000000000000000)
  | 1 => ((-137589817855326633743 : ℚ) / 50000000000000000000)
  | 2 => ((-70627779001101076041 : ℚ) / 20000000000000000000)
  | 3 => ((-236200006063227211127 : ℚ) / 50000000000000000000)
  | 4 => ((-550359271421306534973 : ℚ) / 100000000000000000000)
  | 5 => ((-931727477507414391 : ℚ) / 1562500000000000000)
  | 6 => ((-137589817855326633743 : ℚ) / 100000000000000000000)
  | 7 => ((-16053183436017229737 : ℚ) / 6250000000000000000)
  | 8 => ((-334810194271127788511 : ℚ) / 100000000000000000000)
  | 9 => ((-931727477507414391 : ℚ) / 1562500000000000000)
  | 10 => ((-12326273525987572173 : ℚ) / 6250000000000000000)
  | 11 => ((-137589817855326633743 : ℚ) / 50000000000000000000)
  | 12 => ((-119261117120949042049 : ℚ) / 100000000000000000000)
  | 13 => ((-12326273525987572173 : ℚ) / 6250000000000000000)
  | 14 => ((-931727477507414391 : ℚ) / 1562500000000000000)

def sq : Fin 15 → ℚ
  | 0 => ((-920512000003517 : ℚ) / 1000000000000000)
  | 1 => ((-51261153396029 : ℚ) / 250000000000000)
  | 2 => ((271112658020957 : ℚ) / 500000000000000)
  | 3 => ((196213479984221 : ℚ) / 200000000000000)
  | 4 => ((561589495202439 : ℚ) / 1000000000000000)
  | 5 => ((-280794747620833 : ℚ) / 500000000000000)
  | 6 => ((-196213479984651 : ℚ) / 200000000000000)
  | 7 => ((-33889082252803 : ℚ) / 62500000000000)
  | 8 => ((51261153394683 : ℚ) / 250000000000000)
  | 9 => ((-280794747620833 : ℚ) / 500000000000000)
  | 10 => ((-52117548400211 : ℚ) / 62500000000000)
  | 11 => ((-15200000000333 : ℚ) / 40000000000000)
  | 12 => ((-490533699962451 : ℚ) / 500000000000000)
  | 13 => ((-920512000003517 : ℚ) / 1000000000000000)
  | 14 => ((-280794747620833 : ℚ) / 500000000000000)

def cq : Fin 15 → ℚ
  | 0 => ((-216105254824753 : ℚ) / 500000000000000)
  | 1 => ((1360745465679267 : ℚ) / 1000000000000000)
  | 2 => ((1919897487950859 : ℚ) / 500000000000000)
  | 3 => ((5620712811418413 : ℚ) / 1000000000000000)
  | 4 => ((673255182175999 : ℚ) / 200000000000000)
  | 5 => ((-10143434619007 : ℚ) / 62500000000000)
  | 6 => ((-543515461119757 : ℚ) / 1000000000000000)
  | 7 => ((86578567391689 : ℚ) / 200000000000000)
  | 8 => ((165567423065507 : ℚ) / 62500000000000)
  | 9 => ((-10143434619007 : ℚ) / 62500000000000)
  | 10 => ((-10154740411817 : ℚ) / 40000000000000)
  | 11 => ((34536837971489 : ℚ) / 40000000000000)
  | 12 => ((-543515461122023 : ℚ) / 1000000000000000)
  | 13 => ((-216105254824753 : ℚ) / 500000000000000)
  | 14 => ((-10143434619007 : ℚ) / 62500000000000)

def isA : Fin 15 → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => false
  | 4 => false
  | 5 => true
  | 6 => true
  | 7 => false
  | 8 => false
  | 9 => true
  | 10 => true
  | 11 => false
  | 12 => false
  | 13 => false
  | 14 => true

def isInc : Fin 15 → Bool
  | 0 => false
  | 1 => false
  | 2 => false
  | 3 => true
  | 4 => true
  | 5 => true
  | 6 => true
  | 7 => false
  | 8 => false
  | 9 => true
  | 10 => false
  | 11 => false
  | 12 => true
  | 13 => false
  | 14 => true

def arcM : Fin 15 → ℤ
  | 0 => -1
  | 1 => -1
  | 2 => -1
  | 3 => -1
  | 4 => -1
  | 5 => 0
  | 6 => 0
  | 7 => -1
  | 8 => -1
  | 9 => 0
  | 10 => -1
  | 11 => -1
  | 12 => 0
  | 13 => -1
  | 14 => 0


/-- 角度 cell 的 `slo`（该对 DBM 的下界，取字面量）。 -/
def sloB : Fin 15 → ℚ
  | 0 => ((1 : ℚ) / 4)
  | 1 => ((1 : ℚ) / 4)
  | 2 => ((1 : ℚ) / 4)
  | 3 => ((3 : ℚ) / 4)
  | 4 => ((3 : ℚ) / 4)
  | 5 => (0 : ℚ)
  | 6 => (0 : ℚ)
  | 7 => ((1 : ℚ) / 2)
  | 8 => ((1 : ℚ) / 2)
  | 9 => (0 : ℚ)
  | 10 => ((1 : ℚ) / 4)
  | 11 => ((1 : ℚ) / 4)
  | 12 => ((1 : ℚ) / 4)
  | 13 => ((1 : ℚ) / 4)
  | 14 => (0 : ℚ)


/-- 角度 cell 的 `shi`（该对 DBM 的上界）。 -/
def shiB : Fin 15 → ℚ
  | 0 => ((1 : ℚ) / 2)
  | 1 => ((1 : ℚ) / 2)
  | 2 => ((1 : ℚ) / 2)
  | 3 => (1 : ℚ)
  | 4 => (1 : ℚ)
  | 5 => ((1 : ℚ) / 4)
  | 6 => ((1 : ℚ) / 4)
  | 7 => ((3 : ℚ) / 4)
  | 8 => ((3 : ℚ) / 4)
  | 9 => ((1 : ℚ) / 4)
  | 10 => ((1 : ℚ) / 2)
  | 11 => ((1 : ℚ) / 2)
  | 12 => ((1 : ℚ) / 2)
  | 13 => ((1 : ℚ) / 2)
  | 14 => ((1 : ℚ) / 4)


/-- `zhat_q`（LP 对偶系数，符号形式 `sum_k wlo_k s_k [q in [i_k,j_k)]`）。 -/
def zhat : Fin 9 → ℚ := fun q => ∑ k : Fin 15,
  if ((iOf k : ℕ) ≤ (q : ℕ) ∧ (q : ℕ) < (jOf k : ℕ)) then wlo k * sq k else 0

/-- `Wcoef = sum_k wlo_k s_k (i_k - j_k)`。 -/
def Wcoef : ℚ := ∑ k : Fin 15, wlo k * sq k * ((iOf k : ℚ) - (jOf k : ℕ))

/-- `Cc = sum_k wlo_k c_k`。 -/
def Cc : ℚ := ∑ k : Fin 15, wlo k * cq k

/-- LP 非零对偶行数（6）。 -/
def lamN : ℕ := 6

def lamVal : Fin 6 → ℚ
  | 0 => ((1425515267 : ℚ) / 50000000000)
  | 1 => ((436643377 : ℚ) / 200000000000)
  | 2 => ((5718481 : ℚ) / 62500000000)
  | 3 => ((5187319423 : ℚ) / 250000000000)
  | 4 => ((1218717543 : ℚ) / 1000000000000)
  | 5 => ((482249671 : ℚ) / 500000000000)

theorem lamVal_nonneg : ∀ r : Fin 6, (0 : ℚ) ≤ lamVal r := by
  intro r
  fin_cases r <;> norm_num [lamVal]


/-- LP 的 6 条行：`(i,j,sgn)`（sgn = true 时取 `hiB i j`，否则取 `-loB i j`）。 -/
def lamIJ : Fin 6 → Fin 10 × Fin 10
  | 0 => ((0 : Fin 10), (3 : Fin 10))
  | 1 => ((0 : Fin 10), (9 : Fin 10))
  | 2 => ((4 : Fin 10), (5 : Fin 10))
  | 3 => ((5 : Fin 10), (7 : Fin 10))
  | 4 => ((7 : Fin 10), (9 : Fin 10))
  | 5 => ((8 : Fin 10), (9 : Fin 10))

def lamSgn : Fin 6 → Bool
  | 0 => false
  | 1 => false
  | 2 => true
  | 3 => false
  | 4 => true
  | 5 => true

def rowA (r : Fin 6) (q : Fin 9) : ℚ :=
  if ((lamIJ r).1 : ℕ) ≤ (q : ℕ) ∧ (q : ℕ) < ((lamIJ r).2 : ℕ) then
    (if lamSgn r then (1 : ℚ) else (-1 : ℚ)) else 0

theorem lamIJ_lt : ∀ r : Fin 6, ((lamIJ r).1 : ℕ) < ((lamIJ r).2 : ℕ) := by decide

set_option maxHeartbeats 4000000 in
/-- pair 0: (i,j) = (0,3), shape b, arc dec, m = -1. -/
theorem pairCert_0 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 0 : ℝ)) ≤ zval y (0 : Fin 9) (3 : Fin 9) ∧
      zval y (0 : Fin 9) (3 : Fin 9) ≤ ((Zq 0 : ℝ)) ∧
      (((sq 0 : ℝ)) * zval y (0 : Fin 9) (3 : Fin 9) + ((cq 0 : ℝ))
        ≤ 1 - Real.cos (zval y (0 : Fin 9) (3 : Fin 9))) ∧
      0 ≤ ((sq 0 : ℝ)) * zval y (0 : Fin 9) (3 : Fin 9) + ((cq 0 : ℝ)) := by
  have hlt : (0 : ℕ) < (3 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 0) (j := 3) hlt
      (slo := ((1 : ℚ) / 4)) (shi := ((1 : ℚ) / 2)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 0).1 (hdom 0).2
  have hzlo : ((zq 0 : ℝ)) ≤ zval y (0 : Fin 9) (3 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (0 : Fin 9) (3 : Fin 9) ≤ ((Zq 0 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : Real.pi / 2 ≤ (zq 0 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : Real.pi / 2 ≤ (zq 0 : ℝ) + 2 * Real.pi := by
      have hq : (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 ≤ (zq 0 : ℝ) + 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : Real.pi / 2 ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.pi_lt_piHi
        linarith
      have h2 : 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) ≤ 2 * Real.pi := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : Real.pi / 2 ≤ (zq 0 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 0 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := by
    have hnorm : (Zq 0 : ℝ) + 2 * Real.pi ≤ 3 * Real.pi / 2 := by
      have hq : (Zq 0 : ℝ) + 2 * (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) ≤ 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ 3 * Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : Real.pi ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) := (N11Formalization.RatInterval.pi_lt_piHi).le
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 0 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 0 : ℝ)) ((Zq 0 : ℝ)), ((sq 0 : ℝ)) ≤ Real.sin t := by
    intro t ht
    have h1 : Real.sin ((Zq 0 : ℝ)) ≤ Real.sin t :=
      FlashCosine.arc_dec_le_sin (m := -1) (a := (zq 0 : ℝ)) (b := (Zq 0 : ℝ)) harc_lo' harc_hi' ht
    have h2 : ((N11Formalization.sinLoNLag ((Zq 0)) : ℚ) : ℝ) ≤ Real.sin ((Zq 0 : ℝ)) :=
      N11Formalization.sinLoNLag_le_sin (q := (Zq 0))
    have h3 : ((sq 0 : ℝ)) ≤ ((N11Formalization.sinLoNLag ((Zq 0)) : ℚ) : ℝ) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 0 : ℝ)) ((Zq 0 : ℝ)),
      ((sq 0 : ℝ)) * z + ((cq 0 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_le_sin hsin ?_
    have h4 : ((cq 0 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((zq 0)) : ℚ) : ℝ)
        - ((sq 0 : ℝ)) * ((zq 0 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((zq 0 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((zq 0)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (zq 0))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 0 : ℝ)) * ((zq 0 : ℝ)) + ((cq 0 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 0 : ℝ)) * ((Zq 0 : ℝ)) + ((cq 0 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 1: (i,j) = (0,4), shape a, arc dec, m = -1. -/
theorem pairCert_1 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 1 : ℝ)) ≤ zval y (0 : Fin 9) (4 : Fin 9) ∧
      zval y (0 : Fin 9) (4 : Fin 9) ≤ ((Zq 1 : ℝ)) ∧
      (((sq 1 : ℝ)) * zval y (0 : Fin 9) (4 : Fin 9) + ((cq 1 : ℝ))
        ≤ 1 - Real.cos (zval y (0 : Fin 9) (4 : Fin 9))) ∧
      0 ≤ ((sq 1 : ℝ)) * zval y (0 : Fin 9) (4 : Fin 9) + ((cq 1 : ℝ)) := by
  have hlt : (0 : ℕ) < (4 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 0) (j := 4) hlt
      (slo := ((1 : ℚ) / 4)) (shi := ((1 : ℚ) / 2)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 1).1 (hdom 1).2
  have hzlo : ((zq 1 : ℝ)) ≤ zval y (0 : Fin 9) (4 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (0 : Fin 9) (4 : Fin 9) ≤ ((Zq 1 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : Real.pi / 2 ≤ (zq 1 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : Real.pi / 2 ≤ (zq 1 : ℝ) + 2 * Real.pi := by
      have hq : (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 ≤ (zq 1 : ℝ) + 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : Real.pi / 2 ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.pi_lt_piHi
        linarith
      have h2 : 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) ≤ 2 * Real.pi := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : Real.pi / 2 ≤ (zq 1 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 1 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := by
    have hnorm : (Zq 1 : ℝ) + 2 * Real.pi ≤ 3 * Real.pi / 2 := by
      have hq : (Zq 1 : ℝ) + 2 * (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) ≤ 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ 3 * Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : Real.pi ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) := (N11Formalization.RatInterval.pi_lt_piHi).le
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 1 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 1 : ℝ)) ((Zq 1 : ℝ)), Real.sin t ≤ ((sq 1 : ℝ) : ℝ) := by
    intro t ht
    have h1 : Real.sin t ≤ Real.sin ((zq 1 : ℝ)) :=
      FlashCosine.sin_le_sin_of_mem_arc_dec (m := -1) (a := (zq 1 : ℝ)) (b := (Zq 1 : ℝ)) harc_lo' harc_hi' ht
    have h2 : Real.sin ((zq 1 : ℝ)) ≤ ((N11Formalization.sinHiNLag ((zq 1)) : ℚ) : ℝ) := by
      have hh := N11Formalization.sin_le_sinHiNLag (q := (zq 1))
      have hc : (((zq 1) : ℚ) : ℝ) = ((zq 1 : ℝ)) := by norm_num
      linarith [hh, hc]
    have h3 : ((N11Formalization.sinHiNLag ((zq 1)) : ℚ) : ℝ) ≤ ((sq 1 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 1 : ℝ)) ((Zq 1 : ℝ)),
      ((sq 1 : ℝ)) * z + ((cq 1 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_sin_le hsin ?_
    have h4 : ((cq 1 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((Zq 1)) : ℚ) : ℝ)
        - ((sq 1 : ℝ)) * ((Zq 1 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((Zq 1 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((Zq 1)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (Zq 1))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 1 : ℝ)) * ((zq 1 : ℝ)) + ((cq 1 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 1 : ℝ)) * ((Zq 1 : ℝ)) + ((cq 1 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 2: (i,j) = (0,5), shape a, arc dec, m = -1. -/
theorem pairCert_2 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 2 : ℝ)) ≤ zval y (0 : Fin 9) (5 : Fin 9) ∧
      zval y (0 : Fin 9) (5 : Fin 9) ≤ ((Zq 2 : ℝ)) ∧
      (((sq 2 : ℝ)) * zval y (0 : Fin 9) (5 : Fin 9) + ((cq 2 : ℝ))
        ≤ 1 - Real.cos (zval y (0 : Fin 9) (5 : Fin 9))) ∧
      0 ≤ ((sq 2 : ℝ)) * zval y (0 : Fin 9) (5 : Fin 9) + ((cq 2 : ℝ)) := by
  have hlt : (0 : ℕ) < (5 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 0) (j := 5) hlt
      (slo := ((1 : ℚ) / 4)) (shi := ((1 : ℚ) / 2)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 2).1 (hdom 2).2
  have hzlo : ((zq 2 : ℝ)) ≤ zval y (0 : Fin 9) (5 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (0 : Fin 9) (5 : Fin 9) ≤ ((Zq 2 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : Real.pi / 2 ≤ (zq 2 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : Real.pi / 2 ≤ (zq 2 : ℝ) + 2 * Real.pi := by
      have hq : (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 ≤ (zq 2 : ℝ) + 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : Real.pi / 2 ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.pi_lt_piHi
        linarith
      have h2 : 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) ≤ 2 * Real.pi := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : Real.pi / 2 ≤ (zq 2 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 2 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := by
    have hnorm : (Zq 2 : ℝ) + 2 * Real.pi ≤ 3 * Real.pi / 2 := by
      have hq : (Zq 2 : ℝ) + 2 * (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) ≤ 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ 3 * Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : Real.pi ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) := (N11Formalization.RatInterval.pi_lt_piHi).le
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 2 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 2 : ℝ)) ((Zq 2 : ℝ)), Real.sin t ≤ ((sq 2 : ℝ) : ℝ) := by
    intro t ht
    have h1 : Real.sin t ≤ Real.sin ((zq 2 : ℝ)) :=
      FlashCosine.sin_le_sin_of_mem_arc_dec (m := -1) (a := (zq 2 : ℝ)) (b := (Zq 2 : ℝ)) harc_lo' harc_hi' ht
    have h2 : Real.sin ((zq 2 : ℝ)) ≤ ((N11Formalization.sinHiNLag ((zq 2)) : ℚ) : ℝ) := by
      have hh := N11Formalization.sin_le_sinHiNLag (q := (zq 2))
      have hc : (((zq 2) : ℚ) : ℝ) = ((zq 2 : ℝ)) := by norm_num
      linarith [hh, hc]
    have h3 : ((N11Formalization.sinHiNLag ((zq 2)) : ℚ) : ℝ) ≤ ((sq 2 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 2 : ℝ)) ((Zq 2 : ℝ)),
      ((sq 2 : ℝ)) * z + ((cq 2 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_sin_le hsin ?_
    have h4 : ((cq 2 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((Zq 2)) : ℚ) : ℝ)
        - ((sq 2 : ℝ)) * ((Zq 2 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((Zq 2 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((Zq 2)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (Zq 2))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 2 : ℝ)) * ((zq 2 : ℝ)) + ((cq 2 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 2 : ℝ)) * ((Zq 2 : ℝ)) + ((cq 2 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 3: (i,j) = (0,7), shape b, arc inc, m = -1. -/
theorem pairCert_3 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 3 : ℝ)) ≤ zval y (0 : Fin 9) (7 : Fin 9) ∧
      zval y (0 : Fin 9) (7 : Fin 9) ≤ ((Zq 3 : ℝ)) ∧
      (((sq 3 : ℝ)) * zval y (0 : Fin 9) (7 : Fin 9) + ((cq 3 : ℝ))
        ≤ 1 - Real.cos (zval y (0 : Fin 9) (7 : Fin 9))) ∧
      0 ≤ ((sq 3 : ℝ)) * zval y (0 : Fin 9) (7 : Fin 9) + ((cq 3 : ℝ)) := by
  have hlt : (0 : ℕ) < (7 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 0) (j := 7) hlt
      (slo := ((3 : ℚ) / 4)) (shi := (1 : ℚ)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 3).1 (hdom 3).2
  have hzlo : ((zq 3 : ℝ)) ≤ zval y (0 : Fin 9) (7 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (0 : Fin 9) (7 : Fin 9) ≤ ((Zq 3 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : -(Real.pi / 2) ≤ (zq 3 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : -(Real.pi / 2) ≤ (zq 3 : ℝ) + 2 * Real.pi := by
      have hq : -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ (zq 3 : ℝ) + 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : -(Real.pi / 2) ≤ -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) ≤ 2 * Real.pi := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : -(Real.pi / 2) ≤ (zq 3 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 3 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := by
    have hnorm : (Zq 3 : ℝ) + 2 * Real.pi ≤ Real.pi / 2 := by
      have hq : (Zq 3 : ℝ) + 2 * (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) ≤ (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : Real.pi ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) := (N11Formalization.RatInterval.pi_lt_piHi).le
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 3 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 3 : ℝ)) ((Zq 3 : ℝ)), ((sq 3 : ℝ)) ≤ Real.sin t := by
    intro t ht
    have h1 : Real.sin ((zq 3 : ℝ)) ≤ Real.sin t :=
      FlashCosine.arc_inc_le_sin (m := -1) (a := (zq 3 : ℝ)) (b := (Zq 3 : ℝ)) harc_lo' harc_hi' ht
    have h2 : ((N11Formalization.sinLoNLag ((zq 3)) : ℚ) : ℝ) ≤ Real.sin ((zq 3 : ℝ)) :=
      N11Formalization.sinLoNLag_le_sin (q := (zq 3))
    have h3 : ((sq 3 : ℝ)) ≤ ((N11Formalization.sinLoNLag ((zq 3)) : ℚ) : ℝ) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 3 : ℝ)) ((Zq 3 : ℝ)),
      ((sq 3 : ℝ)) * z + ((cq 3 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_le_sin hsin ?_
    have h4 : ((cq 3 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((zq 3)) : ℚ) : ℝ)
        - ((sq 3 : ℝ)) * ((zq 3 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((zq 3 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((zq 3)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (zq 3))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 3 : ℝ)) * ((zq 3 : ℝ)) + ((cq 3 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 3 : ℝ)) * ((Zq 3 : ℝ)) + ((cq 3 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 4: (i,j) = (0,8), shape b, arc inc, m = -1. -/
theorem pairCert_4 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 4 : ℝ)) ≤ zval y (0 : Fin 9) (8 : Fin 9) ∧
      zval y (0 : Fin 9) (8 : Fin 9) ≤ ((Zq 4 : ℝ)) ∧
      (((sq 4 : ℝ)) * zval y (0 : Fin 9) (8 : Fin 9) + ((cq 4 : ℝ))
        ≤ 1 - Real.cos (zval y (0 : Fin 9) (8 : Fin 9))) ∧
      0 ≤ ((sq 4 : ℝ)) * zval y (0 : Fin 9) (8 : Fin 9) + ((cq 4 : ℝ)) := by
  have hlt : (0 : ℕ) < (8 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 0) (j := 8) hlt
      (slo := ((3 : ℚ) / 4)) (shi := (1 : ℚ)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 4).1 (hdom 4).2
  have hzlo : ((zq 4 : ℝ)) ≤ zval y (0 : Fin 9) (8 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (0 : Fin 9) (8 : Fin 9) ≤ ((Zq 4 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : -(Real.pi / 2) ≤ (zq 4 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : -(Real.pi / 2) ≤ (zq 4 : ℝ) + 2 * Real.pi := by
      have hq : -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ (zq 4 : ℝ) + 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : -(Real.pi / 2) ≤ -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) ≤ 2 * Real.pi := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : -(Real.pi / 2) ≤ (zq 4 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 4 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := by
    have hnorm : (Zq 4 : ℝ) + 2 * Real.pi ≤ Real.pi / 2 := by
      have hq : (Zq 4 : ℝ) + 2 * (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) ≤ (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : Real.pi ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) := (N11Formalization.RatInterval.pi_lt_piHi).le
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 4 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 4 : ℝ)) ((Zq 4 : ℝ)), ((sq 4 : ℝ)) ≤ Real.sin t := by
    intro t ht
    have h1 : Real.sin ((zq 4 : ℝ)) ≤ Real.sin t :=
      FlashCosine.arc_inc_le_sin (m := -1) (a := (zq 4 : ℝ)) (b := (Zq 4 : ℝ)) harc_lo' harc_hi' ht
    have h2 : ((N11Formalization.sinLoNLag ((zq 4)) : ℚ) : ℝ) ≤ Real.sin ((zq 4 : ℝ)) :=
      N11Formalization.sinLoNLag_le_sin (q := (zq 4))
    have h3 : ((sq 4 : ℝ)) ≤ ((N11Formalization.sinLoNLag ((zq 4)) : ℚ) : ℝ) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 4 : ℝ)) ((Zq 4 : ℝ)),
      ((sq 4 : ℝ)) * z + ((cq 4 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_le_sin hsin ?_
    have h4 : ((cq 4 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((zq 4)) : ℚ) : ℝ)
        - ((sq 4 : ℝ)) * ((zq 4 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((zq 4 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((zq 4)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (zq 4))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 4 : ℝ)) * ((zq 4 : ℝ)) + ((cq 4 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 4 : ℝ)) * ((Zq 4 : ℝ)) + ((cq 4 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 5: (i,j) = (3,4), shape a, arc inc, m = 0. -/
theorem pairCert_5 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 5 : ℝ)) ≤ zval y (3 : Fin 9) (4 : Fin 9) ∧
      zval y (3 : Fin 9) (4 : Fin 9) ≤ ((Zq 5 : ℝ)) ∧
      (((sq 5 : ℝ)) * zval y (3 : Fin 9) (4 : Fin 9) + ((cq 5 : ℝ))
        ≤ 1 - Real.cos (zval y (3 : Fin 9) (4 : Fin 9))) ∧
      0 ≤ ((sq 5 : ℝ)) * zval y (3 : Fin 9) (4 : Fin 9) + ((cq 5 : ℝ)) := by
  have hlt : (3 : ℕ) < (4 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 3) (j := 4) hlt
      (slo := (0 : ℚ)) (shi := ((1 : ℚ) / 4)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 5).1 (hdom 5).2
  have hzlo : ((zq 5 : ℝ)) ≤ zval y (3 : Fin 9) (4 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (3 : Fin 9) (4 : Fin 9) ≤ ((Zq 5 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : -(Real.pi / 2) ≤ (zq 5 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : -(Real.pi / 2) ≤ (zq 5 : ℝ) := by
      have hq : -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ (zq 5 : ℝ) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : -(Real.pi / 2) ≤ -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : -(Real.pi / 2) ≤ (zq 5 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 5 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := by
    have hnorm : (Zq 5 : ℝ) ≤ Real.pi / 2 := by
      have hq : (Zq 5 : ℝ) ≤ (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 5 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 5 : ℝ)) ((Zq 5 : ℝ)), Real.sin t ≤ ((sq 5 : ℝ) : ℝ) := by
    intro t ht
    have h1 : Real.sin t ≤ Real.sin ((Zq 5 : ℝ)) :=
      FlashCosine.sin_le_sin_of_mem_arc_inc (m := 0) (a := (zq 5 : ℝ)) (b := (Zq 5 : ℝ)) harc_lo' harc_hi' ht
    have h2 : Real.sin ((Zq 5 : ℝ)) ≤ ((N11Formalization.sinHiNLag ((Zq 5)) : ℚ) : ℝ) := by
      have hh := N11Formalization.sin_le_sinHiNLag (q := (Zq 5))
      have hc : (((Zq 5) : ℚ) : ℝ) = ((Zq 5 : ℝ)) := by norm_num
      linarith [hh, hc]
    have h3 : ((N11Formalization.sinHiNLag ((Zq 5)) : ℚ) : ℝ) ≤ ((sq 5 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 5 : ℝ)) ((Zq 5 : ℝ)),
      ((sq 5 : ℝ)) * z + ((cq 5 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_sin_le hsin ?_
    have h4 : ((cq 5 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((Zq 5)) : ℚ) : ℝ)
        - ((sq 5 : ℝ)) * ((Zq 5 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((Zq 5 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((Zq 5)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (Zq 5))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 5 : ℝ)) * ((zq 5 : ℝ)) + ((cq 5 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 5 : ℝ)) * ((Zq 5 : ℝ)) + ((cq 5 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 6: (i,j) = (3,5), shape a, arc inc, m = 0. -/
theorem pairCert_6 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 6 : ℝ)) ≤ zval y (3 : Fin 9) (5 : Fin 9) ∧
      zval y (3 : Fin 9) (5 : Fin 9) ≤ ((Zq 6 : ℝ)) ∧
      (((sq 6 : ℝ)) * zval y (3 : Fin 9) (5 : Fin 9) + ((cq 6 : ℝ))
        ≤ 1 - Real.cos (zval y (3 : Fin 9) (5 : Fin 9))) ∧
      0 ≤ ((sq 6 : ℝ)) * zval y (3 : Fin 9) (5 : Fin 9) + ((cq 6 : ℝ)) := by
  have hlt : (3 : ℕ) < (5 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 3) (j := 5) hlt
      (slo := (0 : ℚ)) (shi := ((1 : ℚ) / 4)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 6).1 (hdom 6).2
  have hzlo : ((zq 6 : ℝ)) ≤ zval y (3 : Fin 9) (5 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (3 : Fin 9) (5 : Fin 9) ≤ ((Zq 6 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : -(Real.pi / 2) ≤ (zq 6 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : -(Real.pi / 2) ≤ (zq 6 : ℝ) := by
      have hq : -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ (zq 6 : ℝ) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : -(Real.pi / 2) ≤ -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : -(Real.pi / 2) ≤ (zq 6 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 6 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := by
    have hnorm : (Zq 6 : ℝ) ≤ Real.pi / 2 := by
      have hq : (Zq 6 : ℝ) ≤ (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 6 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 6 : ℝ)) ((Zq 6 : ℝ)), Real.sin t ≤ ((sq 6 : ℝ) : ℝ) := by
    intro t ht
    have h1 : Real.sin t ≤ Real.sin ((Zq 6 : ℝ)) :=
      FlashCosine.sin_le_sin_of_mem_arc_inc (m := 0) (a := (zq 6 : ℝ)) (b := (Zq 6 : ℝ)) harc_lo' harc_hi' ht
    have h2 : Real.sin ((Zq 6 : ℝ)) ≤ ((N11Formalization.sinHiNLag ((Zq 6)) : ℚ) : ℝ) := by
      have hh := N11Formalization.sin_le_sinHiNLag (q := (Zq 6))
      have hc : (((Zq 6) : ℚ) : ℝ) = ((Zq 6 : ℝ)) := by norm_num
      linarith [hh, hc]
    have h3 : ((N11Formalization.sinHiNLag ((Zq 6)) : ℚ) : ℝ) ≤ ((sq 6 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 6 : ℝ)) ((Zq 6 : ℝ)),
      ((sq 6 : ℝ)) * z + ((cq 6 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_sin_le hsin ?_
    have h4 : ((cq 6 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((Zq 6)) : ℚ) : ℝ)
        - ((sq 6 : ℝ)) * ((Zq 6 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((Zq 6 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((Zq 6)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (Zq 6))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 6 : ℝ)) * ((zq 6 : ℝ)) + ((cq 6 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 6 : ℝ)) * ((Zq 6 : ℝ)) + ((cq 6 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 7: (i,j) = (3,7), shape b, arc dec, m = -1. -/
theorem pairCert_7 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 7 : ℝ)) ≤ zval y (3 : Fin 9) (7 : Fin 9) ∧
      zval y (3 : Fin 9) (7 : Fin 9) ≤ ((Zq 7 : ℝ)) ∧
      (((sq 7 : ℝ)) * zval y (3 : Fin 9) (7 : Fin 9) + ((cq 7 : ℝ))
        ≤ 1 - Real.cos (zval y (3 : Fin 9) (7 : Fin 9))) ∧
      0 ≤ ((sq 7 : ℝ)) * zval y (3 : Fin 9) (7 : Fin 9) + ((cq 7 : ℝ)) := by
  have hlt : (3 : ℕ) < (7 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 3) (j := 7) hlt
      (slo := ((1 : ℚ) / 2)) (shi := ((3 : ℚ) / 4)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 7).1 (hdom 7).2
  have hzlo : ((zq 7 : ℝ)) ≤ zval y (3 : Fin 9) (7 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (3 : Fin 9) (7 : Fin 9) ≤ ((Zq 7 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : Real.pi / 2 ≤ (zq 7 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : Real.pi / 2 ≤ (zq 7 : ℝ) + 2 * Real.pi := by
      have hq : (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 ≤ (zq 7 : ℝ) + 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : Real.pi / 2 ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.pi_lt_piHi
        linarith
      have h2 : 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) ≤ 2 * Real.pi := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : Real.pi / 2 ≤ (zq 7 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 7 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := by
    have hnorm : (Zq 7 : ℝ) + 2 * Real.pi ≤ 3 * Real.pi / 2 := by
      have hq : (Zq 7 : ℝ) + 2 * (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) ≤ 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ 3 * Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : Real.pi ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) := (N11Formalization.RatInterval.pi_lt_piHi).le
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 7 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 7 : ℝ)) ((Zq 7 : ℝ)), ((sq 7 : ℝ)) ≤ Real.sin t := by
    intro t ht
    have h1 : Real.sin ((Zq 7 : ℝ)) ≤ Real.sin t :=
      FlashCosine.arc_dec_le_sin (m := -1) (a := (zq 7 : ℝ)) (b := (Zq 7 : ℝ)) harc_lo' harc_hi' ht
    have h2 : ((N11Formalization.sinLoNLag ((Zq 7)) : ℚ) : ℝ) ≤ Real.sin ((Zq 7 : ℝ)) :=
      N11Formalization.sinLoNLag_le_sin (q := (Zq 7))
    have h3 : ((sq 7 : ℝ)) ≤ ((N11Formalization.sinLoNLag ((Zq 7)) : ℚ) : ℝ) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 7 : ℝ)) ((Zq 7 : ℝ)),
      ((sq 7 : ℝ)) * z + ((cq 7 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_le_sin hsin ?_
    have h4 : ((cq 7 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((zq 7)) : ℚ) : ℝ)
        - ((sq 7 : ℝ)) * ((zq 7 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((zq 7 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((zq 7)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (zq 7))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 7 : ℝ)) * ((zq 7 : ℝ)) + ((cq 7 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 7 : ℝ)) * ((Zq 7 : ℝ)) + ((cq 7 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 8: (i,j) = (3,8), shape b, arc dec, m = -1. -/
theorem pairCert_8 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 8 : ℝ)) ≤ zval y (3 : Fin 9) (8 : Fin 9) ∧
      zval y (3 : Fin 9) (8 : Fin 9) ≤ ((Zq 8 : ℝ)) ∧
      (((sq 8 : ℝ)) * zval y (3 : Fin 9) (8 : Fin 9) + ((cq 8 : ℝ))
        ≤ 1 - Real.cos (zval y (3 : Fin 9) (8 : Fin 9))) ∧
      0 ≤ ((sq 8 : ℝ)) * zval y (3 : Fin 9) (8 : Fin 9) + ((cq 8 : ℝ)) := by
  have hlt : (3 : ℕ) < (8 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 3) (j := 8) hlt
      (slo := ((1 : ℚ) / 2)) (shi := ((3 : ℚ) / 4)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 8).1 (hdom 8).2
  have hzlo : ((zq 8 : ℝ)) ≤ zval y (3 : Fin 9) (8 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (3 : Fin 9) (8 : Fin 9) ≤ ((Zq 8 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : Real.pi / 2 ≤ (zq 8 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : Real.pi / 2 ≤ (zq 8 : ℝ) + 2 * Real.pi := by
      have hq : (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 ≤ (zq 8 : ℝ) + 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : Real.pi / 2 ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.pi_lt_piHi
        linarith
      have h2 : 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) ≤ 2 * Real.pi := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : Real.pi / 2 ≤ (zq 8 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 8 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := by
    have hnorm : (Zq 8 : ℝ) + 2 * Real.pi ≤ 3 * Real.pi / 2 := by
      have hq : (Zq 8 : ℝ) + 2 * (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) ≤ 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ 3 * Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : Real.pi ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) := (N11Formalization.RatInterval.pi_lt_piHi).le
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 8 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 8 : ℝ)) ((Zq 8 : ℝ)), ((sq 8 : ℝ)) ≤ Real.sin t := by
    intro t ht
    have h1 : Real.sin ((Zq 8 : ℝ)) ≤ Real.sin t :=
      FlashCosine.arc_dec_le_sin (m := -1) (a := (zq 8 : ℝ)) (b := (Zq 8 : ℝ)) harc_lo' harc_hi' ht
    have h2 : ((N11Formalization.sinLoNLag ((Zq 8)) : ℚ) : ℝ) ≤ Real.sin ((Zq 8 : ℝ)) :=
      N11Formalization.sinLoNLag_le_sin (q := (Zq 8))
    have h3 : ((sq 8 : ℝ)) ≤ ((N11Formalization.sinLoNLag ((Zq 8)) : ℚ) : ℝ) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 8 : ℝ)) ((Zq 8 : ℝ)),
      ((sq 8 : ℝ)) * z + ((cq 8 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_le_sin hsin ?_
    have h4 : ((cq 8 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((zq 8)) : ℚ) : ℝ)
        - ((sq 8 : ℝ)) * ((zq 8 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((zq 8 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((zq 8)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (zq 8))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 8 : ℝ)) * ((zq 8 : ℝ)) + ((cq 8 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 8 : ℝ)) * ((Zq 8 : ℝ)) + ((cq 8 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 9: (i,j) = (4,5), shape a, arc inc, m = 0. -/
theorem pairCert_9 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 9 : ℝ)) ≤ zval y (4 : Fin 9) (5 : Fin 9) ∧
      zval y (4 : Fin 9) (5 : Fin 9) ≤ ((Zq 9 : ℝ)) ∧
      (((sq 9 : ℝ)) * zval y (4 : Fin 9) (5 : Fin 9) + ((cq 9 : ℝ))
        ≤ 1 - Real.cos (zval y (4 : Fin 9) (5 : Fin 9))) ∧
      0 ≤ ((sq 9 : ℝ)) * zval y (4 : Fin 9) (5 : Fin 9) + ((cq 9 : ℝ)) := by
  have hlt : (4 : ℕ) < (5 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 4) (j := 5) hlt
      (slo := (0 : ℚ)) (shi := ((1 : ℚ) / 4)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 9).1 (hdom 9).2
  have hzlo : ((zq 9 : ℝ)) ≤ zval y (4 : Fin 9) (5 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (4 : Fin 9) (5 : Fin 9) ≤ ((Zq 9 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : -(Real.pi / 2) ≤ (zq 9 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : -(Real.pi / 2) ≤ (zq 9 : ℝ) := by
      have hq : -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ (zq 9 : ℝ) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : -(Real.pi / 2) ≤ -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : -(Real.pi / 2) ≤ (zq 9 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 9 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := by
    have hnorm : (Zq 9 : ℝ) ≤ Real.pi / 2 := by
      have hq : (Zq 9 : ℝ) ≤ (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 9 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 9 : ℝ)) ((Zq 9 : ℝ)), Real.sin t ≤ ((sq 9 : ℝ) : ℝ) := by
    intro t ht
    have h1 : Real.sin t ≤ Real.sin ((Zq 9 : ℝ)) :=
      FlashCosine.sin_le_sin_of_mem_arc_inc (m := 0) (a := (zq 9 : ℝ)) (b := (Zq 9 : ℝ)) harc_lo' harc_hi' ht
    have h2 : Real.sin ((Zq 9 : ℝ)) ≤ ((N11Formalization.sinHiNLag ((Zq 9)) : ℚ) : ℝ) := by
      have hh := N11Formalization.sin_le_sinHiNLag (q := (Zq 9))
      have hc : (((Zq 9) : ℚ) : ℝ) = ((Zq 9 : ℝ)) := by norm_num
      linarith [hh, hc]
    have h3 : ((N11Formalization.sinHiNLag ((Zq 9)) : ℚ) : ℝ) ≤ ((sq 9 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 9 : ℝ)) ((Zq 9 : ℝ)),
      ((sq 9 : ℝ)) * z + ((cq 9 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_sin_le hsin ?_
    have h4 : ((cq 9 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((Zq 9)) : ℚ) : ℝ)
        - ((sq 9 : ℝ)) * ((Zq 9 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((Zq 9 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((Zq 9)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (Zq 9))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 9 : ℝ)) * ((zq 9 : ℝ)) + ((cq 9 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 9 : ℝ)) * ((Zq 9 : ℝ)) + ((cq 9 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 10: (i,j) = (4,7), shape a, arc dec, m = -1. -/
theorem pairCert_10 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 10 : ℝ)) ≤ zval y (4 : Fin 9) (7 : Fin 9) ∧
      zval y (4 : Fin 9) (7 : Fin 9) ≤ ((Zq 10 : ℝ)) ∧
      (((sq 10 : ℝ)) * zval y (4 : Fin 9) (7 : Fin 9) + ((cq 10 : ℝ))
        ≤ 1 - Real.cos (zval y (4 : Fin 9) (7 : Fin 9))) ∧
      0 ≤ ((sq 10 : ℝ)) * zval y (4 : Fin 9) (7 : Fin 9) + ((cq 10 : ℝ)) := by
  have hlt : (4 : ℕ) < (7 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 4) (j := 7) hlt
      (slo := ((1 : ℚ) / 4)) (shi := ((1 : ℚ) / 2)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 10).1 (hdom 10).2
  have hzlo : ((zq 10 : ℝ)) ≤ zval y (4 : Fin 9) (7 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (4 : Fin 9) (7 : Fin 9) ≤ ((Zq 10 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : Real.pi / 2 ≤ (zq 10 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : Real.pi / 2 ≤ (zq 10 : ℝ) + 2 * Real.pi := by
      have hq : (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 ≤ (zq 10 : ℝ) + 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : Real.pi / 2 ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.pi_lt_piHi
        linarith
      have h2 : 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) ≤ 2 * Real.pi := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : Real.pi / 2 ≤ (zq 10 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 10 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := by
    have hnorm : (Zq 10 : ℝ) + 2 * Real.pi ≤ 3 * Real.pi / 2 := by
      have hq : (Zq 10 : ℝ) + 2 * (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) ≤ 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ 3 * Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : Real.pi ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) := (N11Formalization.RatInterval.pi_lt_piHi).le
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 10 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 10 : ℝ)) ((Zq 10 : ℝ)), Real.sin t ≤ ((sq 10 : ℝ) : ℝ) := by
    intro t ht
    have h1 : Real.sin t ≤ Real.sin ((zq 10 : ℝ)) :=
      FlashCosine.sin_le_sin_of_mem_arc_dec (m := -1) (a := (zq 10 : ℝ)) (b := (Zq 10 : ℝ)) harc_lo' harc_hi' ht
    have h2 : Real.sin ((zq 10 : ℝ)) ≤ ((N11Formalization.sinHiNLag ((zq 10)) : ℚ) : ℝ) := by
      have hh := N11Formalization.sin_le_sinHiNLag (q := (zq 10))
      have hc : (((zq 10) : ℚ) : ℝ) = ((zq 10 : ℝ)) := by norm_num
      linarith [hh, hc]
    have h3 : ((N11Formalization.sinHiNLag ((zq 10)) : ℚ) : ℝ) ≤ ((sq 10 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 10 : ℝ)) ((Zq 10 : ℝ)),
      ((sq 10 : ℝ)) * z + ((cq 10 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_sin_le hsin ?_
    have h4 : ((cq 10 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((Zq 10)) : ℚ) : ℝ)
        - ((sq 10 : ℝ)) * ((Zq 10 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((Zq 10 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((Zq 10)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (Zq 10))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 10 : ℝ)) * ((zq 10 : ℝ)) + ((cq 10 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 10 : ℝ)) * ((Zq 10 : ℝ)) + ((cq 10 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 11: (i,j) = (4,8), shape b, arc dec, m = -1. -/
theorem pairCert_11 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 11 : ℝ)) ≤ zval y (4 : Fin 9) (8 : Fin 9) ∧
      zval y (4 : Fin 9) (8 : Fin 9) ≤ ((Zq 11 : ℝ)) ∧
      (((sq 11 : ℝ)) * zval y (4 : Fin 9) (8 : Fin 9) + ((cq 11 : ℝ))
        ≤ 1 - Real.cos (zval y (4 : Fin 9) (8 : Fin 9))) ∧
      0 ≤ ((sq 11 : ℝ)) * zval y (4 : Fin 9) (8 : Fin 9) + ((cq 11 : ℝ)) := by
  have hlt : (4 : ℕ) < (8 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 4) (j := 8) hlt
      (slo := ((1 : ℚ) / 4)) (shi := ((1 : ℚ) / 2)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 11).1 (hdom 11).2
  have hzlo : ((zq 11 : ℝ)) ≤ zval y (4 : Fin 9) (8 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (4 : Fin 9) (8 : Fin 9) ≤ ((Zq 11 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : Real.pi / 2 ≤ (zq 11 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : Real.pi / 2 ≤ (zq 11 : ℝ) + 2 * Real.pi := by
      have hq : (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 ≤ (zq 11 : ℝ) + 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : Real.pi / 2 ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.pi_lt_piHi
        linarith
      have h2 : 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) ≤ 2 * Real.pi := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : Real.pi / 2 ≤ (zq 11 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 11 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := by
    have hnorm : (Zq 11 : ℝ) + 2 * Real.pi ≤ 3 * Real.pi / 2 := by
      have hq : (Zq 11 : ℝ) + 2 * (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) ≤ 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ 3 * Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : Real.pi ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) := (N11Formalization.RatInterval.pi_lt_piHi).le
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 11 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 11 : ℝ)) ((Zq 11 : ℝ)), ((sq 11 : ℝ)) ≤ Real.sin t := by
    intro t ht
    have h1 : Real.sin ((Zq 11 : ℝ)) ≤ Real.sin t :=
      FlashCosine.arc_dec_le_sin (m := -1) (a := (zq 11 : ℝ)) (b := (Zq 11 : ℝ)) harc_lo' harc_hi' ht
    have h2 : ((N11Formalization.sinLoNLag ((Zq 11)) : ℚ) : ℝ) ≤ Real.sin ((Zq 11 : ℝ)) :=
      N11Formalization.sinLoNLag_le_sin (q := (Zq 11))
    have h3 : ((sq 11 : ℝ)) ≤ ((N11Formalization.sinLoNLag ((Zq 11)) : ℚ) : ℝ) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 11 : ℝ)) ((Zq 11 : ℝ)),
      ((sq 11 : ℝ)) * z + ((cq 11 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_le_sin hsin ?_
    have h4 : ((cq 11 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((zq 11)) : ℚ) : ℝ)
        - ((sq 11 : ℝ)) * ((zq 11 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((zq 11 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((zq 11)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (zq 11))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 11 : ℝ)) * ((zq 11 : ℝ)) + ((cq 11 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 11 : ℝ)) * ((Zq 11 : ℝ)) + ((cq 11 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 12: (i,j) = (5,7), shape b, arc inc, m = 0. -/
theorem pairCert_12 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 12 : ℝ)) ≤ zval y (5 : Fin 9) (7 : Fin 9) ∧
      zval y (5 : Fin 9) (7 : Fin 9) ≤ ((Zq 12 : ℝ)) ∧
      (((sq 12 : ℝ)) * zval y (5 : Fin 9) (7 : Fin 9) + ((cq 12 : ℝ))
        ≤ 1 - Real.cos (zval y (5 : Fin 9) (7 : Fin 9))) ∧
      0 ≤ ((sq 12 : ℝ)) * zval y (5 : Fin 9) (7 : Fin 9) + ((cq 12 : ℝ)) := by
  have hlt : (5 : ℕ) < (7 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 5) (j := 7) hlt
      (slo := ((1 : ℚ) / 4)) (shi := ((1 : ℚ) / 2)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 12).1 (hdom 12).2
  have hzlo : ((zq 12 : ℝ)) ≤ zval y (5 : Fin 9) (7 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (5 : Fin 9) (7 : Fin 9) ≤ ((Zq 12 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : -(Real.pi / 2) ≤ (zq 12 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : -(Real.pi / 2) ≤ (zq 12 : ℝ) := by
      have hq : -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ (zq 12 : ℝ) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : -(Real.pi / 2) ≤ -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : -(Real.pi / 2) ≤ (zq 12 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 12 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := by
    have hnorm : (Zq 12 : ℝ) ≤ Real.pi / 2 := by
      have hq : (Zq 12 : ℝ) ≤ (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 12 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 12 : ℝ)) ((Zq 12 : ℝ)), ((sq 12 : ℝ)) ≤ Real.sin t := by
    intro t ht
    have h1 : Real.sin ((zq 12 : ℝ)) ≤ Real.sin t :=
      FlashCosine.arc_inc_le_sin (m := 0) (a := (zq 12 : ℝ)) (b := (Zq 12 : ℝ)) harc_lo' harc_hi' ht
    have h2 : ((N11Formalization.sinLoNLag ((zq 12)) : ℚ) : ℝ) ≤ Real.sin ((zq 12 : ℝ)) :=
      N11Formalization.sinLoNLag_le_sin (q := (zq 12))
    have h3 : ((sq 12 : ℝ)) ≤ ((N11Formalization.sinLoNLag ((zq 12)) : ℚ) : ℝ) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 12 : ℝ)) ((Zq 12 : ℝ)),
      ((sq 12 : ℝ)) * z + ((cq 12 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_le_sin hsin ?_
    have h4 : ((cq 12 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((zq 12)) : ℚ) : ℝ)
        - ((sq 12 : ℝ)) * ((zq 12 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((zq 12 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((zq 12)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (zq 12))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 12 : ℝ)) * ((zq 12 : ℝ)) + ((cq 12 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 12 : ℝ)) * ((Zq 12 : ℝ)) + ((cq 12 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 13: (i,j) = (5,8), shape b, arc dec, m = -1. -/
theorem pairCert_13 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 13 : ℝ)) ≤ zval y (5 : Fin 9) (8 : Fin 9) ∧
      zval y (5 : Fin 9) (8 : Fin 9) ≤ ((Zq 13 : ℝ)) ∧
      (((sq 13 : ℝ)) * zval y (5 : Fin 9) (8 : Fin 9) + ((cq 13 : ℝ))
        ≤ 1 - Real.cos (zval y (5 : Fin 9) (8 : Fin 9))) ∧
      0 ≤ ((sq 13 : ℝ)) * zval y (5 : Fin 9) (8 : Fin 9) + ((cq 13 : ℝ)) := by
  have hlt : (5 : ℕ) < (8 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 5) (j := 8) hlt
      (slo := ((1 : ℚ) / 4)) (shi := ((1 : ℚ) / 2)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 13).1 (hdom 13).2
  have hzlo : ((zq 13 : ℝ)) ≤ zval y (5 : Fin 9) (8 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (5 : Fin 9) (8 : Fin 9) ≤ ((Zq 13 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : Real.pi / 2 ≤ (zq 13 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : Real.pi / 2 ≤ (zq 13 : ℝ) + 2 * Real.pi := by
      have hq : (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 ≤ (zq 13 : ℝ) + 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : Real.pi / 2 ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.pi_lt_piHi
        linarith
      have h2 : 2 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) ≤ 2 * Real.pi := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : Real.pi / 2 ≤ (zq 13 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 13 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := by
    have hnorm : (Zq 13 : ℝ) + 2 * Real.pi ≤ 3 * Real.pi / 2 := by
      have hq : (Zq 13 : ℝ) + 2 * (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) ≤ 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : 3 * (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ 3 * Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      have h2 : Real.pi ≤ (((N11Formalization.RatInterval.piHi : ℚ) : ℝ)) := (N11Formalization.RatInterval.pi_lt_piHi).le
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 13 : ℝ) - ((-1 : ℤ) : ℝ) * (2 * Real.pi) ≤ 3 * Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 13 : ℝ)) ((Zq 13 : ℝ)), ((sq 13 : ℝ)) ≤ Real.sin t := by
    intro t ht
    have h1 : Real.sin ((Zq 13 : ℝ)) ≤ Real.sin t :=
      FlashCosine.arc_dec_le_sin (m := -1) (a := (zq 13 : ℝ)) (b := (Zq 13 : ℝ)) harc_lo' harc_hi' ht
    have h2 : ((N11Formalization.sinLoNLag ((Zq 13)) : ℚ) : ℝ) ≤ Real.sin ((Zq 13 : ℝ)) :=
      N11Formalization.sinLoNLag_le_sin (q := (Zq 13))
    have h3 : ((sq 13 : ℝ)) ≤ ((N11Formalization.sinLoNLag ((Zq 13)) : ℚ) : ℝ) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 13 : ℝ)) ((Zq 13 : ℝ)),
      ((sq 13 : ℝ)) * z + ((cq 13 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_le_sin hsin ?_
    have h4 : ((cq 13 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((zq 13)) : ℚ) : ℝ)
        - ((sq 13 : ℝ)) * ((zq 13 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((zq 13 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((zq 13)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (zq 13))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 13 : ℝ)) * ((zq 13 : ℝ)) + ((cq 13 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 13 : ℝ)) * ((Zq 13 : ℝ)) + ((cq 13 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩


set_option maxHeartbeats 4000000 in
/-- pair 14: (i,j) = (7,8), shape a, arc inc, m = 0. -/
theorem pairCert_14 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ((zq 14 : ℝ)) ≤ zval y (7 : Fin 9) (8 : Fin 9) ∧
      zval y (7 : Fin 9) (8 : Fin 9) ≤ ((Zq 14 : ℝ)) ∧
      (((sq 14 : ℝ)) * zval y (7 : Fin 9) (8 : Fin 9) + ((cq 14 : ℝ))
        ≤ 1 - Real.cos (zval y (7 : Fin 9) (8 : Fin 9))) ∧
      0 ≤ ((sq 14 : ℝ)) * zval y (7 : Fin 9) (8 : Fin 9) + ((cq 14 : ℝ)) := by
  have hlt : (7 : ℕ) < (8 : ℕ) := by norm_num
  have hcell := cell_bound (L := Lc) (D := Dc) (i := 7) (j := 8) hlt
      (slo := (0 : ℚ)) (shi := ((1 : ℚ) / 4)) (by norm_num)
      L_mem.1 L_mem.2 D_mem.1 D_mem.2 (hdom 14).1 (hdom 14).2
  have hzlo : ((zq 14 : ℝ)) ≤ zval y (7 : Fin 9) (8 : Fin 9) := by
    rw [zval_eq]
    refine le_trans ?_ hcell.1
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have hzhi : zval y (7 : Fin 9) (8 : Fin 9) ≤ ((Zq 14 : ℝ)) := by
    rw [zval_eq]
    refine le_trans hcell.2 ?_
    push_cast
    norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
  have harc_lo : -(Real.pi / 2) ≤ (zq 14 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := by
    have hnorm : -(Real.pi / 2) ≤ (zq 14 : ℝ) := by
      have hq : -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ (zq 14 : ℝ) := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : -(Real.pi / 2) ≤ -(((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_lo' : -(Real.pi / 2) ≤ (zq 14 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) := harc_lo
  have harc_hi : (Zq 14 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := by
    have hnorm : (Zq 14 : ℝ) ≤ Real.pi / 2 := by
      have hq : (Zq 14 : ℝ) ≤ (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 := by norm_num [LQ, Lq, Dq, DQ, zq, Zq, sq, cq, N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi]
      have h1 : (((N11Formalization.RatInterval.piLo : ℚ) : ℝ)) / 2 ≤ Real.pi / 2 := by
        have := N11Formalization.RatInterval.piLo_lt_pi
        linarith
      linarith
    convert hnorm using 1 <;> ring
  have harc_hi' : (Zq 14 : ℝ) - ((0 : ℤ) : ℝ) * (2 * Real.pi) ≤ Real.pi / 2 := harc_hi

  have hsin : ∀ t ∈ Set.Icc ((zq 14 : ℝ)) ((Zq 14 : ℝ)), Real.sin t ≤ ((sq 14 : ℝ) : ℝ) := by
    intro t ht
    have h1 : Real.sin t ≤ Real.sin ((Zq 14 : ℝ)) :=
      FlashCosine.sin_le_sin_of_mem_arc_inc (m := 0) (a := (zq 14 : ℝ)) (b := (Zq 14 : ℝ)) harc_lo' harc_hi' ht
    have h2 : Real.sin ((Zq 14 : ℝ)) ≤ ((N11Formalization.sinHiNLag ((Zq 14)) : ℚ) : ℝ) := by
      have hh := N11Formalization.sin_le_sinHiNLag (q := (Zq 14))
      have hc : (((Zq 14) : ℚ) : ℝ) = ((Zq 14 : ℝ)) := by norm_num
      linarith [hh, hc]
    have h3 : ((N11Formalization.sinHiNLag ((Zq 14)) : ℚ) : ℝ) ≤ ((sq 14 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    linarith
  have hmin : ∀ z ∈ Set.Icc ((zq 14 : ℝ)) ((Zq 14 : ℝ)),
      ((sq 14 : ℝ)) * z + ((cq 14 : ℝ)) ≤ 1 - Real.cos z := by
    refine FlashCosine.minorant_of_sin_le hsin ?_
    have h4 : ((cq 14 : ℝ)) ≤ 1 - ((N11Formalization.cosHiNLag ((Zq 14)) : ℚ) : ℝ)
        - ((sq 14 : ℝ)) * ((Zq 14 : ℝ)) := by
      norm_num [N11Formalization.sinHiNLag, N11Formalization.sinLoNLag, N11Formalization.sinTQ, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ, zq, Zq, sq, cq]
    have h5 : Real.cos ((Zq 14 : ℝ)) ≤ ((N11Formalization.cosHiNLag ((Zq 14)) : ℚ) : ℝ) :=
      N11Formalization.cos_le_cosHiNLag (q := (Zq 14))
    linarith
  have hn1 : (0 : ℝ) ≤ ((sq 14 : ℝ)) * ((zq 14 : ℝ)) + ((cq 14 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  have hn2 : (0 : ℝ) ≤ ((sq 14 : ℝ)) * ((Zq 14 : ℝ)) + ((cq 14 : ℝ)) := by norm_num [zq, Zq, sq, cq]
  exact ⟨hzlo, hzhi, hmin _ ⟨hzlo, hzhi⟩,
    FlashCosine.affine_nonneg_of_endpoints ⟨hzlo, hzhi⟩ hn1 hn2⟩

/-! ## 5. Assembly, stage 1: weight brackets + per-pair packaging + termwise reduction -/

/-- 15 个认证对的 (i,j) 严格递增（Fin 级判定）。 -/
theorem pair_lt : ∀ k : Fin 15, (iOf k : ℕ) < (jOf k : ℕ) := by decide

/-- 认证对的映射单射。 -/
theorem pair_inj : Function.Injective (fun k : Fin 15 => ((iOf k, jOf k) : Fin 9 × Fin 9)) := by decide

/-- 15 个认证对的配对集合。 -/
def S15 : Finset (Fin 9 × Fin 9) := Finset.univ.image (fun k : Fin 15 => (iOf k, jOf k))

theorem S15_fst_lt_snd : ∀ p ∈ S15, p.1 < p.2 := by
  intro p hp
  simp only [S15, Finset.mem_image, Finset.mem_univ, true_and] at hp
  rcases hp with ⟨k, rfl⟩
  exact pair_lt k

/-- `wlo k ≥ 0`（字面量）。 -/
theorem wlo_nonneg : ∀ k : Fin 15, (0 : ℚ) ≤ wlo k := by
  intro k
  fin_cases k <;> norm_num [wlo]


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_0 : (wlo 0 : ℝ) ≤ 2 * weight (0 : Fin 9) (3 : Fin 9) := by
  rw [weight2_cast (0 : Fin 9) (3 : Fin 9)]
  have h : (((1574948903583 : ℚ) / 250000000000000)) ≤ 2 * (wNum (0 : Fin 9) (3 : Fin 9) / wDen (0 : Fin 9) (3 : Fin 9)) := by
    show (((1574948903583 : ℚ) / 250000000000000)) ≤ 2 * ((6638653561014141824837956341985311233388260207303675447944505882806685 : ℚ) / (2107577441373077336969241691125533053864294005132744084669419950952307822 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_1 : (wlo 1 : ℝ) ≤ 2 * weight (0 : Fin 9) (4 : Fin 9) := by
  rw [weight2_cast (0 : Fin 9) (4 : Fin 9)]
  have h : (((425349101103 : ℚ) / 62500000000000)) ≤ 2 * (wNum (0 : Fin 9) (4 : Fin 9) / wDen (0 : Fin 9) (4 : Fin 9)) := by
    show (((425349101103 : ℚ) / 62500000000000)) ≤ 2 * ((7171649361544975819854460383615573706647112730617686816183433963167229 : ℚ) / (2107577441373077336969241691125533053864294005132744084669419950952307822 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_2 : (wlo 2 : ℝ) ≤ 2 * weight (0 : Fin 9) (5 : Fin 9) := by
  rw [weight2_cast (0 : Fin 9) (5 : Fin 9)]
  have h : (((4483646868437 : ℚ) / 1000000000000000)) ≤ 2 * (wNum (0 : Fin 9) (5 : Fin 9) / wDen (0 : Fin 9) (5 : Fin 9)) := by
    show (((4483646868437 : ℚ) / 1000000000000000)) ≤ 2 * ((429528772500084301462514971048710972396630959807950849899375735089501 : ℚ) / (191597949215734303360840153738684823078572182284794916788129086450209802 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_3 : (wlo 3 : ℝ) ≤ 2 * weight (0 : Fin 9) (7 : Fin 9) := by
  rw [weight2_cast (0 : Fin 9) (7 : Fin 9)]
  have h : (((11978106160769 : ℚ) / 1000000000000000)) ≤ 2 * (wNum (0 : Fin 9) (7 : Fin 9) / wDen (0 : Fin 9) (7 : Fin 9)) := by
    show (((11978106160769 : ℚ) / 1000000000000000)) ≤ 2 * ((573745143972926511174913260346864040791527129520042087457827687727794 : ℚ) / (95798974607867151680420076869342411539286091142397458394064543225104901 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_4 : (wlo 4 : ℝ) ≤ 2 * weight (0 : Fin 9) (8 : Fin 9) := by
  rw [weight2_cast (0 : Fin 9) (8 : Fin 9)]
  have h : (((31052389696227 : ℚ) / 500000000000000)) ≤ 2 * (wNum (0 : Fin 9) (8 : Fin 9) / wDen (0 : Fin 9) (8 : Fin 9)) := by
    show (((31052389696227 : ℚ) / 500000000000000)) ≤ 2 * ((32722658012247048569447401177352675763131850174581214462271668140481493 : ℚ) / (1053788720686538668484620845562766526932147002566372042334709975476153911 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_5 : (wlo 5 : ℝ) ≤ 2 * weight (3 : Fin 9) (4 : Fin 9) := by
  rw [weight2_cast (3 : Fin 9) (4 : Fin 9)]
  have h : (((14349213499701 : ℚ) / 250000000000000)) ≤ 2 * (wNum (3 : Fin 9) (4 : Fin 9) / wDen (3 : Fin 9) (4 : Fin 9)) := by
    show (((14349213499701 : ℚ) / 250000000000000)) ≤ 2 * ((30242078673416318805158785042749779340797942616647484249045254471949889 : ℚ) / (1053788720686538668484620845562766526932147002566372042334709975476153911 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_6 : (wlo 6 : ℝ) ≤ 2 * weight (3 : Fin 9) (5 : Fin 9) := by
  rw [weight2_cast (3 : Fin 9) (5 : Fin 9)]
  have h : (((11677961094779 : ℚ) / 1000000000000000)) ≤ 2 * (wNum (3 : Fin 9) (5 : Fin 9) / wDen (3 : Fin 9) (5 : Fin 9)) := by
    show (((11677961094779 : ℚ) / 1000000000000000)) ≤ 2 * ((559368349195230853268199515599068817475534626144717592161360547229446 : ℚ) / (95798974607867151680420076869342411539286091142397458394064543225104901 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_7 : (wlo 7 : ℝ) ≤ 2 * weight (3 : Fin 9) (7 : Fin 9) := by
  rw [weight2_cast (3 : Fin 9) (7 : Fin 9)]
  have h : (((4421568400769 : ℚ) / 1000000000000000)) ≤ 2 * (wNum (3 : Fin 9) (7 : Fin 9) / wDen (3 : Fin 9) (7 : Fin 9)) := by
    show (((4421568400769 : ℚ) / 1000000000000000)) ≤ 2 * ((211790859476115615767910749293241516798538213840143400957642569376410 : ℚ) / (95798974607867151680420076869342411539286091142397458394064543225104901 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_8 : (wlo 8 : ℝ) ≤ 2 * weight (3 : Fin 9) (8 : Fin 9) := by
  rw [weight2_cast (3 : Fin 9) (8 : Fin 9)]
  have h : (((1708494742773 : ℚ) / 250000000000000)) ≤ 2 * (wNum (3 : Fin 9) (8 : Fin 9) / wDen (3 : Fin 9) (8 : Fin 9)) := by
    show (((1708494742773 : ℚ) / 250000000000000)) ≤ 2 * ((3600784978572901076831650505973621001302527340782257706863452931043624 : ℚ) / (1053788720686538668484620845562766526932147002566372042334709975476153911 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_9 : (wlo 9 : ℝ) ≤ 2 * weight (4 : Fin 9) (5 : Fin 9) := by
  rw [weight2_cast (4 : Fin 9) (5 : Fin 9)]
  have h : (((48015899351253 : ℚ) / 1000000000000000)) ≤ 2 * (wNum (4 : Fin 9) (5 : Fin 9) / wDen (4 : Fin 9) (5 : Fin 9)) := by
    show (((48015899351253 : ℚ) / 1000000000000000)) ≤ 2 * ((4599873922724649126803381436082844391022730295513099491630775245941121 : ℚ) / (191597949215734303360840153738684823078572182284794916788129086450209802 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_10 : (wlo 10 : ℝ) ≤ 2 * weight (4 : Fin 9) (7 : Fin 9) := by
  rw [weight2_cast (4 : Fin 9) (7 : Fin 9)]
  have h : (((238828088513 : ℚ) / 50000000000000)) ≤ 2 * (wNum (4 : Fin 9) (7 : Fin 9) / wDen (4 : Fin 9) (7 : Fin 9)) := by
    show (((238828088513 : ℚ) / 50000000000000)) ≤ 2 * ((228794859871055220915044215840775747863328424776881223977396722073312 : ℚ) / (95798974607867151680420076869342411539286091142397458394064543225104901 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_11 : (wlo 11 : ℝ) ≤ 2 * weight (4 : Fin 9) (8 : Fin 9) := by
  rw [weight2_cast (4 : Fin 9) (8 : Fin 9)]
  have h : (((184566422579 : ℚ) / 25000000000000)) ≤ 2 * (wNum (4 : Fin 9) (8 : Fin 9) / wDen (4 : Fin 9) (8 : Fin 9)) := by
    show (((184566422579 : ℚ) / 25000000000000)) ≤ 2 * ((3889880286624829997415200808405123872835017736057322876709350169094661 : ℚ) / (1053788720686538668484620845562766526932147002566372042334709975476153911 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_12 : (wlo 12 : ℝ) ≤ 2 * weight (5 : Fin 9) (7 : Fin 9) := by
  rw [weight2_cast (5 : Fin 9) (7 : Fin 9)]
  have h : (((125875526881 : ℚ) / 40000000000000)) ≤ 2 * (wNum (5 : Fin 9) (7 : Fin 9) / wDen (5 : Fin 9) (7 : Fin 9)) := by
    show (((125875526881 : ℚ) / 40000000000000)) ≤ 2 * ((150734330042818252904486948916117503237189876415913140151870259597338 : ℚ) / (95798974607867151680420076869342411539286091142397458394064543225104901 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_13 : (wlo 13 : ℝ) ≤ 2 * weight (5 : Fin 9) (8 : Fin 9) := by
  rw [weight2_cast (5 : Fin 9) (8 : Fin 9)]
  have h : (((2431916118209 : ℚ) / 500000000000000)) ≤ 2 * (wNum (5 : Fin 9) (8 : Fin 9) / wDen (5 : Fin 9) (8 : Fin 9)) := by
    show (((2431916118209 : ℚ) / 500000000000000)) ≤ 2 * ((232975070456777944392758797552429608806894560044258686319806725974905 : ℚ) / (95798974607867151680420076869342411539286091142397458394064543225104901 : ℚ))
    norm_num
  exact_mod_cast h


set_option maxHeartbeats 1000000 in
/-- 权重下界：`wlo k ≤ 2 * weight i j`（精确有理，`show` 字面化后 `norm_num`）。 -/
theorem wbracket_14 : (wlo 14 : ℝ) ≤ 2 * weight (7 : Fin 9) (8 : Fin 9) := by
  rw [weight2_cast (7 : Fin 9) (8 : Fin 9)]
  have h : (((49289522253343 : ℚ) / 1000000000000000)) ≤ 2 * (wNum (7 : Fin 9) (8 : Fin 9) / wDen (7 : Fin 9) (8 : Fin 9)) := by
    show (((49289522253343 : ℚ) / 1000000000000000)) ≤ 2 * ((2360942845390959601255649183804403339506244159226858189253563478182961 : ℚ) / (95798974607867151680420076869342411539286091142397458394064543225104901 : ℚ))
    norm_num
  exact_mod_cast h


/-- 逐对权重下界（作为 `Fin 15` 上的函数）。 -/
theorem wbracket : ∀ k : Fin 15, (wlo k : ℝ) ≤ 2 * weight (iOf k) (jOf k) := by
  intro k
  fin_cases k <;>
    first
      | exact wbracket_0
      | exact wbracket_1
      | exact wbracket_2
      | exact wbracket_3
      | exact wbracket_4
      | exact wbracket_5
      | exact wbracket_6
      | exact wbracket_7
      | exact wbracket_8
      | exact wbracket_9
      | exact wbracket_10
      | exact wbracket_11
      | exact wbracket_12
      | exact wbracket_13
      | exact wbracket_14

/-- 15 对证书打包（逐对取自 `pairCert_k`）。 -/
theorem pairFacts (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    ∀ k : Fin 15,
      (zq k : ℝ) ≤ zval y (iOf k) (jOf k) ∧ zval y (iOf k) (jOf k) ≤ (Zq k : ℝ) ∧
      ((sq k : ℝ) * zval y (iOf k) (jOf k) + (cq k : ℝ) ≤ 1 - Real.cos (zval y (iOf k) (jOf k))) ∧
      0 ≤ (sq k : ℝ) * zval y (iOf k) (jOf k) + (cq k : ℝ) := by
  intro k
  fin_cases k <;>
    first
      | exact pairCert_0 y hy0 hdom
      | exact pairCert_1 y hy0 hdom
      | exact pairCert_2 y hy0 hdom
      | exact pairCert_3 y hy0 hdom
      | exact pairCert_4 y hy0 hdom
      | exact pairCert_5 y hy0 hdom
      | exact pairCert_6 y hy0 hdom
      | exact pairCert_7 y hy0 hdom
      | exact pairCert_8 y hy0 hdom
      | exact pairCert_9 y hy0 hdom
      | exact pairCert_10 y hy0 hdom
      | exact pairCert_11 y hy0 hdom
      | exact pairCert_12 y hy0 hdom
      | exact pairCert_13 y hy0 hdom
      | exact pairCert_14 y hy0 hdom

/-- **stage 1**: 15 对加权 affine 和 ≤ 全 36 对 cosine 能量（乘 2 口径）。 -/
theorem stage1 (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q)
    (hdom : ∀ k : Fin 15, (sloB k : ℝ) ≤ tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ∧
        tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k)) ≤ (shiB k : ℝ)) :
    (∑ k : Fin 15, (wlo k : ℝ) * ((sq k : ℝ) * zval y (iOf k) (jOf k) + (cq k : ℝ)))
      ≤ 2 * ∑ i, ∑ j, if i < j then weight i j * (1 - Real.cos (zval y i j)) else 0 := by
  have hfacts := pairFacts y hy0 hdom
  have hw := wbracket
  -- termwise: wlo_k * affine_k ≤ (2 weight_k) * (1 - cos z_k)
  have hterm : ∀ k : Fin 15,
      (wlo k : ℝ) * ((sq k : ℝ) * zval y (iOf k) (jOf k) + (cq k : ℝ))
        ≤ (2 * weight (iOf k) (jOf k)) * (1 - Real.cos (zval y (iOf k) (jOf k))) := by
    intro k
    obtain ⟨h1, h2, h3, h4⟩ := hfacts k
    have hw0 : (0 : ℝ) ≤ 2 * weight (iOf k) (jOf k) := weight_nonneg _ _
    have hwlo0 : (0 : ℝ) ≤ (wlo k : ℝ) := by exact_mod_cast wlo_nonneg k
    have hW2 : (0 : ℝ) ≤ 2 * weight (iOf k) (jOf k) := hw0
    calc (wlo k : ℝ) * ((sq k : ℝ) * zval y (iOf k) (jOf k) + (cq k : ℝ))
        ≤ (2 * weight (iOf k) (jOf k)) * ((sq k : ℝ) * zval y (iOf k) (jOf k) + (cq k : ℝ)) :=
          mul_le_mul_of_nonneg_right (hw k) h4
      _ ≤ (2 * weight (iOf k) (jOf k)) * (1 - Real.cos (zval y (iOf k) (jOf k))) :=
          mul_le_mul_of_nonneg_left h3 hW2
  -- partial sum over the 15 certified pairs
  have hpart := FlashCosine.partial_energy_le (w := fun i j => 2 * weight i j) weight_nonneg
      (fun i j => zval y i j) S15 S15_fst_lt_snd
  -- rewrite the S15-sum as a Fin 15 sum
  have hsum : (∑ p ∈ S15, (2 * weight p.1 p.2) * (1 - Real.cos (zval y p.1 p.2)))
      = ∑ k : Fin 15, (2 * weight (iOf k) (jOf k)) * (1 - Real.cos (zval y (iOf k) (jOf k))) := by
    rw [S15]
    exact Finset.sum_image (s := Finset.univ) (g := fun k : Fin 15 => ((iOf k, jOf k) : Fin 9 × Fin 9))
      (fun a _ b _ hab => pair_inj hab)
  -- ≤ by the termwise bound, then partial_energy_le
  calc (∑ k : Fin 15, (wlo k : ℝ) * ((sq k : ℝ) * zval y (iOf k) (jOf k) + (cq k : ℝ)))
      ≤ ∑ k : Fin 15, (2 * weight (iOf k) (jOf k)) * (1 - Real.cos (zval y (iOf k) (jOf k))) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = ∑ p ∈ S15, (2 * weight p.1 p.2) * (1 - Real.cos (zval y p.1 p.2)) := hsum.symm
    _ ≤ 2 * ∑ i, ∑ j, if i < j then weight i j * (1 - Real.cos (zval y i j)) else 0 := by
      refine le_trans hpart (le_of_eq ?_)
      conv_rhs => rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      conv_rhs => rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hij : i < j
      · simp only [hij, if_true]; ring
      · simp only [hij, if_false, mul_zero]

/-! ## 6. Assembly, stage 2: the aggregate identity -/

theorem pair_lt_asm : ∀ k : Fin 15, (iOf k : ℕ) < (jOf k : ℕ) := by decide

theorem sigma_eq (y : Fin 9 → ℝ) (k : Fin 15) :
    tval y (Fin.castSucc (jOf k)) - tval y (Fin.castSucc (iOf k))
      = ∑ q : Fin 9,
          if ((iOf k : ℕ) ≤ (q : ℕ) ∧ (q : ℕ) < (jOf k : ℕ)) then y q else 0 :=
  tval_sub y (pair_lt_asm k).le

/-- **恒等式**（stage 2 承重件）：
`Σ_k wlo_k (sq_k z_k + cq_k) = Wcoef·Lc + Dc·(Σ_q zhat_q y_q) + Cc`。 -/
theorem affine_id (y : Fin 9 → ℝ) :
    (∑ k : Fin 15, (wlo k : ℝ) * ((sq k : ℝ) * zval y (iOf k) (jOf k) + (cq k : ℝ)))
      = (Wcoef : ℝ) * Lc + Dc * (∑ q : Fin 9, (zhat q : ℝ) * y q) + (Cc : ℝ) := by
  simp [zval_eq, sigma_eq y, tval, wlo, sq, cq, iOf, jOf, Wcoef, Cc, zhat,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_sub_distrib]
  push_cast
  ring

end N11Formalization.FlashCosine
