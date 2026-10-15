import Mathlib
import N11Formalization.FlashCosineLeaf284Bridge
import N11Formalization.FlashCosineLeaf284Energy
import N11Formalization.PairTemplate

/-!
  **Leaf 4348 pair layer, stage 3 (pairs 13..18), template V5.**

  DRAFT for the Lead's serial slot.  No `sorry`, no custom `axiom`, no `native_decide`.

  Per pair: `arc` (interval membership via the kernel-proved `PairTemplate` lemmas, with explicit
  middle terms), `line` (ONE compiled rule on the gamma-collapsed line; the pi-arc bounds are
  discharged by `RatInterval.piLo_lt_pi`/`pi_lt_piHi` exactly as in the compiled `cert0` block of
  `FlashCosineLeaf284Energy`), `collapse` (literal identity), `cell` (the pair's whole-cell
  minorant).  Shifts `m` are per pair, taken from the source table.
-/

namespace N11Formalization.Leaf4348Pairs

open Finset
set_option autoImplicit false
open N11Formalization.FlashCosine (Lq LQ Dq DQ L_mem D_mem tval zval zval_eq)
open N11Formalization.FlashLeafSplit (Cell tlift)

/-! ### pair (1, 6), 1 line(s), branch `endpoint`, shift m = -1 -/

def A16 : ℚ := ((-406976335907546169351342249509336701659 : ℚ) / 115292150460684697600000000000000000000)
def B16 : ℚ := ((-203075442303688141334200890011482978321 : ℚ) / 57646075230342348800000000000000000000)
def S16 : ℚ := ((3380930067170977 : ℚ) / 9007199254740992)
def C16 : ℚ := ((16252647697183462638514342028498592315019519763130782465956251652604184436443147 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s16_0 : ℚ := ((3380930067170977 : ℚ) / 9007199254740992)
def c16_0 : ℚ := ((16252647697183462638514342028498592315019519763130782465956251652604184436443147 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g16_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc16 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((257 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 1))
    (hshi : (((131 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A16 : ℝ) ≤ zval y 1 6 ∧ zval y 1 6 ≤ (B16 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 1) (j := 6)
      (by norm_num) (dbm := dbm) (slo := ((257 : ℚ) / 512)) (shi := ((131 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 1) (j := 6)
    (by norm_num) (slo := ((257 : ℚ) / 512)) (shi := ((131 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A16 ≤ ((((1 : ℚ) - 6) * LQ + Dq * ((257 : ℚ) / 512)) : ℚ) := by
    norm_num [A16, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((1 : ℚ) - 6) * Lq + DQ * ((131 : ℚ) / 256)) : ℚ) ≤ B16 := by
    norm_num [B16, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A16 : ℝ) ≤ (((((1 : ℚ) - 6) * LQ + Dq * ((257 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((1 : ℚ) - 6) * Lq + DQ * ((131 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B16 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line16 : ∀ z ∈ Set.Icc (A16 : ℝ) (B16 : ℝ),
    (S16 : ℝ) * z + (C16 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A16 : ℝ)) (b := (B16 : ℝ)) (m := -1)
    (by norm_num [A16]; linarith [hpLo, hpHi])
    (by norm_num [B16]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S16, A16, C16, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S16, B16, C16, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse16 : S16 = ((3380930067170977 : ℚ) / 9007199254740992) ∧ C16 = ((16252647697183462638514342028498592315019519763130782465956251652604184436443147 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S16, C16, s16_0, c16_0, g16_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell16 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((257 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 1))
    (hshi : (((131 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S16 : ℝ) * zval y 1 6 + (C16 : ℝ) ≤ 1 - Real.cos (zval y 1 6) := by
  exact line16 (zval y 1 6) (arc16 y hslo hshi hcell)

/-! ### pair (1, 7), 1 line(s), branch `endpoint`, shift m = -1 -/

def A17 : ℚ := ((-12326504161535997407213067221350454909 : ℚ) / 2882303761517117440000000000000000000)
def B17 : ℚ := ((-246034812450675572137798808788775312213 : ℚ) / 57646075230342348800000000000000000000)
def S17 : ℚ := ((1018623328756757 : ℚ) / 1125899906842624)
def C17 : ℚ := ((6614060156942252049532792270474537139360703068833703995515927518372677103094753 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000)
def s17_0 : ℚ := ((1018623328756757 : ℚ) / 1125899906842624)
def c17_0 : ℚ := ((6614060156942252049532792270474537139360703068833703995515927518372677103094753 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000)
def g17_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc17 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((35 : ℚ) / 64) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 1))
    (hshi : (((143 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A17 : ℝ) ≤ zval y 1 7 ∧ zval y 1 7 ≤ (B17 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 1) (j := 7)
      (by norm_num) (dbm := dbm) (slo := ((35 : ℚ) / 64)) (shi := ((143 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 1) (j := 7)
    (by norm_num) (slo := ((35 : ℚ) / 64)) (shi := ((143 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A17 ≤ ((((1 : ℚ) - 7) * LQ + Dq * ((35 : ℚ) / 64)) : ℚ) := by
    norm_num [A17, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((1 : ℚ) - 7) * Lq + DQ * ((143 : ℚ) / 256)) : ℚ) ≤ B17 := by
    norm_num [B17, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A17 : ℝ) ≤ (((((1 : ℚ) - 7) * LQ + Dq * ((35 : ℚ) / 64)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((1 : ℚ) - 7) * Lq + DQ * ((143 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B17 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line17 : ∀ z ∈ Set.Icc (A17 : ℝ) (B17 : ℝ),
    (S17 : ℝ) * z + (C17 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A17 : ℝ)) (b := (B17 : ℝ)) (m := -1)
    (by norm_num [A17]; linarith [hpLo, hpHi])
    (by norm_num [B17]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S17, A17, C17, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S17, B17, C17, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse17 : S17 = ((1018623328756757 : ℚ) / 1125899906842624) ∧ C17 = ((6614060156942252049532792270474537139360703068833703995515927518372677103094753 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S17, C17, s17_0, c17_0, g17_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell17 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((35 : ℚ) / 64) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 1))
    (hshi : (((143 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S17 : ℝ) * zval y 1 7 + (C17 : ℝ) ≤ 1 - Real.cos (zval y 1 7) := by
  exact line17 (zval y 1 7) (arc17 y hslo hshi hcell)

/-! ### pair (1, 8), 1 line(s), branch `tangent`, shift m = -1 -/

def A18 : ℚ := ((-571549845074147472483521736847662680463 : ℚ) / 115292150460684697600000000000000000000)
def B18 : ℚ := ((-285362196886571759574588960168186924907 : ℚ) / 57646075230342348800000000000000000000)
def S18 : ℚ := ((4371280577696623 : ℚ) / 4503599627370496)
def C18 : ℚ := ((13922951157198144453050473518312454943298590422640538504835945578999757886284203 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000)
def s18_0 : ℚ := ((4371280577696623 : ℚ) / 4503599627370496)
def c18_0 : ℚ := ((13922951157198144453050473518312454943298590422640538504835945578999757886284203 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000)
def g18_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc18 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((349 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 1))
    (hshi : (((177 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A18 : ℝ) ≤ zval y 1 8 ∧ zval y 1 8 ≤ (B18 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 1) (j := 8)
      (by norm_num) (dbm := dbm) (slo := ((349 : ℚ) / 512)) (shi := ((177 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 1) (j := 8)
    (by norm_num) (slo := ((349 : ℚ) / 512)) (shi := ((177 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A18 ≤ ((((1 : ℚ) - 8) * LQ + Dq * ((349 : ℚ) / 512)) : ℚ) := by
    norm_num [A18, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((1 : ℚ) - 8) * Lq + DQ * ((177 : ℚ) / 256)) : ℚ) ≤ B18 := by
    norm_num [B18, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A18 : ℝ) ≤ (((((1 : ℚ) - 8) * LQ + Dq * ((349 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((1 : ℚ) - 8) * Lq + DQ * ((177 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B18 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line18 : ∀ z ∈ Set.Icc (A18 : ℝ) (B18 : ℝ),
    (S18 : ℝ) * z + (C18 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A18 : ℝ)) (b := (B18 : ℝ)) (m := -1)
    (by norm_num [A18]; linarith [hpLo, hpHi])
    (by norm_num [B18]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-9910788169 : ℚ) / 2000000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A18, B18]
  · norm_num
  · norm_num [S18, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S18, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C18, S18, A18, B18, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse18 : S18 = ((4371280577696623 : ℚ) / 4503599627370496) ∧ C18 = ((13922951157198144453050473518312454943298590422640538504835945578999757886284203 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S18, C18, s18_0, c18_0, g18_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell18 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((349 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 1))
    (hshi : (((177 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S18 : ℝ) * zval y 1 8 + (C18 : ℝ) ≤ 1 - Real.cos (zval y 1 8) := by
  exact line18 (zval y 1 8) (arc18 y hslo hshi hcell)

/-! ### pair (2, 3), 1 line(s), branch `tangent`, shift m = 0 -/

def A23 : ℚ := ((-88395094188167772815235645408040584883 : ℚ) / 115292150460684697600000000000000000000)
def B23 : ℚ := ((-88064913668710596323945881926059639401 : ℚ) / 115292150460684697600000000000000000000)
def S23 : ℚ := ((-3122337654496649 : ℚ) / 4503599627370496)
def C23 : ℚ := ((-25175590588971992768041416841961984545327676206783458533963211728139634808395217 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s23_0 : ℚ := ((-3122337654496649 : ℚ) / 4503599627370496)
def c23_0 : ℚ := ((-25175590588971992768041416841961984545327676206783458533963211728139634808395217 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g23_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc23 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((9 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 3) (Fin.castSucc 2))
    (hshi : (((11 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 3))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A23 : ℝ) ≤ zval y 2 3 ∧ zval y 2 3 ≤ (B23 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 2) (j := 3)
      (by norm_num) (dbm := dbm) (slo := ((9 : ℚ) / 512)) (shi := ((11 : ℚ) / 512)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 2) (j := 3)
    (by norm_num) (slo := ((9 : ℚ) / 512)) (shi := ((11 : ℚ) / 512)) (by norm_num) hlo hhi
  have hAq : A23 ≤ ((((2 : ℚ) - 3) * LQ + Dq * ((9 : ℚ) / 512)) : ℚ) := by
    norm_num [A23, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((2 : ℚ) - 3) * Lq + DQ * ((11 : ℚ) / 512)) : ℚ) ≤ B23 := by
    norm_num [B23, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A23 : ℝ) ≤ (((((2 : ℚ) - 3) * LQ + Dq * ((9 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((2 : ℚ) - 3) * Lq + DQ * ((11 : ℚ) / 512)) : ℚ) : ℝ) ≤ (B23 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line23 : ∀ z ∈ Set.Icc (A23 : ℝ) (B23 : ℝ),
    (S23 : ℝ) * z + (C23 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A23 : ℝ)) (b := (B23 : ℝ)) (m := 0)
    (by norm_num [A23]; linarith [hpLo, hpHi])
    (by norm_num [B23]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-1915139441 : ℚ) / 2500000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A23, B23]
  · norm_num
  · norm_num [S23, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S23, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C23, S23, A23, B23, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse23 : S23 = ((-3122337654496649 : ℚ) / 4503599627370496) ∧ C23 = ((-25175590588971992768041416841961984545327676206783458533963211728139634808395217 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S23, C23, s23_0, c23_0, g23_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell23 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((9 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 3) (Fin.castSucc 2))
    (hshi : (((11 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 3))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S23 : ℝ) * zval y 2 3 + (C23 : ℝ) ≤ 1 - Real.cos (zval y 2 3) := by
  exact line23 (zval y 2 3) (arc23 y hslo hshi hcell)

/-! ### pair (2, 4), 1 line(s), branch `tangent`, shift m = 0 -/

def A24 : ℚ := ((-76508595497615536870951728510765263947 : ℚ) / 57646075230342348800000000000000000000)
def B24 : ℚ := ((-38171752618730791820078589025540474131 : ℚ) / 28823037615171174400000000000000000000)
def S24 : ℚ := ((-8741305561927261 : ℚ) / 9007199254740992)
def C24 : ℚ := ((-10584304280486353636890343895791983843446912284175478129714251872235145928087981 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s24_0 : ℚ := ((-8741305561927261 : ℚ) / 9007199254740992)
def c24_0 : ℚ := ((-10584304280486353636890343895791983843446912284175478129714251872235145928087981 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g24_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc24 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((81 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 4) (Fin.castSucc 2))
    (hshi : (((41 : ℚ) / 128) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 4))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A24 : ℝ) ≤ zval y 2 4 ∧ zval y 2 4 ≤ (B24 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 2) (j := 4)
      (by norm_num) (dbm := dbm) (slo := ((81 : ℚ) / 256)) (shi := ((41 : ℚ) / 128)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 2) (j := 4)
    (by norm_num) (slo := ((81 : ℚ) / 256)) (shi := ((41 : ℚ) / 128)) (by norm_num) hlo hhi
  have hAq : A24 ≤ ((((2 : ℚ) - 4) * LQ + Dq * ((81 : ℚ) / 256)) : ℚ) := by
    norm_num [A24, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((2 : ℚ) - 4) * Lq + DQ * ((41 : ℚ) / 128)) : ℚ) ≤ B24 := by
    norm_num [B24, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A24 : ℝ) ≤ (((((2 : ℚ) - 4) * LQ + Dq * ((81 : ℚ) / 256)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((2 : ℚ) - 4) * Lq + DQ * ((41 : ℚ) / 128)) : ℚ) : ℝ) ≤ (B24 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line24 : ∀ z ∈ Set.Icc (A24 : ℝ) (B24 : ℝ),
    (S24 : ℝ) * z + (C24 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A24 : ℝ)) (b := (B24 : ℝ)) (m := 0)
    (by norm_num [A24]; linarith [hpLo, hpHi])
    (by norm_num [B24]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-1659015709 : ℚ) / 1250000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A24, B24]
  · norm_num
  · norm_num [S24, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S24, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C24, S24, A24, B24, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse24 : S24 = ((-8741305561927261 : ℚ) / 9007199254740992) ∧ C24 = ((-10584304280486353636890343895791983843446912284175478129714251872235145928087981 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S24, C24, s24_0, c24_0, g24_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell24 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((81 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 4) (Fin.castSucc 2))
    (hshi : (((41 : ℚ) / 128) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 4))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S24 : ℝ) * zval y 2 4 + (C24 : ℝ) ≤ 1 - Real.cos (zval y 2 4) := by
  exact line24 (zval y 2 4) (arc24 y hslo hshi hcell)

/-! ### pair (2, 5), 1 line(s), branch `endpoint`, shift m = -1 -/

def A25 : ℚ := ((-23167195986752965321390644830541494701 : ℚ) / 11529215046068469760000000000000000000)
def B25 : ℚ := ((-115505799413762714560274249094225255447 : ℚ) / 57646075230342348800000000000000000000)
def S25 : ℚ := ((-8165408613718357 : ℚ) / 9007199254740992)
def C25 : ℚ := ((-1984653742381165039046921250401411072656883220060614049971179433943365345104517 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s25_0 : ℚ := ((-8165408613718357 : ℚ) / 9007199254740992)
def c25_0 : ℚ := ((-1984653742381165039046921250401411072656883220060614049971179433943365345104517 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g25_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc25 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((115 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 5) (Fin.castSucc 2))
    (hshi : (((117 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 5))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A25 : ℝ) ≤ zval y 2 5 ∧ zval y 2 5 ≤ (B25 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 2) (j := 5)
      (by norm_num) (dbm := dbm) (slo := ((115 : ℚ) / 256)) (shi := ((117 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 2) (j := 5)
    (by norm_num) (slo := ((115 : ℚ) / 256)) (shi := ((117 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A25 ≤ ((((2 : ℚ) - 5) * LQ + Dq * ((115 : ℚ) / 256)) : ℚ) := by
    norm_num [A25, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((2 : ℚ) - 5) * Lq + DQ * ((117 : ℚ) / 256)) : ℚ) ≤ B25 := by
    norm_num [B25, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A25 : ℝ) ≤ (((((2 : ℚ) - 5) * LQ + Dq * ((115 : ℚ) / 256)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((2 : ℚ) - 5) * Lq + DQ * ((117 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B25 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line25 : ∀ z ∈ Set.Icc (A25 : ℝ) (B25 : ℝ),
    (S25 : ℝ) * z + (C25 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A25 : ℝ)) (b := (B25 : ℝ)) (m := -1)
    (by norm_num [A25]; linarith [hpLo, hpHi])
    (by norm_num [B25]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S25, A25, C25, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S25, B25, C25, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse25 : S25 = ((-8165408613718357 : ℚ) / 9007199254740992) ∧ C25 = ((-1984653742381165039046921250401411072656883220060614049971179433943365345104517 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S25, C25, s25_0, c25_0, g25_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell25 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((115 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 5) (Fin.castSucc 2))
    (hshi : (((117 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 5))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S25 : ℝ) * zval y 2 5 + (C25 : ℝ) ≤ 1 - Real.cos (zval y 2 5) := by
  exact line25 (zval y 2 5) (arc25 y hslo hshi hcell)
#print axioms N11Formalization.Leaf4348Pairs.arc16
#print axioms N11Formalization.Leaf4348Pairs.line16
#print axioms N11Formalization.Leaf4348Pairs.collapse16
#print axioms N11Formalization.Leaf4348Pairs.cell16
#print axioms N11Formalization.Leaf4348Pairs.arc17
#print axioms N11Formalization.Leaf4348Pairs.line17
#print axioms N11Formalization.Leaf4348Pairs.collapse17
#print axioms N11Formalization.Leaf4348Pairs.cell17
#print axioms N11Formalization.Leaf4348Pairs.arc18
#print axioms N11Formalization.Leaf4348Pairs.line18
#print axioms N11Formalization.Leaf4348Pairs.collapse18
#print axioms N11Formalization.Leaf4348Pairs.cell18
#print axioms N11Formalization.Leaf4348Pairs.arc23
#print axioms N11Formalization.Leaf4348Pairs.line23
#print axioms N11Formalization.Leaf4348Pairs.collapse23
#print axioms N11Formalization.Leaf4348Pairs.cell23
#print axioms N11Formalization.Leaf4348Pairs.arc24
#print axioms N11Formalization.Leaf4348Pairs.line24
#print axioms N11Formalization.Leaf4348Pairs.collapse24
#print axioms N11Formalization.Leaf4348Pairs.cell24
#print axioms N11Formalization.Leaf4348Pairs.arc25
#print axioms N11Formalization.Leaf4348Pairs.line25
#print axioms N11Formalization.Leaf4348Pairs.collapse25
#print axioms N11Formalization.Leaf4348Pairs.cell25

end N11Formalization.Leaf4348Pairs
