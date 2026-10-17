import Mathlib
import N11Formalization.FlashCosineLeaf284Bridge
import N11Formalization.FlashCosineLeaf284Energy
import N11Formalization.PairTemplate

/-!
  **Leaf 4348 pair layer, stage 4 (pairs 19..24), template V5.**

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

/-! ### pair (2, 6), 1 line(s), branch `endpoint`, shift m = -1 -/

def A26 : ℚ := ((-158795350080916188437041472179928253349 : ℚ) / 57646075230342348800000000000000000000)
def B26 : ℚ := ((-1239298904846446889691759751623319491 : ℚ) / 450359962737049600000000000000000000)
def S26 : ℚ := ((-6821601739515035 : ℚ) / 18014398509481984)
def C26 : ℚ := ((5518438093462488978769386866856666137711920469073671570504050602834145602779393 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000)
def s26_0 : ℚ := ((-6821601739515035 : ℚ) / 18014398509481984)
def c26_0 : ℚ := ((5518438093462488978769386866856666137711920469073671570504050602834145602779393 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000)
def g26_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc26 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((127 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 2))
    (hshi : (((1 : ℚ) / 2) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A26 : ℝ) ≤ zval y 2 6 ∧ zval y 2 6 ≤ (B26 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 2) (j := 6)
      (by norm_num) (dbm := dbm) (slo := ((127 : ℚ) / 256)) (shi := ((1 : ℚ) / 2)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 2) (j := 6)
    (by norm_num) (slo := ((127 : ℚ) / 256)) (shi := ((1 : ℚ) / 2)) (by norm_num) hlo hhi
  have hAq : A26 ≤ ((((2 : ℚ) - 6) * LQ + Dq * ((127 : ℚ) / 256)) : ℚ) := by
    norm_num [A26, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((2 : ℚ) - 6) * Lq + DQ * ((1 : ℚ) / 2)) : ℚ) ≤ B26 := by
    norm_num [B26, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A26 : ℝ) ≤ (((((2 : ℚ) - 6) * LQ + Dq * ((127 : ℚ) / 256)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((2 : ℚ) - 6) * Lq + DQ * ((1 : ℚ) / 2)) : ℚ) : ℝ) ≤ (B26 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line26 : ∀ z ∈ Set.Icc (A26 : ℝ) (B26 : ℝ),
    (S26 : ℝ) * z + (C26 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A26 : ℝ)) (b := (B26 : ℝ)) (m := -1)
    (by norm_num [A26]; linarith [hpLo, hpHi])
    (by norm_num [B26]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S26, A26, C26, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S26, B26, C26, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse26 : S26 = ((-6821601739515035 : ℚ) / 18014398509481984) ∧ C26 = ((5518438093462488978769386866856666137711920469073671570504050602834145602779393 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S26, C26, s26_0, c26_0, g26_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell26 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((127 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 2))
    (hshi : (((1 : ℚ) / 2) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S26 : ℝ) * zval y 2 6 + (C26 : ℝ) ≤ 1 - Real.cos (zval y 2 6) := by
  exact line26 (zval y 2 6) (arc26 y hslo hshi hcell)

/-! ### pair (2, 7), 1 line(s), branch `endpoint`, shift m = -1 -/

def A27 : ℚ := ((-403344350196544097257255497124058131373 : ℚ) / 115292150460684697600000000000000000000)
def B27 : ℚ := ((-201424539707737576167470086648809923231 : ℚ) / 57646075230342348800000000000000000000)
def S27 : ℚ := ((6256795724596401 : ℚ) / 18014398509481984)
def C27 : ℚ := ((1576043842942535491471793110642045357369084555272798092330979977300603453421373 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000)
def s27_0 : ℚ := ((6256795724596401 : ℚ) / 18014398509481984)
def c27_0 : ℚ := ((1576043842942535491471793110642045357369084555272798092330979977300603453421373 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000)
def g27_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc27 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((279 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 2))
    (hshi : (((141 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A27 : ℝ) ≤ zval y 2 7 ∧ zval y 2 7 ≤ (B27 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 2) (j := 7)
      (by norm_num) (dbm := dbm) (slo := ((279 : ℚ) / 512)) (shi := ((141 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 2) (j := 7)
    (by norm_num) (slo := ((279 : ℚ) / 512)) (shi := ((141 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A27 ≤ ((((2 : ℚ) - 7) * LQ + Dq * ((279 : ℚ) / 512)) : ℚ) := by
    norm_num [A27, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((2 : ℚ) - 7) * Lq + DQ * ((141 : ℚ) / 256)) : ℚ) ≤ B27 := by
    norm_num [B27, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A27 : ℝ) ≤ (((((2 : ℚ) - 7) * LQ + Dq * ((279 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((2 : ℚ) - 7) * Lq + DQ * ((141 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B27 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line27 : ∀ z ∈ Set.Icc (A27 : ℝ) (B27 : ℝ),
    (S27 : ℝ) * z + (C27 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A27 : ℝ)) (b := (B27 : ℝ)) (m := -1)
    (by norm_num [A27]; linarith [hpLo, hpHi])
    (by norm_num [B27]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S27, A27, C27, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S27, B27, C27, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse27 : S27 = ((6256795724596401 : ℚ) / 18014398509481984) ∧ C27 = ((1576043842942535491471793110642045357369084555272798092330979977300603453421373 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S27, C27, s27_0, c27_0, g27_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell27 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((279 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 2))
    (hshi : (((141 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S27 : ℝ) * zval y 2 7 + (C27 : ℝ) ≤ 1 - Real.cos (zval y 2 7) := by
  exact line27 (zval y 2 7) (arc27 y hslo hshi hcell)

/-! ### pair (2, 8), 1 line(s), branch `endpoint`, shift m = -1 -/

def A28 : ℚ := ((-120458507202312918363063636279425653869 : ℚ) / 28823037615171174400000000000000000000)
def B28 : ℚ := ((-9630076965745350544170409521128861437 : ℚ) / 2305843009213693952000000000000000000)
def S28 : ℚ := ((7750550574176473 : ℚ) / 9007199254740992)
def C28 : ℚ := ((6380521021332950462836569742233078822272948901586204115292015852013541409167271 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000)
def s28_0 : ℚ := ((7750550574176473 : ℚ) / 9007199254740992)
def c28_0 : ℚ := ((6380521021332950462836569742233078822272948901586204115292015852013541409167271 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000)
def g28_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc28 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((87 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 2))
    (hshi : (((175 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A28 : ℝ) ≤ zval y 2 8 ∧ zval y 2 8 ≤ (B28 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 2) (j := 8)
      (by norm_num) (dbm := dbm) (slo := ((87 : ℚ) / 128)) (shi := ((175 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 2) (j := 8)
    (by norm_num) (slo := ((87 : ℚ) / 128)) (shi := ((175 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A28 ≤ ((((2 : ℚ) - 8) * LQ + Dq * ((87 : ℚ) / 128)) : ℚ) := by
    norm_num [A28, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((2 : ℚ) - 8) * Lq + DQ * ((175 : ℚ) / 256)) : ℚ) ≤ B28 := by
    norm_num [B28, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A28 : ℝ) ≤ (((((2 : ℚ) - 8) * LQ + Dq * ((87 : ℚ) / 128)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((2 : ℚ) - 8) * Lq + DQ * ((175 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B28 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line28 : ∀ z ∈ Set.Icc (A28 : ℝ) (B28 : ℝ),
    (S28 : ℝ) * z + (C28 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A28 : ℝ)) (b := (B28 : ℝ)) (m := -1)
    (by norm_num [A28]; linarith [hpLo, hpHi])
    (by norm_num [B28]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S28, A28, C28, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S28, B28, C28, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse28 : S28 = ((7750550574176473 : ℚ) / 9007199254740992) ∧ C28 = ((6380521021332950462836569742233078822272948901586204115292015852013541409167271 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S28, C28, s28_0, c28_0, g28_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell28 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((87 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 2))
    (hshi : (((175 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 2) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S28 : ℝ) * zval y 2 8 + (C28 : ℝ) ≤ 1 - Real.cos (zval y 2 8) := by
  exact line28 (zval y 2 8) (arc28 y hslo hshi hcell)

/-! ### pair (3, 4), 1 line(s), branch `tangent`, shift m = 0 -/

def A34 : ℚ := ((-8098398383331788025458969362966234753 : ℚ) / 14411518807585587200000000000000000000)
def B34 : ℚ := ((-64622096806212570956368474176102257123 : ℚ) / 115292150460684697600000000000000000000)
def S34 : ℚ := ((-4791101766943145 : ℚ) / 9007199254740992)
def C34 : ℚ := ((-2902603036683771067519759678985153729148206778730769029713016502217157018052849 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s34_0 : ℚ := ((-4791101766943145 : ℚ) / 9007199254740992)
def c34_0 : ℚ := ((-2902603036683771067519759678985153729148206778730769029713016502217157018052849 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g34_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc34 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((19 : ℚ) / 64) : ℚ) = -dbm (Fin.castSucc 4) (Fin.castSucc 3))
    (hshi : (((153 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 3) (Fin.castSucc 4))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A34 : ℝ) ≤ zval y 3 4 ∧ zval y 3 4 ≤ (B34 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 3) (j := 4)
      (by norm_num) (dbm := dbm) (slo := ((19 : ℚ) / 64)) (shi := ((153 : ℚ) / 512)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 3) (j := 4)
    (by norm_num) (slo := ((19 : ℚ) / 64)) (shi := ((153 : ℚ) / 512)) (by norm_num) hlo hhi
  have hAq : A34 ≤ ((((3 : ℚ) - 4) * LQ + Dq * ((19 : ℚ) / 64)) : ℚ) := by
    norm_num [A34, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((3 : ℚ) - 4) * Lq + DQ * ((153 : ℚ) / 512)) : ℚ) ≤ B34 := by
    norm_num [B34, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A34 : ℝ) ≤ (((((3 : ℚ) - 4) * LQ + Dq * ((19 : ℚ) / 64)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((3 : ℚ) - 4) * Lq + DQ * ((153 : ℚ) / 512)) : ℚ) : ℝ) ≤ (B34 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line34 : ∀ z ∈ Set.Icc (A34 : ℝ) (B34 : ℝ),
    (S34 : ℝ) * z + (C34 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A34 : ℝ)) (b := (B34 : ℝ)) (m := 0)
    (by norm_num [A34]; linarith [hpLo, hpHi])
    (by norm_num [B34]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-1402163311 : ℚ) / 2500000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A34, B34]
  · norm_num
  · norm_num [S34, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S34, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C34, S34, A34, B34, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse34 : S34 = ((-4791101766943145 : ℚ) / 9007199254740992) ∧ C34 = ((-2902603036683771067519759678985153729148206778730769029713016502217157018052849 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S34, C34, s34_0, c34_0, g34_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell34 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((19 : ℚ) / 64) : ℚ) = -dbm (Fin.castSucc 4) (Fin.castSucc 3))
    (hshi : (((153 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 3) (Fin.castSucc 4))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S34 : ℝ) * zval y 3 4 + (C34 : ℝ) ≤ 1 - Real.cos (zval y 3 4) := by
  exact line34 (zval y 3 4) (arc34 y hslo hshi hcell)

/-! ### pair (3, 5), 1 line(s), branch `tangent`, shift m = 0 -/

def A35 : ℚ := ((-7172097796947644183783737309380714857 : ℚ) / 5764607523034234880000000000000000000)
def B35 : ℚ := ((-142946685158814832796602616262390871493 : ℚ) / 115292150460684697600000000000000000000)
def S35 : ℚ := ((-8526954058944465 : ℚ) / 9007199254740992)
def C35 : ℚ := ((-49868329944809730994211796249501775055143254061666967844550260345355202833053541 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s35_0 : ℚ := ((-8526954058944465 : ℚ) / 9007199254740992)
def c35_0 : ℚ := ((-49868329944809730994211796249501775055143254061666967844550260345355202833053541 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g35_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc35 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((55 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 5) (Fin.castSucc 3))
    (hshi : (((223 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 3) (Fin.castSucc 5))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A35 : ℝ) ≤ zval y 3 5 ∧ zval y 3 5 ≤ (B35 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 3) (j := 5)
      (by norm_num) (dbm := dbm) (slo := ((55 : ℚ) / 128)) (shi := ((223 : ℚ) / 512)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 3) (j := 5)
    (by norm_num) (slo := ((55 : ℚ) / 128)) (shi := ((223 : ℚ) / 512)) (by norm_num) hlo hhi
  have hAq : A35 ≤ ((((3 : ℚ) - 5) * LQ + Dq * ((55 : ℚ) / 128)) : ℚ) := by
    norm_num [A35, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((3 : ℚ) - 5) * Lq + DQ * ((223 : ℚ) / 512)) : ℚ) ≤ B35 := by
    norm_num [B35, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A35 : ℝ) ≤ (((((3 : ℚ) - 5) * LQ + Dq * ((55 : ℚ) / 128)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((3 : ℚ) - 5) * Lq + DQ * ((223 : ℚ) / 512)) : ℚ) : ℝ) ≤ (B35 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line35 : ∀ z ∈ Set.Icc (A35 : ℝ) (B35 : ℝ),
    (S35 : ℝ) * z + (C35 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A35 : ℝ)) (b := (B35 : ℝ)) (m := 0)
    (by norm_num [A35]; linarith [hpLo, hpHi])
    (by norm_num [B35]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-776735163 : ℚ) / 625000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A35, B35]
  · norm_num
  · norm_num [S35, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S35, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C35, S35, A35, B35, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse35 : S35 = ((-8526954058944465 : ℚ) / 9007199254740992) ∧ C35 = ((-49868329944809730994211796249501775055143254061666967844550260345355202833053541 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S35, C35, s35_0, c35_0, g35_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell35 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((55 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 5) (Fin.castSucc 3))
    (hshi : (((223 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 3) (Fin.castSucc 5))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S35 : ℝ) * zval y 3 5 + (C35 : ℝ) ≤ 1 - Real.cos (zval y 3 5) := by
  exact line35 (zval y 3 5) (arc35 y hslo hshi hcell)

/-! ### pair (3, 6), 1 line(s), branch `endpoint`, shift m = -1 -/

def A36 : ℚ := ((-45839121194732920811769459790363184363 : ℚ) / 23058430092136939520000000000000000000)
def B36 : ℚ := ((-228865425452789694403798453816975539277 : ℚ) / 115292150460684697600000000000000000000)
def S36 : ℚ := ((-8239990828710127 : ℚ) / 9007199254740992)
def C36 : ℚ := ((-41346204155295426244043061558640721727026534219103236112965573715765356760706011 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s36_0 : ℚ := ((-8239990828710127 : ℚ) / 9007199254740992)
def c36_0 : ℚ := ((-41346204155295426244043061558640721727026534219103236112965573715765356760706011 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g36_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc36 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((245 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 3))
    (hshi : (((247 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 3) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A36 : ℝ) ≤ zval y 3 6 ∧ zval y 3 6 ≤ (B36 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 3) (j := 6)
      (by norm_num) (dbm := dbm) (slo := ((245 : ℚ) / 512)) (shi := ((247 : ℚ) / 512)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 3) (j := 6)
    (by norm_num) (slo := ((245 : ℚ) / 512)) (shi := ((247 : ℚ) / 512)) (by norm_num) hlo hhi
  have hAq : A36 ≤ ((((3 : ℚ) - 6) * LQ + Dq * ((245 : ℚ) / 512)) : ℚ) := by
    norm_num [A36, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((3 : ℚ) - 6) * Lq + DQ * ((247 : ℚ) / 512)) : ℚ) ≤ B36 := by
    norm_num [B36, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A36 : ℝ) ≤ (((((3 : ℚ) - 6) * LQ + Dq * ((245 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((3 : ℚ) - 6) * Lq + DQ * ((247 : ℚ) / 512)) : ℚ) : ℝ) ≤ (B36 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line36 : ∀ z ∈ Set.Icc (A36 : ℝ) (B36 : ℝ),
    (S36 : ℝ) * z + (C36 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A36 : ℝ)) (b := (B36 : ℝ)) (m := -1)
    (by norm_num [A36]; linarith [hpLo, hpHi])
    (by norm_num [B36]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S36, A36, C36, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S36, B36, C36, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse36 : S36 = ((-8239990828710127 : ℚ) / 9007199254740992) ∧ C36 = ((-41346204155295426244043061558640721727026534219103236112965573715765356760706011 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S36, C36, s36_0, c36_0, g36_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell36 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((245 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 3))
    (hshi : (((247 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 3) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S36 : ℝ) * zval y 3 6 + (C36 : ℝ) ≤ 1 - Real.cos (zval y 3 6) := by
  exact line36 (zval y 3 6) (arc36 y hslo hshi hcell)
#print axioms N11Formalization.Leaf4348Pairs.arc26
#print axioms N11Formalization.Leaf4348Pairs.line26
#print axioms N11Formalization.Leaf4348Pairs.collapse26
#print axioms N11Formalization.Leaf4348Pairs.cell26
#print axioms N11Formalization.Leaf4348Pairs.arc27
#print axioms N11Formalization.Leaf4348Pairs.line27
#print axioms N11Formalization.Leaf4348Pairs.collapse27
#print axioms N11Formalization.Leaf4348Pairs.cell27
#print axioms N11Formalization.Leaf4348Pairs.arc28
#print axioms N11Formalization.Leaf4348Pairs.line28
#print axioms N11Formalization.Leaf4348Pairs.collapse28
#print axioms N11Formalization.Leaf4348Pairs.cell28
#print axioms N11Formalization.Leaf4348Pairs.arc34
#print axioms N11Formalization.Leaf4348Pairs.line34
#print axioms N11Formalization.Leaf4348Pairs.collapse34
#print axioms N11Formalization.Leaf4348Pairs.cell34
#print axioms N11Formalization.Leaf4348Pairs.arc35
#print axioms N11Formalization.Leaf4348Pairs.line35
#print axioms N11Formalization.Leaf4348Pairs.collapse35
#print axioms N11Formalization.Leaf4348Pairs.cell35
#print axioms N11Formalization.Leaf4348Pairs.arc36
#print axioms N11Formalization.Leaf4348Pairs.line36
#print axioms N11Formalization.Leaf4348Pairs.collapse36
#print axioms N11Formalization.Leaf4348Pairs.cell36

end N11Formalization.Leaf4348Pairs
