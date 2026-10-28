import Mathlib
import N11Formalization.FlashCosineLeaf284Bridge
import N11Formalization.FlashCosineLeaf284Energy
import N11Formalization.PairTemplate

/-!
  **Leaf 4348 pair layer, stage 2 (pairs 7..12), template V5.**

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

/-! ### pair (0, 7), 1 line(s), branch `tangent`, shift m = -1 -/

def A07 : ℚ := ((-581125080130425662549750447681578911217 : ℚ) / 115292150460684697600000000000000000000)
def B07 : ℚ := ((-145239997467009255795727225296236697843 : ℚ) / 28823037615171174400000000000000000000)
def S07 : ℚ := ((4265481571818827 : ℚ) / 4503599627370496)
def C07 : ℚ := ((54517387569457878785463156227952562712600231934916213387164527797739257874934029 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s07_0 : ℚ := ((4265481571818827 : ℚ) / 4503599627370496)
def c07_0 : ℚ := ((54517387569457878785463156227952562712600231934916213387164527797739257874934029 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g07_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc07 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((291 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 0))
    (hshi : (((73 : ℚ) / 128) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A07 : ℝ) ≤ zval y 0 7 ∧ zval y 0 7 ≤ (B07 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 0) (j := 7)
      (by norm_num) (dbm := dbm) (slo := ((291 : ℚ) / 512)) (shi := ((73 : ℚ) / 128)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 0) (j := 7)
    (by norm_num) (slo := ((291 : ℚ) / 512)) (shi := ((73 : ℚ) / 128)) (by norm_num) hlo hhi
  have hAq : A07 ≤ ((((0 : ℚ) - 7) * LQ + Dq * ((291 : ℚ) / 512)) : ℚ) := by
    norm_num [A07, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((0 : ℚ) - 7) * Lq + DQ * ((73 : ℚ) / 128)) : ℚ) ≤ B07 := by
    norm_num [B07, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A07 : ℝ) ≤ (((((0 : ℚ) - 7) * LQ + Dq * ((291 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((0 : ℚ) - 7) * Lq + DQ * ((73 : ℚ) / 128)) : ℚ) : ℝ) ≤ (B07 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line07 : ∀ z ∈ Set.Icc (A07 : ℝ) (B07 : ℝ),
    (S07 : ℝ) * z + (C07 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A07 : ℝ)) (b := (B07 : ℝ)) (m := -1)
    (by norm_num [A07]; linarith [hpLo, hpHi])
    (by norm_num [B07]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-50390246653 : ℚ) / 10000000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A07, B07]
  · norm_num
  · norm_num [S07, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S07, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C07, S07, A07, B07, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse07 : S07 = ((4265481571818827 : ℚ) / 4503599627370496) ∧ C07 = ((54517387569457878785463156227952562712600231934916213387164527797739257874934029 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S07, C07, s07_0, c07_0, g07_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell07 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((291 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 0))
    (hshi : (((73 : ℚ) / 128) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S07 : ℝ) * zval y 0 7 + (C07 : ℝ) ≤ 1 - Real.cos (zval y 0 7) := by
  exact line07 (zval y 0 7) (arc07 y hslo hshi hcell)

/-! ### pair (0, 8), 1 line(s), branch `tangent`, shift m = -1 -/

def A08 : ℚ := ((-659779849002724242021753438965463330333 : ℚ) / 115292150460684697600000000000000000000)
def B08 : ℚ := ((-16490368968495734951412230098594250419 : ℚ) / 2882303761517117440000000000000000000)
def S08 : ℚ := ((4797925903495409 : ℚ) / 9007199254740992)
def C08 : ℚ := ((32013515027462289014539884674818026978149344475587686722265048386975576879477699 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s08_0 : ℚ := ((4797925903495409 : ℚ) / 9007199254740992)
def c08_0 : ℚ := ((32013515027462289014539884674818026978149344475587686722265048386975576879477699 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g08_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc08 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((359 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 0))
    (hshi : (((45 : ℚ) / 64) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A08 : ℝ) ≤ zval y 0 8 ∧ zval y 0 8 ≤ (B08 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 0) (j := 8)
      (by norm_num) (dbm := dbm) (slo := ((359 : ℚ) / 512)) (shi := ((45 : ℚ) / 64)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 0) (j := 8)
    (by norm_num) (slo := ((359 : ℚ) / 512)) (shi := ((45 : ℚ) / 64)) (by norm_num) hlo hhi
  have hAq : A08 ≤ ((((0 : ℚ) - 8) * LQ + Dq * ((359 : ℚ) / 512)) : ℚ) := by
    norm_num [A08, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((0 : ℚ) - 8) * Lq + DQ * ((45 : ℚ) / 64)) : ℚ) ≤ B08 := by
    norm_num [B08, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A08 : ℝ) ≤ (((((0 : ℚ) - 8) * LQ + Dq * ((359 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((0 : ℚ) - 8) * Lq + DQ * ((45 : ℚ) / 64)) : ℚ) : ℝ) ≤ (B08 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line08 : ∀ z ∈ Set.Icc (A08 : ℝ) (B08 : ℝ),
    (S08 : ℝ) * z + (C08 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A08 : ℝ)) (b := (B08 : ℝ)) (m := -1)
    (by norm_num [A08]; linarith [hpLo, hpHi])
    (by norm_num [B08]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-57214250267 : ℚ) / 10000000000)) (e := ((11 : ℚ) / 5000000000)) hm
  · norm_num [A08, B08]
  · norm_num
  · norm_num [S08, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S08, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C08, S08, A08, B08, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse08 : S08 = ((4797925903495409 : ℚ) / 9007199254740992) ∧ C08 = ((32013515027462289014539884674818026978149344475587686722265048386975576879477699 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S08, C08, s08_0, c08_0, g08_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell08 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((359 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 0))
    (hshi : (((45 : ℚ) / 64) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S08 : ℝ) * zval y 0 8 + (C08 : ℝ) ≤ 1 - Real.cos (zval y 0 8) := by
  exact line08 (zval y 0 8) (arc08 y hslo hshi hcell)

/-! ### pair (1, 2), 1 line(s), branch `tangent`, shift m = 0 -/

def A12 : ℚ := ((-89715816264895799031267191729960064987 : ℚ) / 115292150460684697600000000000000000000)
def B12 : ℚ := ((-44445182483342939453655641803698083473 : ℚ) / 57646075230342348800000000000000000000)
def S12 : ℚ := ((-6311600552680405 : ℚ) / 9007199254740992)
def C12 : ℚ := ((-12874314074284368273771485034292833711116034526729013896304516612624564086758851 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s12_0 : ℚ := ((-6311600552680405 : ℚ) / 9007199254740992)
def c12_0 : ℚ := ((-12874314074284368273771485034292833711116034526729013896304516612624564086758851 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g12_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc12 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((1 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 2) (Fin.castSucc 1))
    (hshi : (((3 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 2))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A12 : ℝ) ≤ zval y 1 2 ∧ zval y 1 2 ≤ (B12 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 1) (j := 2)
      (by norm_num) (dbm := dbm) (slo := ((1 : ℚ) / 512)) (shi := ((3 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 1) (j := 2)
    (by norm_num) (slo := ((1 : ℚ) / 512)) (shi := ((3 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A12 ≤ ((((1 : ℚ) - 2) * LQ + Dq * ((1 : ℚ) / 512)) : ℚ) := by
    norm_num [A12, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((1 : ℚ) - 2) * Lq + DQ * ((3 : ℚ) / 256)) : ℚ) ≤ B12 := by
    norm_num [B12, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A12 : ℝ) ≤ (((((1 : ℚ) - 2) * LQ + Dq * ((1 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((1 : ℚ) - 2) * Lq + DQ * ((3 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B12 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line12 : ∀ z ∈ Set.Icc (A12 : ℝ) (B12 : ℝ),
    (S12 : ℝ) * z + (C12 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A12 : ℝ)) (b := (B12 : ℝ)) (m := 0)
    (by norm_num [A12]; linarith [hpLo, hpHi])
    (by norm_num [B12]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-776418007 : ℚ) / 1000000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A12, B12]
  · norm_num
  · norm_num [S12, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S12, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C12, S12, A12, B12, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse12 : S12 = ((-6311600552680405 : ℚ) / 9007199254740992) ∧ C12 = ((-12874314074284368273771485034292833711116034526729013896304516612624564086758851 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S12, C12, s12_0, c12_0, g12_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell12 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((1 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 2) (Fin.castSucc 1))
    (hshi : (((3 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 2))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S12 : ℝ) * zval y 1 2 + (C12 : ℝ) ≤ 1 - Real.cos (zval y 1 2) := by
  exact line12 (zval y 1 2) (arc12 y hslo hshi hcell)

/-! ### pair (1, 3), 1 line(s), branch `tangent`, shift m = 0 -/

def A13 : ℚ := ((-17811091045306357184650283713800064987 : ℚ) / 11529215046068469760000000000000000000)
def B13 : ℚ := ((-11070023055936970734245640366857694491 : ℚ) / 7205759403792793600000000000000000000)
def S13 : ℚ := ((-2250764319341729 : ℚ) / 2251799813685248)
def C13 : ℚ := ((-57008329056629711577348533909708127786048633614142950051317732961988828490066229 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s13_0 : ℚ := ((-2250764319341729 : ℚ) / 2251799813685248)
def c13_0 : ℚ := ((-57008329056629711577348533909708127786048633614142950051317732961988828490066229 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g13_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc13 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((5 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 3) (Fin.castSucc 1))
    (hshi : (((1 : ℚ) / 32) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 3))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A13 : ℝ) ≤ zval y 1 3 ∧ zval y 1 3 ≤ (B13 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 1) (j := 3)
      (by norm_num) (dbm := dbm) (slo := ((5 : ℚ) / 256)) (shi := ((1 : ℚ) / 32)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 1) (j := 3)
    (by norm_num) (slo := ((5 : ℚ) / 256)) (shi := ((1 : ℚ) / 32)) (by norm_num) hlo hhi
  have hAq : A13 ≤ ((((1 : ℚ) - 3) * LQ + Dq * ((5 : ℚ) / 256)) : ℚ) := by
    norm_num [A13, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((1 : ℚ) - 3) * Lq + DQ * ((1 : ℚ) / 32)) : ℚ) ≤ B13 := by
    norm_num [B13, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A13 : ℝ) ≤ (((((1 : ℚ) - 3) * LQ + Dq * ((5 : ℚ) / 256)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((1 : ℚ) - 3) * Lq + DQ * ((1 : ℚ) / 32)) : ℚ) : ℝ) ≤ (B13 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line13 : ∀ z ∈ Set.Icc (A13 : ℝ) (B13 : ℝ),
    (S13 : ℝ) * z + (C13 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A13 : ℝ)) (b := (B13 : ℝ)) (m := 0)
    (by norm_num [A13]; linarith [hpLo, hpHi])
    (by norm_num [B13]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-1540468547 : ℚ) / 1000000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A13, B13]
  · norm_num
  · norm_num [S13, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S13, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C13, S13, A13, B13, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse13 : S13 = ((-2250764319341729 : ℚ) / 2251799813685248) ∧ C13 = ((-57008329056629711577348533909708127786048633614142950051317732961988828490066229 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S13, C13, s13_0, c13_0, g13_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell13 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((5 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 3) (Fin.castSucc 1))
    (hshi : (((1 : ℚ) / 32) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 3))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S13 : ℝ) * zval y 1 3 + (C13 : ℝ) ≤ 1 - Real.cos (zval y 1 3) := by
  exact line13 (zval y 1 3) (arc13 y hslo hshi hcell)

/-! ### pair (1, 4), 1 line(s), branch `endpoint`, shift m = -1 -/

def A14 : ℚ := ((-242733007260126872773170648751490592881 : ℚ) / 115292150460684697600000000000000000000)
def B14 : ℚ := ((-30238444495099894902621475047761584311 : ℚ) / 14411518807585587200000000000000000000)
def S14 : ℚ := ((-1941728652737369 : ℚ) / 2251799813685248)
def C14 : ℚ := ((-15299394195754974517773254500993811744882218293371419302782607619683852183776671 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s14_0 : ℚ := ((-1941728652737369 : ℚ) / 2251799813685248)
def c14_0 : ℚ := ((-15299394195754974517773254500993811744882218293371419302782607619683852183776671 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g14_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc14 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((163 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 4) (Fin.castSucc 1))
    (hshi : (((21 : ℚ) / 64) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 4))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A14 : ℝ) ≤ zval y 1 4 ∧ zval y 1 4 ≤ (B14 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 1) (j := 4)
      (by norm_num) (dbm := dbm) (slo := ((163 : ℚ) / 512)) (shi := ((21 : ℚ) / 64)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 1) (j := 4)
    (by norm_num) (slo := ((163 : ℚ) / 512)) (shi := ((21 : ℚ) / 64)) (by norm_num) hlo hhi
  have hAq : A14 ≤ ((((1 : ℚ) - 4) * LQ + Dq * ((163 : ℚ) / 512)) : ℚ) := by
    norm_num [A14, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((1 : ℚ) - 4) * Lq + DQ * ((21 : ℚ) / 64)) : ℚ) ≤ B14 := by
    norm_num [B14, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A14 : ℝ) ≤ (((((1 : ℚ) - 4) * LQ + Dq * ((163 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((1 : ℚ) - 4) * Lq + DQ * ((21 : ℚ) / 64)) : ℚ) : ℝ) ≤ (B14 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line14 : ∀ z ∈ Set.Icc (A14 : ℝ) (B14 : ℝ),
    (S14 : ℝ) * z + (C14 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A14 : ℝ)) (b := (B14 : ℝ)) (m := -1)
    (by norm_num [A14]; linarith [hpLo, hpHi])
    (by norm_num [B14]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S14, A14, C14, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S14, B14, C14, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse14 : S14 = ((-1941728652737369 : ℚ) / 2251799813685248) ∧ C14 = ((-15299394195754974517773254500993811744882218293371419302782607619683852183776671 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S14, C14, s14_0, c14_0, g14_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell14 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((163 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 4) (Fin.castSucc 1))
    (hshi : (((21 : ℚ) / 64) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 4))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S14 : ℝ) * zval y 1 4 + (C14 : ℝ) ≤ 1 - Real.cos (zval y 1 4) := by
  exact line14 (zval y 1 4) (arc14 y hslo hshi hcell)

/-! ### pair (1, 5), 1 line(s), branch `endpoint`, shift m = -1 -/

def A15 : ℚ := ((-321387776132425452245173640035375011997 : ℚ) / 115292150460684697600000000000000000000)
def B15 : ℚ := ((-160116072156700710530602971234190644429 : ℚ) / 57646075230342348800000000000000000000)
def S15 : ℚ := ((-3164642270760419 : ℚ) / 9007199254740992)
def C15 : ℚ := ((95858443125288730079476335771636520546070611499852357643549789952500826933916809 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s15_0 : ℚ := ((-3164642270760419 : ℚ) / 9007199254740992)
def c15_0 : ℚ := ((95858443125288730079476335771636520546070611499852357643549789952500826933916809 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g15_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc15 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((231 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 5) (Fin.castSucc 1))
    (hshi : (((119 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 5))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A15 : ℝ) ≤ zval y 1 5 ∧ zval y 1 5 ≤ (B15 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 1) (j := 5)
      (by norm_num) (dbm := dbm) (slo := ((231 : ℚ) / 512)) (shi := ((119 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 1) (j := 5)
    (by norm_num) (slo := ((231 : ℚ) / 512)) (shi := ((119 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A15 ≤ ((((1 : ℚ) - 5) * LQ + Dq * ((231 : ℚ) / 512)) : ℚ) := by
    norm_num [A15, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((1 : ℚ) - 5) * Lq + DQ * ((119 : ℚ) / 256)) : ℚ) ≤ B15 := by
    norm_num [B15, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A15 : ℝ) ≤ (((((1 : ℚ) - 5) * LQ + Dq * ((231 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((1 : ℚ) - 5) * Lq + DQ * ((119 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B15 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line15 : ∀ z ∈ Set.Icc (A15 : ℝ) (B15 : ℝ),
    (S15 : ℝ) * z + (C15 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A15 : ℝ)) (b := (B15 : ℝ)) (m := -1)
    (by norm_num [A15]; linarith [hpLo, hpHi])
    (by norm_num [B15]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S15, A15, C15, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S15, B15, C15, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse15 : S15 = ((-3164642270760419 : ℚ) / 9007199254740992) ∧ C15 = ((95858443125288730079476335771636520546070611499852357643549789952500826933916809 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S15, C15, s15_0, c15_0, g15_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell15 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((231 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 5) (Fin.castSucc 1))
    (hshi : (((119 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 1) (Fin.castSucc 5))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S15 : ℝ) * zval y 1 5 + (C15 : ℝ) ≤ 1 - Real.cos (zval y 1 5) := by
  exact line15 (zval y 1 5) (arc15 y hslo hshi hcell)
#print axioms N11Formalization.Leaf4348Pairs.arc07
#print axioms N11Formalization.Leaf4348Pairs.line07
#print axioms N11Formalization.Leaf4348Pairs.collapse07
#print axioms N11Formalization.Leaf4348Pairs.cell07
#print axioms N11Formalization.Leaf4348Pairs.arc08
#print axioms N11Formalization.Leaf4348Pairs.line08
#print axioms N11Formalization.Leaf4348Pairs.collapse08
#print axioms N11Formalization.Leaf4348Pairs.cell08
#print axioms N11Formalization.Leaf4348Pairs.arc12
#print axioms N11Formalization.Leaf4348Pairs.line12
#print axioms N11Formalization.Leaf4348Pairs.collapse12
#print axioms N11Formalization.Leaf4348Pairs.cell12
#print axioms N11Formalization.Leaf4348Pairs.arc13
#print axioms N11Formalization.Leaf4348Pairs.line13
#print axioms N11Formalization.Leaf4348Pairs.collapse13
#print axioms N11Formalization.Leaf4348Pairs.cell13
#print axioms N11Formalization.Leaf4348Pairs.arc14
#print axioms N11Formalization.Leaf4348Pairs.line14
#print axioms N11Formalization.Leaf4348Pairs.collapse14
#print axioms N11Formalization.Leaf4348Pairs.cell14
#print axioms N11Formalization.Leaf4348Pairs.arc15
#print axioms N11Formalization.Leaf4348Pairs.line15
#print axioms N11Formalization.Leaf4348Pairs.collapse15
#print axioms N11Formalization.Leaf4348Pairs.cell15

end N11Formalization.Leaf4348Pairs
