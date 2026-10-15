import Mathlib
import N11Formalization.FlashCosineLeaf284Bridge
import N11Formalization.FlashCosineLeaf284Energy
import N11Formalization.PairTemplate

/-!
  **Leaf 4348 pair layer, stage 6 (pairs 31..36), template V5.**

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

/-! ### pair (5, 6), 1 line(s), branch `tangent`, shift m = 0 -/

def A56 : ℚ := ((-43124460406742365107092191317460714857 : ℚ) / 57646075230342348800000000000000000000)
def B56 : ℚ := ((-42794279887392374286924838441025028383 : ℚ) / 57646075230342348800000000000000000000)
def S56 : ℚ := ((-381305933927761 : ℚ) / 562949953421312)
def C56 : ℚ := ((-23970305351379034872165207887583909369549660470611491581154029576302233675913243 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s56_0 : ℚ := ((-381305933927761 : ℚ) / 562949953421312)
def c56_0 : ℚ := ((-23970305351379034872165207887583909369549660470611491581154029576302233675913243 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g56_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc56 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((11 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 5))
    (hshi : (((13 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 5) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A56 : ℝ) ≤ zval y 5 6 ∧ zval y 5 6 ≤ (B56 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 5) (j := 6)
      (by norm_num) (dbm := dbm) (slo := ((11 : ℚ) / 256)) (shi := ((13 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 5) (j := 6)
    (by norm_num) (slo := ((11 : ℚ) / 256)) (shi := ((13 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A56 ≤ ((((5 : ℚ) - 6) * LQ + Dq * ((11 : ℚ) / 256)) : ℚ) := by
    norm_num [A56, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((5 : ℚ) - 6) * Lq + DQ * ((13 : ℚ) / 256)) : ℚ) ≤ B56 := by
    norm_num [B56, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A56 : ℝ) ≤ (((((5 : ℚ) - 6) * LQ + Dq * ((11 : ℚ) / 256)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((5 : ℚ) - 6) * Lq + DQ * ((13 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B56 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line56 : ∀ z ∈ Set.Icc (A56 : ℝ) (B56 : ℝ),
    (S56 : ℝ) * z + (C56 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A56 : ℝ)) (b := (B56 : ℝ)) (m := 0)
    (by norm_num [A56]; linarith [hpLo, hpHi])
    (by norm_num [B56]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-1860336473 : ℚ) / 2500000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A56, B56]
  · norm_num
  · norm_num [S56, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S56, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C56, S56, A56, B56, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse56 : S56 = ((-381305933927761 : ℚ) / 562949953421312) ∧ C56 = ((-23970305351379034872165207887583909369549660470611491581154029576302233675913243 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S56, C56, s56_0, c56_0, g56_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell56 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((11 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 5))
    (hshi : (((13 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 5) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S56 : ℝ) * zval y 5 6 + (C56 : ℝ) ≤ 1 - Real.cos (zval y 5 6) := by
  exact line56 (zval y 5 6) (arc56 y hslo hshi hcell)

/-! ### pair (5, 7), 1 line(s), branch `tangent`, shift m = 0 -/

def A57 : ℚ := ((-172002570848196450597356935399123054389 : ℚ) / 115292150460684697600000000000000000000)
def B57 : ℚ := ((-3430146001375192203620910288732694491 : ℚ) / 2305843009213693952000000000000000000)
def S57 : ℚ := ((-8977230819621121 : ℚ) / 9007199254740992)
def C57 : ℚ := ((-28287549956539534252204279476020899777208848537211101015218498574425047001838267 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s57_0 : ℚ := ((-8977230819621121 : ℚ) / 9007199254740992)
def c57_0 : ℚ := ((-28287549956539534252204279476020899777208848537211101015218498574425047001838267 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g57_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc57 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((47 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 5))
    (hshi : (((25 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 5) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A57 : ℝ) ≤ zval y 5 7 ∧ zval y 5 7 ≤ (B57 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 5) (j := 7)
      (by norm_num) (dbm := dbm) (slo := ((47 : ℚ) / 512)) (shi := ((25 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 5) (j := 7)
    (by norm_num) (slo := ((47 : ℚ) / 512)) (shi := ((25 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A57 ≤ ((((5 : ℚ) - 7) * LQ + Dq * ((47 : ℚ) / 512)) : ℚ) := by
    norm_num [A57, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((5 : ℚ) - 7) * Lq + DQ * ((25 : ℚ) / 256)) : ℚ) ≤ B57 := by
    norm_num [B57, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A57 : ℝ) ≤ (((((5 : ℚ) - 7) * LQ + Dq * ((47 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((5 : ℚ) - 7) * Lq + DQ * ((25 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B57 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line57 : ∀ z ∈ Set.Icc (A57 : ℝ) (B57 : ℝ),
    (S57 : ℝ) * z + (C57 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A57 : ℝ)) (b := (B57 : ℝ)) (m := 0)
    (by norm_num [A57]; linarith [hpLo, hpHi])
    (by norm_num [B57]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-3722999049 : ℚ) / 2500000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A57, B57]
  · norm_num
  · norm_num [S57, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S57, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C57, S57, A57, B57, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse57 : S57 = ((-8977230819621121 : ℚ) / 9007199254740992) ∧ C57 = ((-28287549956539534252204279476020899777208848537211101015218498574425047001838267 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S57, C57, s57_0, c57_0, g57_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell57 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((47 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 5))
    (hshi : (((25 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 5) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S57 : ℝ) * zval y 5 7 + (C57 : ℝ) ≤ 1 - Real.cos (zval y 5 7) := by
  exact line57 (zval y 5 7) (arc57 y hslo hshi hcell)

/-! ### pair (5, 8), 1 line(s), branch `endpoint`, shift m = -1 -/

def A58 : ℚ := ((-62623062365226006698088995848191884623 : ℚ) / 28823037615171174400000000000000000000)
def B58 : ℚ := ((-125081034470275992527312908597728974969 : ℚ) / 57646075230342348800000000000000000000)
def S58 : ℚ := ((-7431692438397999 : ℚ) / 9007199254740992)
def C58 : ℚ := ((-22644651020557437641190852829546870026199542742353182699078931370730293130966717 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s58_0 : ℚ := ((-7431692438397999 : ℚ) / 9007199254740992)
def c58_0 : ℚ := ((-22644651020557437641190852829546870026199542742353182699078931370730293130966717 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g58_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc58 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((29 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 5))
    (hshi : (((59 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 5) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A58 : ℝ) ≤ zval y 5 8 ∧ zval y 5 8 ≤ (B58 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 5) (j := 8)
      (by norm_num) (dbm := dbm) (slo := ((29 : ℚ) / 128)) (shi := ((59 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 5) (j := 8)
    (by norm_num) (slo := ((29 : ℚ) / 128)) (shi := ((59 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A58 ≤ ((((5 : ℚ) - 8) * LQ + Dq * ((29 : ℚ) / 128)) : ℚ) := by
    norm_num [A58, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((5 : ℚ) - 8) * Lq + DQ * ((59 : ℚ) / 256)) : ℚ) ≤ B58 := by
    norm_num [B58, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A58 : ℝ) ≤ (((((5 : ℚ) - 8) * LQ + Dq * ((29 : ℚ) / 128)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((5 : ℚ) - 8) * Lq + DQ * ((59 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B58 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line58 : ∀ z ∈ Set.Icc (A58 : ℝ) (B58 : ℝ),
    (S58 : ℝ) * z + (C58 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A58 : ℝ)) (b := (B58 : ℝ)) (m := -1)
    (by norm_num [A58]; linarith [hpLo, hpHi])
    (by norm_num [B58]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S58, A58, C58, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S58, B58, C58, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse58 : S58 = ((-7431692438397999 : ℚ) / 9007199254740992) ∧ C58 = ((-22644651020557437641190852829546870026199542742353182699078931370730293130966717 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S58, C58, s58_0, c58_0, g58_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell58 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((29 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 5))
    (hshi : (((59 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 5) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S58 : ℝ) * zval y 5 8 + (C58 : ℝ) ≤ 1 - Real.cos (zval y 5 8) := by
  exact line58 (zval y 5 8) (arc58 y hslo hshi hcell)

/-! ### pair (6, 7), 1 line(s), branch `tangent`, shift m = 0 -/

def A67 : ℚ := ((-86083830553893726937180439344681494701 : ℚ) / 115292150460684697600000000000000000000)
def B67 : ℚ := ((-42794279887392374286924838441025028383 : ℚ) / 57646075230342348800000000000000000000)
def S67 : ℚ := ((-3050688630696529 : ℚ) / 4503599627370496)
def C67 : ℚ := ((-5993572561695598909755535472978117145410554507219380455964652736140492137780929 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s67_0 : ℚ := ((-3050688630696529 : ℚ) / 4503599627370496)
def c67_0 : ℚ := ((-5993572561695598909755535472978117145410554507219380455964652736140492137780929 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g67_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc67 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((23 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 6))
    (hshi : (((13 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 6) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A67 : ℝ) ≤ zval y 6 7 ∧ zval y 6 7 ≤ (B67 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 6) (j := 7)
      (by norm_num) (dbm := dbm) (slo := ((23 : ℚ) / 512)) (shi := ((13 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 6) (j := 7)
    (by norm_num) (slo := ((23 : ℚ) / 512)) (shi := ((13 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A67 ≤ ((((6 : ℚ) - 7) * LQ + Dq * ((23 : ℚ) / 512)) : ℚ) := by
    norm_num [A67, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((6 : ℚ) - 7) * Lq + DQ * ((13 : ℚ) / 256)) : ℚ) ≤ B67 := by
    norm_num [B67, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A67 : ℝ) ≤ (((((6 : ℚ) - 7) * LQ + Dq * ((23 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((6 : ℚ) - 7) * Lq + DQ * ((13 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B67 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line67 : ∀ z ∈ Set.Icc (A67 : ℝ) (B67 : ℝ),
    (S67 : ℝ) * z + (C67 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A67 : ℝ)) (b := (B67 : ℝ)) (m := 0)
    (by norm_num [A67]; linarith [hpLo, hpHi])
    (by norm_num [B67]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-3721036897 : ℚ) / 5000000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A67, B67]
  · norm_num
  · norm_num [S67, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S67, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C67, S67, A67, B67, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse67 : S67 = ((-3050688630696529 : ℚ) / 4503599627370496) ∧ C67 = ((-5993572561695598909755535472978117145410554507219380455964652736140492137780929 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S67, C67, s67_0, c67_0, g67_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell67 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((23 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 6))
    (hshi : (((13 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 6) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S67 : ℝ) * zval y 6 7 + (C67 : ℝ) ≤ 1 - Real.cos (zval y 6 7) := by
  exact line67 (zval y 6 7) (arc67 y hslo hshi hcell)

/-! ### pair (6, 8), 1 line(s), branch `tangent`, shift m = 0 -/

def A68 : ℚ := ((-41143377291650325783044871834581494701 : ℚ) / 28823037615171174400000000000000000000)
def B68 : ℚ := ((-82121664323288561723714989820436641077 : ℚ) / 57646075230342348800000000000000000000)
def S68 : ℚ := ((-1114178351265653 : ℚ) / 1125899906842624)
def C68 : ℚ := ((-1735765792190739325910416261010483926885671605462717040351495059407566116595473 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000)
def s68_0 : ℚ := ((-1114178351265653 : ℚ) / 1125899906842624)
def c68_0 : ℚ := ((-1735765792190739325910416261010483926885671605462717040351495059407566116595473 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000)
def g68_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc68 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((23 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 6))
    (hshi : (((47 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 6) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A68 : ℝ) ≤ zval y 6 8 ∧ zval y 6 8 ≤ (B68 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 6) (j := 8)
      (by norm_num) (dbm := dbm) (slo := ((23 : ℚ) / 128)) (shi := ((47 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 6) (j := 8)
    (by norm_num) (slo := ((23 : ℚ) / 128)) (shi := ((47 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A68 ≤ ((((6 : ℚ) - 8) * LQ + Dq * ((23 : ℚ) / 128)) : ℚ) := by
    norm_num [A68, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((6 : ℚ) - 8) * Lq + DQ * ((47 : ℚ) / 256)) : ℚ) ≤ B68 := by
    norm_num [B68, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A68 : ℝ) ≤ (((((6 : ℚ) - 8) * LQ + Dq * ((23 : ℚ) / 128)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((6 : ℚ) - 8) * Lq + DQ * ((47 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B68 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line68 : ∀ z ∈ Set.Icc (A68 : ℝ) (B68 : ℝ),
    (S68 : ℝ) * z + (C68 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A68 : ℝ)) (b := (B68 : ℝ)) (m := 0)
    (by norm_num [A68]; linarith [hpLo, hpHi])
    (by norm_num [B68]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-14263737021 : ℚ) / 10000000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A68, B68]
  · norm_num
  · norm_num [S68, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S68, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C68, S68, A68, B68, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse68 : S68 = ((-1114178351265653 : ℚ) / 1125899906842624) ∧ C68 = ((-1735765792190739325910416261010483926885671605462717040351495059407566116595473 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S68, C68, s68_0, c68_0, g68_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell68 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((23 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 6))
    (hshi : (((47 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 6) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S68 : ℝ) * zval y 6 8 + (C68 : ℝ) ≤ 1 - Real.cos (zval y 6 8) := by
  exact line68 (zval y 6 8) (arc68 y hslo hshi hcell)

/-! ### pair (7, 8), 1 line(s), branch `tangent`, shift m = 0 -/

def A78 : ℚ := ((-78819859131889582749006934574124354129 : ℚ) / 115292150460684697600000000000000000000)
def B78 : ℚ := ((-78489678612197318356907222422555919879 : ℚ) / 115292150460684697600000000000000000000)
def S78 : ℚ := ((-5676704924291901 : ℚ) / 9007199254740992)
def C78 : ℚ := ((-2576723076224223904757316165298520643598804790492769144471787809407524209794151 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000)
def s78_0 : ℚ := ((-5676704924291901 : ℚ) / 9007199254740992)
def c78_0 : ℚ := ((-2576723076224223904757316165298520643598804790492769144471787809407524209794151 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000)
def g78_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc78 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((67 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 7))
    (hshi : (((69 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 7) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A78 : ℝ) ≤ zval y 7 8 ∧ zval y 7 8 ≤ (B78 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 7) (j := 8)
      (by norm_num) (dbm := dbm) (slo := ((67 : ℚ) / 512)) (shi := ((69 : ℚ) / 512)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 7) (j := 8)
    (by norm_num) (slo := ((67 : ℚ) / 512)) (shi := ((69 : ℚ) / 512)) (by norm_num) hlo hhi
  have hAq : A78 ≤ ((((7 : ℚ) - 8) * LQ + Dq * ((67 : ℚ) / 512)) : ℚ) := by
    norm_num [A78, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((7 : ℚ) - 8) * Lq + DQ * ((69 : ℚ) / 512)) : ℚ) ≤ B78 := by
    norm_num [B78, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A78 : ℝ) ≤ (((((7 : ℚ) - 8) * LQ + Dq * ((67 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((7 : ℚ) - 8) * Lq + DQ * ((69 : ℚ) / 512)) : ℚ) : ℝ) ≤ (B78 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line78 : ∀ z ∈ Set.Icc (A78 : ℝ) (B78 : ℝ),
    (S78 : ℝ) * z + (C78 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A78 : ℝ)) (b := (B78 : ℝ)) (m := 0)
    (by norm_num [A78]; linarith [hpLo, hpHi])
    (by norm_num [B78]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-6818633879 : ℚ) / 10000000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A78, B78]
  · norm_num
  · norm_num [S78, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S78, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C78, S78, A78, B78, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse78 : S78 = ((-5676704924291901 : ℚ) / 9007199254740992) ∧ C78 = ((-2576723076224223904757316165298520643598804790492769144471787809407524209794151 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S78, C78, s78_0, c78_0, g78_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell78 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((67 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 7))
    (hshi : (((69 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 7) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S78 : ℝ) * zval y 7 8 + (C78 : ℝ) ≤ 1 - Real.cos (zval y 7 8) := by
  exact line78 (zval y 7 8) (arc78 y hslo hshi hcell)
#print axioms N11Formalization.Leaf4348Pairs.arc56
#print axioms N11Formalization.Leaf4348Pairs.line56
#print axioms N11Formalization.Leaf4348Pairs.collapse56
#print axioms N11Formalization.Leaf4348Pairs.cell56
#print axioms N11Formalization.Leaf4348Pairs.arc57
#print axioms N11Formalization.Leaf4348Pairs.line57
#print axioms N11Formalization.Leaf4348Pairs.collapse57
#print axioms N11Formalization.Leaf4348Pairs.cell57
#print axioms N11Formalization.Leaf4348Pairs.arc58
#print axioms N11Formalization.Leaf4348Pairs.line58
#print axioms N11Formalization.Leaf4348Pairs.collapse58
#print axioms N11Formalization.Leaf4348Pairs.cell58
#print axioms N11Formalization.Leaf4348Pairs.arc67
#print axioms N11Formalization.Leaf4348Pairs.line67
#print axioms N11Formalization.Leaf4348Pairs.collapse67
#print axioms N11Formalization.Leaf4348Pairs.cell67
#print axioms N11Formalization.Leaf4348Pairs.arc68
#print axioms N11Formalization.Leaf4348Pairs.line68
#print axioms N11Formalization.Leaf4348Pairs.collapse68
#print axioms N11Formalization.Leaf4348Pairs.cell68
#print axioms N11Formalization.Leaf4348Pairs.arc78
#print axioms N11Formalization.Leaf4348Pairs.line78
#print axioms N11Formalization.Leaf4348Pairs.collapse78
#print axioms N11Formalization.Leaf4348Pairs.cell78

end N11Formalization.Leaf4348Pairs
