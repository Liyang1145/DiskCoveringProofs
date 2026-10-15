import Mathlib
import N11Formalization.FlashCosineLeaf284Bridge
import N11Formalization.FlashCosineLeaf284Energy
import N11Formalization.PairTemplate

/-!
  **Leaf 4348 pair layer, stage 1 (pairs 1..6), template V5.**

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

/-! ### pair (0, 1), 1 line(s), branch `tangent`, shift m = 0 -/

def A01 : ℚ := ((-17811091045306357184650283713800064987 : ℚ) / 23058430092136939520000000000000000000)
def B01 : ℚ := ((-88064913668710596323945881926059639401 : ℚ) / 115292150460684697600000000000000000000)
def S01 : ℚ := ((-6245520038373475 : ℚ) / 9007199254740992)
def C01 : ℚ := ((-1259138778073360707488612706059767697818371874318065846169070483068041714747783 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s01_0 : ℚ := ((-6245520038373475 : ℚ) / 9007199254740992)
def c01_0 : ℚ := ((-1259138778073360707488612706059767697818371874318065846169070483068041714747783 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g01_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc01 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((5 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 1) (Fin.castSucc 0))
    (hshi : (((11 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 1))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A01 : ℝ) ≤ zval y 0 1 ∧ zval y 0 1 ≤ (B01 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 0) (j := 1)
      (by norm_num) (dbm := dbm) (slo := ((5 : ℚ) / 512)) (shi := ((11 : ℚ) / 512)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 0) (j := 1)
    (by norm_num) (slo := ((5 : ℚ) / 512)) (shi := ((11 : ℚ) / 512)) (by norm_num) hlo hhi
  have hAq : A01 ≤ ((((0 : ℚ) - 1) * LQ + Dq * ((5 : ℚ) / 512)) : ℚ) := by
    norm_num [A01, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((0 : ℚ) - 1) * Lq + DQ * ((11 : ℚ) / 512)) : ℚ) ≤ B01 := by
    norm_num [B01, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A01 : ℝ) ≤ (((((0 : ℚ) - 1) * LQ + Dq * ((5 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((0 : ℚ) - 1) * Lq + DQ * ((11 : ℚ) / 512)) : ℚ) : ℝ) ≤ (B01 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line01 : ∀ z ∈ Set.Icc (A01 : ℝ) (B01 : ℝ),
    (S01 : ℝ) * z + (C01 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A01 : ℝ)) (b := (B01 : ℝ)) (m := 0)
    (by norm_num [A01]; linarith [hpLo, hpHi])
    (by norm_num [B01]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-3830929611 : ℚ) / 5000000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A01, B01]
  · norm_num
  · norm_num [S01, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S01, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C01, S01, A01, B01, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse01 : S01 = ((-6245520038373475 : ℚ) / 9007199254740992) ∧ C01 = ((-1259138778073360707488612706059767697818371874318065846169070483068041714747783 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S01, C01, s01_0, c01_0, g01_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell01 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((5 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 1) (Fin.castSucc 0))
    (hshi : (((11 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 1))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S01 : ℝ) * zval y 0 1 + (C01 : ℝ) ≤ 1 - Real.cos (zval y 0 1) := by
  exact line01 (zval y 0 1) (arc01 y hslo hshi hcell)

/-! ### pair (0, 2), 1 line(s), branch `tangent`, shift m = 0 -/

def A02 : ℚ := ((-17811091045306357184650283713800064987 : ℚ) / 11529215046068469760000000000000000000)
def B02 : ℚ := ((-44445182483342939453655641803698083473 : ℚ) / 28823037615171174400000000000000000000)
def S02 : ℚ := ((-9004087081540635 : ℚ) / 9007199254740992)
def C02 : ℚ := ((-57025963965307120972486324526957679663961780802601117810275723760979241269309363 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s02_0 : ℚ := ((-9004087081540635 : ℚ) / 9007199254740992)
def c02_0 : ℚ := ((-57025963965307120972486324526957679663961780802601117810275723760979241269309363 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g02_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc02 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((5 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 2) (Fin.castSucc 0))
    (hshi : (((3 : ℚ) / 128) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 2))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A02 : ℝ) ≤ zval y 0 2 ∧ zval y 0 2 ≤ (B02 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 0) (j := 2)
      (by norm_num) (dbm := dbm) (slo := ((5 : ℚ) / 256)) (shi := ((3 : ℚ) / 128)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 0) (j := 2)
    (by norm_num) (slo := ((5 : ℚ) / 256)) (shi := ((3 : ℚ) / 128)) (by norm_num) hlo hhi
  have hAq : A02 ≤ ((((0 : ℚ) - 2) * LQ + Dq * ((5 : ℚ) / 256)) : ℚ) := by
    norm_num [A02, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((0 : ℚ) - 2) * Lq + DQ * ((3 : ℚ) / 128)) : ℚ) ≤ B02 := by
    norm_num [B02, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A02 : ℝ) ≤ (((((0 : ℚ) - 2) * LQ + Dq * ((5 : ℚ) / 256)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((0 : ℚ) - 2) * Lq + DQ * ((3 : ℚ) / 128)) : ℚ) : ℝ) ≤ (B02 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line02 : ∀ z ∈ Set.Icc (A02 : ℝ) (B02 : ℝ),
    (S02 : ℝ) * z + (C02 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A02 : ℝ)) (b := (B02 : ℝ)) (m := 0)
    (by norm_num [A02]; linarith [hpLo, hpHi])
    (by norm_num [B02]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-772253953 : ℚ) / 500000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A02, B02]
  · norm_num
  · norm_num [S02, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S02, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C02, S02, A02, B02, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse02 : S02 = ((-9004087081540635 : ℚ) / 9007199254740992) ∧ C02 = ((-57025963965307120972486324526957679663961780802601117810275723760979241269309363 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S02, C02, s02_0, c02_0, g02_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell02 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((5 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 2) (Fin.castSucc 0))
    (hshi : (((3 : ℚ) / 128) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 2))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S02 : ℝ) * zval y 0 2 + (C02 : ℝ) ≤ 1 - Real.cos (zval y 0 2) := by
  exact line02 (zval y 0 2) (arc02 y hslo hshi hcell)

/-! ### pair (0, 3), 1 line(s), branch `endpoint`, shift m = -1 -/

def A03 : ℚ := ((-266175824122049338107730595965561364727 : ℚ) / 115292150460684697600000000000000000000)
def B03 : ℚ := ((-133005366930838705327620764738559639401 : ℚ) / 57646075230342348800000000000000000000)
def S03 : ℚ := ((-6668542934247825 : ℚ) / 9007199254740992)
def C03 : ℚ := ((-4565478503151384699145695636383799957305282171429951777682963924560204839335931 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s03_0 : ℚ := ((-6668542934247825 : ℚ) / 9007199254740992)
def c03_0 : ℚ := ((-4565478503151384699145695636383799957305282171429951777682963924560204839335931 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g03_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc03 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((21 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 3) (Fin.castSucc 0))
    (hshi : (((11 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 3))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A03 : ℝ) ≤ zval y 0 3 ∧ zval y 0 3 ≤ (B03 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 0) (j := 3)
      (by norm_num) (dbm := dbm) (slo := ((21 : ℚ) / 512)) (shi := ((11 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 0) (j := 3)
    (by norm_num) (slo := ((21 : ℚ) / 512)) (shi := ((11 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A03 ≤ ((((0 : ℚ) - 3) * LQ + Dq * ((21 : ℚ) / 512)) : ℚ) := by
    norm_num [A03, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((0 : ℚ) - 3) * Lq + DQ * ((11 : ℚ) / 256)) : ℚ) ≤ B03 := by
    norm_num [B03, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A03 : ℝ) ≤ (((((0 : ℚ) - 3) * LQ + Dq * ((21 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((0 : ℚ) - 3) * Lq + DQ * ((11 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B03 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line03 : ∀ z ∈ Set.Icc (A03 : ℝ) (B03 : ℝ),
    (S03 : ℝ) * z + (C03 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A03 : ℝ)) (b := (B03 : ℝ)) (m := -1)
    (by norm_num [A03]; linarith [hpLo, hpHi])
    (by norm_num [B03]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S03, A03, C03, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S03, B03, C03, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse03 : S03 = ((-6668542934247825 : ℚ) / 9007199254740992) ∧ C03 = ((-4565478503151384699145695636383799957305282171429951777682963924560204839335931 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S03, C03, s03_0, c03_0, g03_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell03 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((21 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 3) (Fin.castSucc 0))
    (hshi : (((11 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 3))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S03 : ℝ) * zval y 0 3 + (C03 : ℝ) ≤ 1 - Real.cos (zval y 0 3) := by
  exact line03 (zval y 0 3) (arc03 y hslo hshi hcell)

/-! ### pair (0, 4), 1 line(s), branch `endpoint`, shift m = -1 -/

def A04 : ℚ := ((-330963011188703642311402350869291242751 : ℚ) / 115292150460684697600000000000000000000)
def B04 : ℚ := ((-165398960463742519064141541994744420717 : ℚ) / 57646075230342348800000000000000000000)
def S04 : ℚ := ((-2416928086050817 : ℚ) / 9007199254740992)
def C04 : ℚ := ((5966145677898977246070040229693723877136259205871516177702583163182897784341741 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s04_0 : ℚ := ((-2416928086050817 : ℚ) / 9007199254740992)
def c04_0 : ℚ := ((5966145677898977246070040229693723877136259205871516177702583163182897784341741 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g04_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc04 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((173 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 4) (Fin.castSucc 0))
    (hshi : (((87 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 4))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A04 : ℝ) ≤ zval y 0 4 ∧ zval y 0 4 ≤ (B04 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 0) (j := 4)
      (by norm_num) (dbm := dbm) (slo := ((173 : ℚ) / 512)) (shi := ((87 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 0) (j := 4)
    (by norm_num) (slo := ((173 : ℚ) / 512)) (shi := ((87 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A04 ≤ ((((0 : ℚ) - 4) * LQ + Dq * ((173 : ℚ) / 512)) : ℚ) := by
    norm_num [A04, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((0 : ℚ) - 4) * Lq + DQ * ((87 : ℚ) / 256)) : ℚ) ≤ B04 := by
    norm_num [B04, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A04 : ℝ) ≤ (((((0 : ℚ) - 4) * LQ + Dq * ((173 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((0 : ℚ) - 4) * Lq + DQ * ((87 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B04 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line04 : ∀ z ∈ Set.Icc (A04 : ℝ) (B04 : ℝ),
    (S04 : ℝ) * z + (C04 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A04 : ℝ)) (b := (B04 : ℝ)) (m := -1)
    (by norm_num [A04]; linarith [hpLo, hpHi])
    (by norm_num [B04]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S04, A04, C04, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S04, B04, C04, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse04 : S04 = ((-2416928086050817 : ℚ) / 9007199254740992) ∧ C04 = ((5966145677898977246070040229693723877136259205871516177702583163182897784341741 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S04, C04, s04_0, c04_0, g04_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell04 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((173 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 4) (Fin.castSucc 0))
    (hshi : (((87 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 4))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S04 : ℝ) * zval y 0 4 + (C04 : ℝ) ≤ 1 - Real.cos (zval y 0 4) := by
  exact line04 (zval y 0 4) (arc04 y hslo hshi hcell)

/-! ### pair (0, 5), 2 line(s), branch `endpoint`, shift m = -1 -/

def A05 : ℚ := ((-204726344900705609253200699431467863427 : ℚ) / 57646075230342348800000000000000000000)
def B05 : ℚ := ((-102280627320021824992129306518944363951 : ℚ) / 28823037615171174400000000000000000000)
def S05 : ℚ := ((667953085114963349848125 : ℚ) / 1758865271155134927208448)
def C05 : ℚ := ((102038549694827869402728589886848912360162122850420179897550510921453901555369198682736057 : ℚ) / 31243723540000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s05_0 : ℚ := (0 : ℚ)
def c05_0 : ℚ := ((19171832684871432660717738236956326078809538388020541240895034724405837537279783 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g05_0 : ℚ := ((136791229 : ℚ) / 3124372354)
def s05_1 : ℚ := ((223576551453465 : ℚ) / 562949953421312)
def c05_1 : ℚ := ((16638211144757104532530187017317456659275991248170737319135274370416426891817099 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g05_1 : ℚ := ((2987581125 : ℚ) / 3124372354)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc05 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((121 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 5) (Fin.castSucc 0))
    (hshi : (((61 : ℚ) / 128) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 5))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A05 : ℝ) ≤ zval y 0 5 ∧ zval y 0 5 ≤ (B05 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 0) (j := 5)
      (by norm_num) (dbm := dbm) (slo := ((121 : ℚ) / 256)) (shi := ((61 : ℚ) / 128)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 0) (j := 5)
    (by norm_num) (slo := ((121 : ℚ) / 256)) (shi := ((61 : ℚ) / 128)) (by norm_num) hlo hhi
  have hAq : A05 ≤ ((((0 : ℚ) - 5) * LQ + Dq * ((121 : ℚ) / 256)) : ℚ) := by
    norm_num [A05, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((0 : ℚ) - 5) * Lq + DQ * ((61 : ℚ) / 128)) : ℚ) ≤ B05 := by
    norm_num [B05, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A05 : ℝ) ≤ (((((0 : ℚ) - 5) * LQ + Dq * ((121 : ℚ) / 256)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((0 : ℚ) - 5) * Lq + DQ * ((61 : ℚ) / 128)) : ℚ) : ℝ) ≤ (B05 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line05 : ∀ z ∈ Set.Icc (A05 : ℝ) (B05 : ℝ),
    (S05 : ℝ) * z + (C05 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A05 : ℝ)) (b := (B05 : ℝ)) (m := -1)
    (by norm_num [A05]; linarith [hpLo, hpHi])
    (by norm_num [B05]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S05, A05, C05, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S05, B05, C05, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse05 : S05 = ((667953085114963349848125 : ℚ) / 1758865271155134927208448) ∧ C05 = ((102038549694827869402728589886848912360162122850420179897550510921453901555369198682736057 : ℚ) / 31243723540000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S05, C05, s05_0, s05_1, c05_0, c05_1, g05_0, g05_1]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell05 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((121 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 5) (Fin.castSucc 0))
    (hshi : (((61 : ℚ) / 128) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 5))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S05 : ℝ) * zval y 0 5 + (C05 : ℝ) ≤ 1 - Real.cos (zval y 0 5) := by
  exact line05 (zval y 0 5) (arc05 y hslo hshi hcell)

/-! ### pair (0, 6), 1 line(s), branch `endpoint`, shift m = -1 -/

def A06 : ℚ := ((-247685715047856971083288947458688643271 : ℚ) / 57646075230342348800000000000000000000)
def B06 : ℚ := ((-123760312393515540393928265907590530897 : ℚ) / 28823037615171174400000000000000000000)
def S06 : ℚ := ((8234773595050903 : ℚ) / 9007199254740992)
def C06 : ℚ := ((10664101013830050831238708388085877847903651005773284964410316033254649016751931 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s06_0 : ℚ := ((8234773595050903 : ℚ) / 9007199254740992)
def c06_0 : ℚ := ((10664101013830050831238708388085877847903651005773284964410316033254649016751931 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g06_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc06 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((133 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 0))
    (hshi : (((67 : ℚ) / 128) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A06 : ℝ) ≤ zval y 0 6 ∧ zval y 0 6 ≤ (B06 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 0) (j := 6)
      (by norm_num) (dbm := dbm) (slo := ((133 : ℚ) / 256)) (shi := ((67 : ℚ) / 128)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 0) (j := 6)
    (by norm_num) (slo := ((133 : ℚ) / 256)) (shi := ((67 : ℚ) / 128)) (by norm_num) hlo hhi
  have hAq : A06 ≤ ((((0 : ℚ) - 6) * LQ + Dq * ((133 : ℚ) / 256)) : ℚ) := by
    norm_num [A06, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((0 : ℚ) - 6) * Lq + DQ * ((67 : ℚ) / 128)) : ℚ) ≤ B06 := by
    norm_num [B06, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A06 : ℝ) ≤ (((((0 : ℚ) - 6) * LQ + Dq * ((133 : ℚ) / 256)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((0 : ℚ) - 6) * Lq + DQ * ((67 : ℚ) / 128)) : ℚ) : ℝ) ≤ (B06 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line06 : ∀ z ∈ Set.Icc (A06 : ℝ) (B06 : ℝ),
    (S06 : ℝ) * z + (C06 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A06 : ℝ)) (b := (B06 : ℝ)) (m := -1)
    (by norm_num [A06]; linarith [hpLo, hpHi])
    (by norm_num [B06]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S06, A06, C06, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S06, B06, C06, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse06 : S06 = ((8234773595050903 : ℚ) / 9007199254740992) ∧ C06 = ((10664101013830050831238708388085877847903651005773284964410316033254649016751931 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S06, C06, s06_0, c06_0, g06_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell06 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((133 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 0))
    (hshi : (((67 : ℚ) / 128) : ℚ) = dbm (Fin.castSucc 0) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S06 : ℝ) * zval y 0 6 + (C06 : ℝ) ≤ 1 - Real.cos (zval y 0 6) := by
  exact line06 (zval y 0 6) (arc06 y hslo hshi hcell)
#print axioms N11Formalization.Leaf4348Pairs.arc01
#print axioms N11Formalization.Leaf4348Pairs.line01
#print axioms N11Formalization.Leaf4348Pairs.collapse01
#print axioms N11Formalization.Leaf4348Pairs.cell01
#print axioms N11Formalization.Leaf4348Pairs.arc02
#print axioms N11Formalization.Leaf4348Pairs.line02
#print axioms N11Formalization.Leaf4348Pairs.collapse02
#print axioms N11Formalization.Leaf4348Pairs.cell02
#print axioms N11Formalization.Leaf4348Pairs.arc03
#print axioms N11Formalization.Leaf4348Pairs.line03
#print axioms N11Formalization.Leaf4348Pairs.collapse03
#print axioms N11Formalization.Leaf4348Pairs.cell03
#print axioms N11Formalization.Leaf4348Pairs.arc04
#print axioms N11Formalization.Leaf4348Pairs.line04
#print axioms N11Formalization.Leaf4348Pairs.collapse04
#print axioms N11Formalization.Leaf4348Pairs.cell04
#print axioms N11Formalization.Leaf4348Pairs.arc05
#print axioms N11Formalization.Leaf4348Pairs.line05
#print axioms N11Formalization.Leaf4348Pairs.collapse05
#print axioms N11Formalization.Leaf4348Pairs.cell05
#print axioms N11Formalization.Leaf4348Pairs.arc06
#print axioms N11Formalization.Leaf4348Pairs.line06
#print axioms N11Formalization.Leaf4348Pairs.collapse06
#print axioms N11Formalization.Leaf4348Pairs.cell06

end N11Formalization.Leaf4348Pairs
