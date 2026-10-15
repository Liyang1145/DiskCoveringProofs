import Mathlib
import N11Formalization.FlashCosineLeaf284Bridge
import N11Formalization.FlashCosineLeaf284Energy
import N11Formalization.PairTemplate

/-!
  **Leaf 4348 pair layer, stage 5 (pairs 25..30), template V5.**

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

/-! ### pair (3, 7), 1 line(s), branch `endpoint`, shift m = -1 -/

def A37 : ℚ := ((-31494925600837632444201985171601754649 : ℚ) / 11529215046068469760000000000000000000)
def B37 : ℚ := ((-314784165746764556010994291371560207061 : ℚ) / 115292150460684697600000000000000000000)
def S37 : ℚ := ((-7189945586754613 : ℚ) / 18014398509481984)
def C37 : ℚ := ((16537631595304219820798106778161584921523085536633479336588163136679475428723053 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s37_0 : ℚ := ((-7189945586754613 : ℚ) / 18014398509481984)
def c37_0 : ℚ := ((16537631595304219820798106778161584921523085536633479336588163136679475428723053 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g37_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc37 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((135 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 3))
    (hshi : (((271 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 3) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A37 : ℝ) ≤ zval y 3 7 ∧ zval y 3 7 ≤ (B37 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 3) (j := 7)
      (by norm_num) (dbm := dbm) (slo := ((135 : ℚ) / 256)) (shi := ((271 : ℚ) / 512)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 3) (j := 7)
    (by norm_num) (slo := ((135 : ℚ) / 256)) (shi := ((271 : ℚ) / 512)) (by norm_num) hlo hhi
  have hAq : A37 ≤ ((((3 : ℚ) - 7) * LQ + Dq * ((135 : ℚ) / 256)) : ℚ) := by
    norm_num [A37, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((3 : ℚ) - 7) * Lq + DQ * ((271 : ℚ) / 512)) : ℚ) ≤ B37 := by
    norm_num [B37, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A37 : ℝ) ≤ (((((3 : ℚ) - 7) * LQ + Dq * ((135 : ℚ) / 256)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((3 : ℚ) - 7) * Lq + DQ * ((271 : ℚ) / 512)) : ℚ) : ℝ) ≤ (B37 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line37 : ∀ z ∈ Set.Icc (A37 : ℝ) (B37 : ℝ),
    (S37 : ℝ) * z + (C37 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A37 : ℝ)) (b := (B37 : ℝ)) (m := -1)
    (by norm_num [A37]; linarith [hpLo, hpHi])
    (by norm_num [B37]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S37, A37, C37, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S37, B37, C37, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse37 : S37 = ((-7189945586754613 : ℚ) / 18014398509481984) ∧ C37 = ((16537631595304219820798106778161584921523085536633479336588163136679475428723053 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S37, C37, s37_0, c37_0, g37_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell37 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((135 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 3))
    (hshi : (((271 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 3) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S37 : ℝ) * zval y 3 7 + (C37 : ℝ) ≤ 1 - Real.cos (zval y 3 7) := by
  exact line37 (zval y 3 7) (arc37 y hslo hshi hcell)

/-! ### pair (3, 8), 1 line(s), branch `endpoint`, shift m = -1 -/

def A38 : ℚ := ((-196802012440337451957011421499950982803 : ℚ) / 57646075230342348800000000000000000000)
def B38 : ℚ := ((-393438934618556930884574594130383432449 : ℚ) / 115292150460684697600000000000000000000)
def S38 : ℚ := ((4833856172100237 : ℚ) / 18014398509481984)
def C38 : ℚ := ((28792146022373188618669831414022657968463149716148383545105231080783715614120513 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s38_0 : ℚ := ((4833856172100237 : ℚ) / 18014398509481984)
def c38_0 : ℚ := ((28792146022373188618669831414022657968463149716148383545105231080783715614120513 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g38_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc38 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((169 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 3))
    (hshi : (((339 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 3) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A38 : ℝ) ≤ zval y 3 8 ∧ zval y 3 8 ≤ (B38 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 3) (j := 8)
      (by norm_num) (dbm := dbm) (slo := ((169 : ℚ) / 256)) (shi := ((339 : ℚ) / 512)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 3) (j := 8)
    (by norm_num) (slo := ((169 : ℚ) / 256)) (shi := ((339 : ℚ) / 512)) (by norm_num) hlo hhi
  have hAq : A38 ≤ ((((3 : ℚ) - 8) * LQ + Dq * ((169 : ℚ) / 256)) : ℚ) := by
    norm_num [A38, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((3 : ℚ) - 8) * Lq + DQ * ((339 : ℚ) / 512)) : ℚ) ≤ B38 := by
    norm_num [B38, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A38 : ℝ) ≤ (((((3 : ℚ) - 8) * LQ + Dq * ((169 : ℚ) / 256)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((3 : ℚ) - 8) * Lq + DQ * ((339 : ℚ) / 512)) : ℚ) : ℝ) ≤ (B38 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line38 : ∀ z ∈ Set.Icc (A38 : ℝ) (B38 : ℝ),
    (S38 : ℝ) * z + (C38 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A38 : ℝ)) (b := (B38 : ℝ)) (m := -1)
    (by norm_num [A38]; linarith [hpLo, hpHi])
    (by norm_num [B38]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S38, A38, C38, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S38, B38, C38, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse38 : S38 = ((4833856172100237 : ℚ) / 18014398509481984) ∧ C38 = ((28792146022373188618669831414022657968463149716148383545105231080783715614120513 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S38, C38, s38_0, c38_0, g38_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell38 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((169 : ℚ) / 256) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 3))
    (hshi : (((339 : ℚ) / 512) : ℚ) = dbm (Fin.castSucc 3) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S38 : ℝ) * zval y 3 8 + (C38 : ℝ) ≤ 1 - Real.cos (zval y 3 8) := by
  exact line38 (zval y 3 8) (arc38 y hslo hshi hcell)

/-! ### pair (4, 5), 1 line(s), branch `tangent`, shift m = 0 -/

def A45 : ℚ := ((-19663692218074644868000747820971104779 : ℚ) / 28823037615171174400000000000000000000)
def B45 : ℚ := ((-7832458835260226184023414208628861437 : ℚ) / 11529215046068469760000000000000000000)
def S45 : ℚ := ((-709900999811975 : ℚ) / 1125899906842624)
def C45 : ℚ := ((-20632738366839181521692822024404887361930598548191122326687048645915598641458479 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s45_0 : ℚ := ((-709900999811975 : ℚ) / 1125899906842624)
def c45_0 : ℚ := ((-20632738366839181521692822024404887361930598548191122326687048645915598641458479 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g45_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc45 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((17 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 5) (Fin.castSucc 4))
    (hshi : (((35 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 4) (Fin.castSucc 5))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A45 : ℝ) ≤ zval y 4 5 ∧ zval y 4 5 ≤ (B45 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 4) (j := 5)
      (by norm_num) (dbm := dbm) (slo := ((17 : ℚ) / 128)) (shi := ((35 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 4) (j := 5)
    (by norm_num) (slo := ((17 : ℚ) / 128)) (shi := ((35 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A45 ≤ ((((4 : ℚ) - 5) * LQ + Dq * ((17 : ℚ) / 128)) : ℚ) := by
    norm_num [A45, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((4 : ℚ) - 5) * Lq + DQ * ((35 : ℚ) / 256)) : ℚ) ≤ B45 := by
    norm_num [B45, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A45 : ℝ) ≤ (((((4 : ℚ) - 5) * LQ + Dq * ((17 : ℚ) / 128)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((4 : ℚ) - 5) * Lq + DQ * ((35 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B45 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line45 : ∀ z ∈ Set.Icc (A45 : ℝ) (B45 : ℝ),
    (S45 : ℝ) * z + (C45 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A45 : ℝ)) (b := (B45 : ℝ)) (m := 0)
    (by norm_num [A45]; linarith [hpLo, hpHi])
    (by norm_num [B45]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-6822213703 : ℚ) / 10000000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A45, B45]
  · norm_num
  · norm_num [S45, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S45, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C45, S45, A45, B45, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse45 : S45 = ((-709900999811975 : ℚ) / 1125899906842624) ∧ C45 = ((-20632738366839181521692822024404887361930598548191122326687048645915598641458479 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S45, C45, s45_0, c45_0, g45_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell45 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((17 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 5) (Fin.castSucc 4))
    (hshi : (((35 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 4) (Fin.castSucc 5))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S45 : ℝ) * zval y 4 5 + (C45 : ℝ) ≤ 1 - Real.cos (zval y 4 5) := by
  exact line45 (zval y 4 5) (arc45 y hslo hshi hcell)

/-! ### pair (4, 6), 1 line(s), branch `tangent`, shift m = 0 -/

def A46 : ℚ := ((-41143377291650325783044871834581494701 : ℚ) / 28823037615171174400000000000000000000)
def B46 : ℚ := ((-82121664323288561723714989820436641077 : ℚ) / 57646075230342348800000000000000000000)
def S46 : ℚ := ((-1114178351265653 : ℚ) / 1125899906842624)
def C46 : ℚ := ((-1735765792190739325910416261010483926885671605462717040351495059407566116595473 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000)
def s46_0 : ℚ := ((-1114178351265653 : ℚ) / 1125899906842624)
def c46_0 : ℚ := ((-1735765792190739325910416261010483926885671605462717040351495059407566116595473 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000)
def g46_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc46 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((23 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 4))
    (hshi : (((47 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 4) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A46 : ℝ) ≤ zval y 4 6 ∧ zval y 4 6 ≤ (B46 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 4) (j := 6)
      (by norm_num) (dbm := dbm) (slo := ((23 : ℚ) / 128)) (shi := ((47 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 4) (j := 6)
    (by norm_num) (slo := ((23 : ℚ) / 128)) (shi := ((47 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A46 ≤ ((((4 : ℚ) - 6) * LQ + Dq * ((23 : ℚ) / 128)) : ℚ) := by
    norm_num [A46, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((4 : ℚ) - 6) * Lq + DQ * ((47 : ℚ) / 256)) : ℚ) ≤ B46 := by
    norm_num [B46, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A46 : ℝ) ≤ (((((4 : ℚ) - 6) * LQ + Dq * ((23 : ℚ) / 128)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((4 : ℚ) - 6) * Lq + DQ * ((47 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B46 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line46 : ∀ z ∈ Set.Icc (A46 : ℝ) (B46 : ℝ),
    (S46 : ℝ) * z + (C46 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.monotone_sin_arc
    (a := (A46 : ℝ)) (b := (B46 : ℝ)) (m := 0)
    (by norm_num [A46]; linarith [hpLo, hpHi])
    (by norm_num [B46]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_inc (t := ((-14263737021 : ℚ) / 10000000000)) (e := ((1 : ℚ) / 5000000000)) hm
  · norm_num [A46, B46]
  · norm_num
  · norm_num [S46, N11Formalization.sinLoNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [S46, N11Formalization.sinHiNLag, N11Formalization.sinTQ, Finset.sum_range_succ]
  · norm_num [C46, S46, A46, B46, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse46 : S46 = ((-1114178351265653 : ℚ) / 1125899906842624) ∧ C46 = ((-1735765792190739325910416261010483926885671605462717040351495059407566116595473 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S46, C46, s46_0, c46_0, g46_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell46 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((23 : ℚ) / 128) : ℚ) = -dbm (Fin.castSucc 6) (Fin.castSucc 4))
    (hshi : (((47 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 4) (Fin.castSucc 6))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S46 : ℝ) * zval y 4 6 + (C46 : ℝ) ≤ 1 - Real.cos (zval y 4 6) := by
  exact line46 (zval y 4 6) (arc46 y hslo hshi hcell)

/-! ### pair (4, 7), 1 line(s), branch `endpoint`, shift m = -1 -/

def A47 : ℚ := ((-250327159201313023515352040102527603479 : ℚ) / 115292150460684697600000000000000000000)
def B47 : ℚ := ((-125081034470275992527312908597728974969 : ℚ) / 57646075230342348800000000000000000000)
def S47 : ℚ := ((-3717668048735665 : ℚ) / 4503599627370496)
def C47 : ℚ := ((-11366212893701428705783545582136610130592177192868169117575760355140871653827641 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s47_0 : ℚ := ((-3717668048735665 : ℚ) / 4503599627370496)
def c47_0 : ℚ := ((-11366212893701428705783545582136610130592177192868169117575760355140871653827641 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g47_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc47 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((117 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 4))
    (hshi : (((59 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 4) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A47 : ℝ) ≤ zval y 4 7 ∧ zval y 4 7 ≤ (B47 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 4) (j := 7)
      (by norm_num) (dbm := dbm) (slo := ((117 : ℚ) / 512)) (shi := ((59 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 4) (j := 7)
    (by norm_num) (slo := ((117 : ℚ) / 512)) (shi := ((59 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A47 ≤ ((((4 : ℚ) - 7) * LQ + Dq * ((117 : ℚ) / 512)) : ℚ) := by
    norm_num [A47, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((4 : ℚ) - 7) * Lq + DQ * ((59 : ℚ) / 256)) : ℚ) ≤ B47 := by
    norm_num [B47, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A47 : ℝ) ≤ (((((4 : ℚ) - 7) * LQ + Dq * ((117 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((4 : ℚ) - 7) * Lq + DQ * ((59 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B47 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line47 : ∀ z ∈ Set.Icc (A47 : ℝ) (B47 : ℝ),
    (S47 : ℝ) * z + (C47 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A47 : ℝ)) (b := (B47 : ℝ)) (m := -1)
    (by norm_num [A47]; linarith [hpLo, hpHi])
    (by norm_num [B47]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S47, A47, C47, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S47, B47, C47, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse47 : S47 = ((-3717668048735665 : ℚ) / 4503599627370496) ∧ C47 = ((-11366212893701428705783545582136610130592177192868169117575760355140871653827641 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S47, C47, s47_0, c47_0, g47_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell47 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((117 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 7) (Fin.castSucc 4))
    (hshi : (((59 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 4) (Fin.castSucc 7))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S47 : ℝ) * zval y 4 7 + (C47 : ℝ) ≤ 1 - Real.cos (zval y 4 7) := by
  exact line47 (zval y 4 7) (arc47 y hslo hshi hcell)

/-! ### pair (4, 8), 1 line(s), branch `endpoint`, shift m = -1 -/

def A48 : ℚ := ((-65796385614722320597471006277282404519 : ℚ) / 23058430092136939520000000000000000000)
def B48 : ℚ := ((-164408418906172179964103059977140587663 : ℚ) / 57646075230342348800000000000000000000)
def S48 : ℚ := ((-5131319949528879 : ℚ) / 18014398509481984)
def C48 : ℚ := ((2291961994323045449167930953196155176423953626889388628168755080275302705388837 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000)
def s48_0 : ℚ := ((-5131319949528879 : ℚ) / 18014398509481984)
def c48_0 : ℚ := ((2291961994323045449167930953196155176423953626889388628168755080275302705388837 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000)
def g48_0 : ℚ := (1 : ℚ)

/-- Interval membership from the two DBM rows (kernel-bracket interval). -/
theorem arc48 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((185 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 4))
    (hshi : (((93 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 4) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (A48 : ℝ) ≤ zval y 4 8 ∧ zval y 4 8 ≤ (B48 : ℝ) := by
  obtain ⟨hlo, hhi⟩ :=
    N11Formalization.PairTemplate.pair_sigma_bounds (y := y) (i := 4) (j := 8)
      (by norm_num) (dbm := dbm) (slo := ((185 : ℚ) / 512)) (shi := ((93 : ℚ) / 256)) hslo hshi hcell
  have hb := N11Formalization.PairTemplate.pair_arc_mem (y := y) (i := 4) (j := 8)
    (by norm_num) (slo := ((185 : ℚ) / 512)) (shi := ((93 : ℚ) / 256)) (by norm_num) hlo hhi
  have hAq : A48 ≤ ((((4 : ℚ) - 8) * LQ + Dq * ((185 : ℚ) / 512)) : ℚ) := by
    norm_num [A48, LQ, Dq, Lq, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hBq : ((((4 : ℚ) - 8) * Lq + DQ * ((93 : ℚ) / 256)) : ℚ) ≤ B48 := by
    norm_num [B48, LQ, Dq, Lq, DQ, N11Formalization.RatInterval.piLo,
      N11Formalization.RatInterval.piHi]
  have hAr : (A48 : ℝ) ≤ (((((4 : ℚ) - 8) * LQ + Dq * ((185 : ℚ) / 512)) : ℚ) : ℝ) := by exact_mod_cast hAq
  have hBr : (((((4 : ℚ) - 8) * Lq + DQ * ((93 : ℚ) / 256)) : ℚ) : ℝ) ≤ (B48 : ℝ) := by exact_mod_cast hBq
  simp only [zval_eq] at hb ⊢
  exact ⟨le_trans hAr hb.1, le_trans hb.2 hBr⟩

/-- The gamma-collapsed line, certified by ONE compiled rule (cert0 shape). -/
theorem line48 : ∀ z ∈ Set.Icc (A48 : ℝ) (B48 : ℝ),
    (S48 : ℝ) * z + (C48 : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := N11Formalization.RatInterval.piLo_lt_pi
  have hpHi := N11Formalization.RatInterval.pi_lt_piHi
  norm_num [N11Formalization.RatInterval.piLo, N11Formalization.RatInterval.piHi] at hpLo hpHi
  have hm := N11Formalization.FlashCosineSupport.antitone_sin_arc
    (a := (A48 : ℝ)) (b := (B48 : ℝ)) (m := -1)
    (by norm_num [A48]; linarith [hpLo, hpHi])
    (by norm_num [B48]; linarith [hpLo, hpHi])
  apply N11Formalization.FlashCosineLeaf284Energy.rational_dec hm
  · norm_num [S48, A48, C48, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]
  · norm_num [S48, B48, C48, N11Formalization.cosHiNLag, N11Formalization.cosTQ, Finset.sum_range_succ]

/-- The collapse is DATA: the frozen slope/intercept are exactly the gamma-mixture. -/
theorem collapse48 : S48 = ((-5131319949528879 : ℚ) / 18014398509481984) ∧ C48 = ((2291961994323045449167930953196155176423953626889388628168755080275302705388837 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  norm_num [S48, C48, s48_0, c48_0, g48_0]

/-- The pair's whole-cell minorant, on the collapsed line. -/
theorem cell48 (y : Fin 9 → ℝ) {dbm : Fin 10 → Fin 10 → ℚ}
    (hslo : (((185 : ℚ) / 512) : ℚ) = -dbm (Fin.castSucc 8) (Fin.castSucc 4))
    (hshi : (((93 : ℚ) / 256) : ℚ) = dbm (Fin.castSucc 4) (Fin.castSucc 8))
    (hcell : Cell (fun a b => (dbm a b : ℝ)) (tlift y)) :
    (S48 : ℝ) * zval y 4 8 + (C48 : ℝ) ≤ 1 - Real.cos (zval y 4 8) := by
  exact line48 (zval y 4 8) (arc48 y hslo hshi hcell)
#print axioms N11Formalization.Leaf4348Pairs.arc37
#print axioms N11Formalization.Leaf4348Pairs.line37
#print axioms N11Formalization.Leaf4348Pairs.collapse37
#print axioms N11Formalization.Leaf4348Pairs.cell37
#print axioms N11Formalization.Leaf4348Pairs.arc38
#print axioms N11Formalization.Leaf4348Pairs.line38
#print axioms N11Formalization.Leaf4348Pairs.collapse38
#print axioms N11Formalization.Leaf4348Pairs.cell38
#print axioms N11Formalization.Leaf4348Pairs.arc45
#print axioms N11Formalization.Leaf4348Pairs.line45
#print axioms N11Formalization.Leaf4348Pairs.collapse45
#print axioms N11Formalization.Leaf4348Pairs.cell45
#print axioms N11Formalization.Leaf4348Pairs.arc46
#print axioms N11Formalization.Leaf4348Pairs.line46
#print axioms N11Formalization.Leaf4348Pairs.collapse46
#print axioms N11Formalization.Leaf4348Pairs.cell46
#print axioms N11Formalization.Leaf4348Pairs.arc47
#print axioms N11Formalization.Leaf4348Pairs.line47
#print axioms N11Formalization.Leaf4348Pairs.collapse47
#print axioms N11Formalization.Leaf4348Pairs.cell47
#print axioms N11Formalization.Leaf4348Pairs.arc48
#print axioms N11Formalization.Leaf4348Pairs.line48
#print axioms N11Formalization.Leaf4348Pairs.collapse48
#print axioms N11Formalization.Leaf4348Pairs.cell48

end N11Formalization.Leaf4348Pairs
