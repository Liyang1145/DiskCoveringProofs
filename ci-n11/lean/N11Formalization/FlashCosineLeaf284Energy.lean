import N11Formalization.FlashCosineLeaf284Bridge
import N11Formalization.FlashCosineSupport
import N11Formalization.IntervalsHighLag
namespace N11Formalization.FlashCosineLeaf284Energy
open Finset FlashCosineLeaf284Bridge
open FlashCosine (Lq LQ Dq DQ L_mem D_mem tval zval zval_eq cell_bound)
set_option autoImplicit false
set_option maxHeartbeats 120000000
set_option maxRecDepth 300000
set_option linter.unusedSimpArgs false

/-- Rational witness adapter: the only trigonometric premises come from proved
universal Taylor bounds, not program self-reported stationary minima. -/
theorem rational_inc {a b t s c e : ℚ}
    (hm : MonotoneOn Real.sin (Set.Icc (a : ℝ) (b : ℝ)))
    (ht : a ≤ t ∧ t ≤ b) (he : 0 ≤ e)
    (hl : s - e ≤ sinLoNLag t) (hh : sinHiNLag t ≤ s + e)
    (hc : c ≤ 1 - cosHiNLag t - s * t - e * (b - a)) :
    ∀ z ∈ Set.Icc (a : ℝ) (b : ℝ), (s : ℝ) * z + (c : ℝ) ≤ 1 - Real.cos z := by
  have htR : (t : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) :=
    ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hlR : (s : ℝ) - (e : ℝ) ≤ (sinLoNLag t : ℝ) := by exact_mod_cast hl
  have hhR : (sinHiNLag t : ℝ) ≤ (s : ℝ) + (e : ℝ) := by exact_mod_cast hh
  have hs : |Real.sin (t : ℝ) - (s : ℝ)| ≤ (e : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [sinLoNLag_le_sin t, sin_le_sinHiNLag t]
  have hcR : (c : ℝ) ≤ 1 - (cosHiNLag t : ℝ) - (s : ℝ) * (t : ℝ) -
      (e : ℝ) * ((b : ℝ) - (a : ℝ)) := by exact_mod_cast hc
  exact FlashCosineSupport.minorant_of_approx_support hm htR heR hs
    (cos_le_cosHiNLag t) hcR

theorem rational_dec {a b s c : ℚ}
    (hm : AntitoneOn Real.sin (Set.Icc (a : ℝ) (b : ℝ)))
    (ha : c ≤ 1 - cosHiNLag a - s * a)
    (hb : c ≤ 1 - cosHiNLag b - s * b) :
    ∀ z ∈ Set.Icc (a : ℝ) (b : ℝ), (s : ℝ) * z + (c : ℝ) ≤ 1 - Real.cos z := by
  have haR : (c : ℝ) ≤ 1 - (cosHiNLag a : ℝ) - (s : ℝ) * (a : ℝ) := by exact_mod_cast ha
  have hbR : (c : ℝ) ≤ 1 - (cosHiNLag b : ℝ) - (s : ℝ) * (b : ℝ) := by exact_mod_cast hb
  exact FlashCosineSupport.minorant_of_antitone_sin hm
    (by linarith [cos_le_cosHiNLag a]) (by linarith [cos_le_cosHiNLag b])

def delta : ℚ := 1 / 10^6

def a : Fin 36 → ℚ := fun k => match (k : ℕ) with
  | 0 => ((-3897963 : ℚ) / 5000000)
  | 1 => ((-155918519 : ℚ) / 100000000)
  | 2 => ((-107774539 : ℚ) / 50000000)
  | 3 => ((-293508337 : ℚ) / 100000000)
  | 4 => ((-22071181 : ℚ) / 6250000)
  | 5 => ((-86219631 : ℚ) / 20000000)
  | 6 => ((-254528707 : ℚ) / 50000000)
  | 7 => ((-568687973 : ℚ) / 100000000)
  | 8 => ((-3897963 : ℚ) / 5000000)
  | 9 => ((-155918519 : ℚ) / 100000000)
  | 10 => ((-116938889 : ℚ) / 50000000)
  | 11 => ((-155918519 : ℚ) / 50000000)
  | 12 => ((-389796297 : ℚ) / 100000000)
  | 13 => ((-56178357 : ℚ) / 12500000)
  | 14 => ((-254528707 : ℚ) / 50000000)
  | 15 => ((-3897963 : ℚ) / 5000000)
  | 16 => ((-155918519 : ℚ) / 100000000)
  | 17 => ((-116938889 : ℚ) / 50000000)
  | 18 => ((-155918519 : ℚ) / 50000000)
  | 19 => ((-92866899 : ℚ) / 25000000)
  | 20 => ((-86219631 : ℚ) / 20000000)
  | 21 => ((-3897963 : ℚ) / 5000000)
  | 22 => ((-155918519 : ℚ) / 100000000)
  | 23 => ((-116938889 : ℚ) / 50000000)
  | 24 => ((-293508337 : ℚ) / 100000000)
  | 25 => ((-22071181 : ℚ) / 6250000)
  | 26 => ((-3897963 : ℚ) / 5000000)
  | 27 => ((-155918519 : ℚ) / 100000000)
  | 28 => ((-107774539 : ℚ) / 50000000)
  | 29 => ((-293508337 : ℚ) / 100000000)
  | 30 => ((-3897963 : ℚ) / 5000000)
  | 31 => ((-155918519 : ℚ) / 100000000)
  | 32 => ((-107774539 : ℚ) / 50000000)
  | 33 => ((-3897963 : ℚ) / 5000000)
  | 34 => ((-155918519 : ℚ) / 100000000)
  | 35 => ((-3897963 : ℚ) / 5000000)
  | _ => 0

def b : Fin 36 → ℚ := fun k => match (k : ℕ) with
  | 0 => ((-41301857 : ℚ) / 100000000)
  | 1 => ((-119261117 : ℚ) / 100000000)
  | 2 => ((-24652547 : ℚ) / 12500000)
  | 3 => ((-55035927 : ℚ) / 20000000)
  | 4 => ((-167405097 : ℚ) / 50000000)
  | 5 => ((-24652547 : ℚ) / 6250000)
  | 6 => ((-118100003 : ℚ) / 25000000)
  | 7 => ((-550359271 : ℚ) / 100000000)
  | 8 => ((-41301857 : ℚ) / 100000000)
  | 9 => ((-119261117 : ℚ) / 100000000)
  | 10 => ((-24652547 : ℚ) / 12500000)
  | 11 => ((-128425467 : ℚ) / 50000000)
  | 12 => ((-316481493 : ℚ) / 100000000)
  | 13 => ((-24652547 : ℚ) / 6250000)
  | 14 => ((-118100003 : ℚ) / 25000000)
  | 15 => ((-41301857 : ℚ) / 100000000)
  | 16 => ((-119261117 : ℚ) / 100000000)
  | 17 => ((-7155667 : ℚ) / 4000000)
  | 18 => ((-119261117 : ℚ) / 50000000)
  | 19 => ((-316481493 : ℚ) / 100000000)
  | 20 => ((-24652547 : ℚ) / 6250000)
  | 21 => ((-29815279 : ℚ) / 50000000)
  | 22 => ((-119261117 : ℚ) / 100000000)
  | 23 => ((-24652547 : ℚ) / 12500000)
  | 24 => ((-55035927 : ℚ) / 20000000)
  | 25 => ((-167405097 : ℚ) / 50000000)
  | 26 => ((-29815279 : ℚ) / 50000000)
  | 27 => ((-119261117 : ℚ) / 100000000)
  | 28 => ((-24652547 : ℚ) / 12500000)
  | 29 => ((-55035927 : ℚ) / 20000000)
  | 30 => ((-41301857 : ℚ) / 100000000)
  | 31 => ((-119261117 : ℚ) / 100000000)
  | 32 => ((-24652547 : ℚ) / 12500000)
  | 33 => ((-41301857 : ℚ) / 100000000)
  | 34 => ((-119261117 : ℚ) / 100000000)
  | 35 => ((-29815279 : ℚ) / 50000000)
  | _ => 0

theorem cert0 : ∀ z ∈ Set.Icc (a 0 : ℝ) (b 0 : ℝ),
    (sl 0 : ℝ) * z + ((cc 0 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 0 : ℝ)) (b := (b 0 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-18344271 : ℚ) / 25000000)) (e := ((11 : ℚ) / 10000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert1 : ∀ z ∈ Set.Icc (a 1 : ℝ) (b 1 : ℝ),
    (sl 1 : ℝ) * z + ((cc 1 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 1 : ℝ)) (b := (b 1 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-142171993 : ℚ) / 100000000)) (e := ((3 : ℚ) / 10000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert2 : ∀ z ∈ Set.Icc (a 2 : ℝ) (b 2 : ℝ),
    (sl 2 : ℝ) * z + ((cc 2 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 2 : ℝ)) (b := (b 2 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert3 : ∀ z ∈ Set.Icc (a 3 : ℝ) (b 3 : ℝ),
    (sl 3 : ℝ) * z + ((cc 3 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 3 : ℝ)) (b := (b 3 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert4 : ∀ z ∈ Set.Icc (a 4 : ℝ) (b 4 : ℝ),
    (sl 4 : ℝ) * z + ((cc 4 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 4 : ℝ)) (b := (b 4 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert5 : ∀ z ∈ Set.Icc (a 5 : ℝ) (b 5 : ℝ),
    (sl 5 : ℝ) * z + ((cc 5 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 5 : ℝ)) (b := (b 5 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert6 : ∀ z ∈ Set.Icc (a 6 : ℝ) (b 6 : ℝ),
    (sl 6 : ℝ) * z + ((cc 6 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 6 : ℝ)) (b := (b 6 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-499893063 : ℚ) / 100000000)) (e := ((9 : ℚ) / 10000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert7 : ∀ z ∈ Set.Icc (a 7 : ℝ) (b 7 : ℝ),
    (sl 7 : ℝ) * z + ((cc 7 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 7 : ℝ)) (b := (b 7 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-139909641 : ℚ) / 25000000)) (e := ((17 : ℚ) / 5000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert8 : ∀ z ∈ Set.Icc (a 8 : ℝ) (b 8 : ℝ),
    (sl 8 : ℝ) * z + ((cc 8 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 8 : ℝ)) (b := (b 8 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-68794909 : ℚ) / 100000000)) (e := ((1 : ℚ) / 1250000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert9 : ∀ z ∈ Set.Icc (a 9 : ℝ) (b 9 : ℝ),
    (sl 9 : ℝ) * z + ((cc 9 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 9 : ℝ)) (b := (b 9 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-142171993 : ℚ) / 100000000)) (e := ((3 : ℚ) / 10000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert10 : ∀ z ∈ Set.Icc (a 10 : ℝ) (b 10 : ℝ),
    (sl 10 : ℝ) * z + ((cc 10 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 10 : ℝ)) (b := (b 10 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert11 : ∀ z ∈ Set.Icc (a 11 : ℝ) (b 11 : ℝ),
    (sl 11 : ℝ) * z + ((cc 11 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 11 : ℝ)) (b := (b 11 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert12 : ∀ z ∈ Set.Icc (a 12 : ℝ) (b 12 : ℝ),
    (sl 12 : ℝ) * z + ((cc 12 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 12 : ℝ)) (b := (b 12 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert13 : ∀ z ∈ Set.Icc (a 13 : ℝ) (b 13 : ℝ),
    (sl 13 : ℝ) * z + ((cc 13 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 13 : ℝ)) (b := (b 13 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert14 : ∀ z ∈ Set.Icc (a 14 : ℝ) (b 14 : ℝ),
    (sl 14 : ℝ) * z + ((cc 14 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 14 : ℝ)) (b := (b 14 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-243073269 : ℚ) / 50000000)) (e := ((7 : ℚ) / 10000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert15 : ∀ z ∈ Set.Icc (a 15 : ℝ) (b 15 : ℝ),
    (sl 15 : ℝ) * z + ((cc 15 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 15 : ℝ)) (b := (b 15 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-18344271 : ℚ) / 25000000)) (e := ((11 : ℚ) / 10000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert16 : ∀ z ∈ Set.Icc (a 16 : ℝ) (b 16 : ℝ),
    (sl 16 : ℝ) * z + ((cc 16 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 16 : ℝ)) (b := (b 16 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-68794909 : ℚ) / 50000000)) (e := ((1 : ℚ) / 2000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert17 : ∀ z ∈ Set.Icc (a 17 : ℝ) (b 17 : ℝ),
    (sl 17 : ℝ) * z + ((cc 17 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 17 : ℝ)) (b := (b 17 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert18 : ∀ z ∈ Set.Icc (a 18 : ℝ) (b 18 : ℝ),
    (sl 18 : ℝ) * z + ((cc 18 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 18 : ℝ)) (b := (b 18 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert19 : ∀ z ∈ Set.Icc (a 19 : ℝ) (b 19 : ℝ),
    (sl 19 : ℝ) * z + ((cc 19 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 19 : ℝ)) (b := (b 19 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert20 : ∀ z ∈ Set.Icc (a 20 : ℝ) (b 20 : ℝ),
    (sl 20 : ℝ) * z + ((cc 20 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 20 : ℝ)) (b := (b 20 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert21 : ∀ z ∈ Set.Icc (a 21 : ℝ) (b 21 : ℝ),
    (sl 21 : ℝ) * z + ((cc 21 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 21 : ℝ)) (b := (b 21 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-66503821 : ℚ) / 100000000)) (e := ((29 : ℚ) / 10000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert22 : ∀ z ∈ Set.Icc (a 22 : ℝ) (b 22 : ℝ),
    (sl 22 : ℝ) * z + ((cc 22 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 22 : ℝ)) (b := (b 22 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-128425467 : ℚ) / 100000000)) (e := ((1 : ℚ) / 625000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert23 : ∀ z ∈ Set.Icc (a 23 : ℝ) (b 23 : ℝ),
    (sl 23 : ℝ) * z + ((cc 23 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 23 : ℝ)) (b := (b 23 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert24 : ∀ z ∈ Set.Icc (a 24 : ℝ) (b 24 : ℝ),
    (sl 24 : ℝ) * z + ((cc 24 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 24 : ℝ)) (b := (b 24 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert25 : ∀ z ∈ Set.Icc (a 25 : ℝ) (b 25 : ℝ),
    (sl 25 : ℝ) * z + ((cc 25 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 25 : ℝ)) (b := (b 25 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert26 : ∀ z ∈ Set.Icc (a 26 : ℝ) (b 26 : ℝ),
    (sl 26 : ℝ) * z + ((cc 26 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 26 : ℝ)) (b := (b 26 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-30960823 : ℚ) / 50000000)) (e := ((3 : ℚ) / 2000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert27 : ∀ z ∈ Set.Icc (a 27 : ℝ) (b 27 : ℝ),
    (sl 27 : ℝ) * z + ((cc 27 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 27 : ℝ)) (b := (b 27 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-68794909 : ℚ) / 50000000)) (e := ((1 : ℚ) / 2000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert28 : ∀ z ∈ Set.Icc (a 28 : ℝ) (b 28 : ℝ),
    (sl 28 : ℝ) * z + ((cc 28 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 28 : ℝ)) (b := (b 28 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert29 : ∀ z ∈ Set.Icc (a 29 : ℝ) (b 29 : ℝ),
    (sl 29 : ℝ) * z + ((cc 29 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 29 : ℝ)) (b := (b 29 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert30 : ∀ z ∈ Set.Icc (a 30 : ℝ) (b 30 : ℝ),
    (sl 30 : ℝ) * z + ((cc 30 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 30 : ℝ)) (b := (b 30 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-77959259 : ℚ) / 100000000)) (e := ((23 : ℚ) / 10000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert31 : ∀ z ∈ Set.Icc (a 31 : ℝ) (b 31 : ℝ),
    (sl 31 : ℝ) * z + ((cc 31 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 31 : ℝ)) (b := (b 31 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-151336343 : ℚ) / 100000000)) (e := ((1 : ℚ) / 2000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert32 : ∀ z ∈ Set.Icc (a 32 : ℝ) (b 32 : ℝ),
    (sl 32 : ℝ) * z + ((cc 32 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.antitone_sin_arc
    (a := (a 32 : ℝ)) (b := (b 32 : ℝ)) (m := (-1 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_dec hm
  · norm_num [cc, delta, sl, a, cosHiNLag, cosTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert33 : ∀ z ∈ Set.Icc (a 33 : ℝ) (b 33 : ℝ),
    (sl 33 : ℝ) * z + ((cc 33 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 33 : ℝ)) (b := (b 33 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-77959259 : ℚ) / 100000000)) (e := ((23 : ℚ) / 10000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert34 : ∀ z ∈ Set.Icc (a 34 : ℝ) (b 34 : ℝ),
    (sl 34 : ℝ) * z + ((cc 34 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 34 : ℝ)) (b := (b 34 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-68794909 : ℚ) / 50000000)) (e := ((1 : ℚ) / 2000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem cert35 : ∀ z ∈ Set.Icc (a 35 : ℝ) (b 35 : ℝ),
    (sl 35 : ℝ) * z + ((cc 35 - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  have hpLo := RatInterval.piLo_lt_pi
  have hpHi := RatInterval.pi_lt_piHi
  norm_num [RatInterval.piLo, RatInterval.piHi] at hpLo hpHi
  have hm := FlashCosineSupport.monotone_sin_arc
    (a := (a 35 : ℝ)) (b := (b 35 : ℝ)) (m := (0 : ℤ))
    (by norm_num [a]; linarith [hpLo, hpHi])
    (by norm_num [b]; linarith [hpLo, hpHi])
  apply rational_inc (t := ((-30960823 : ℚ) / 50000000)) (e := ((3 : ℚ) / 2000000000)) hm
  · norm_num [a, b]
  · norm_num
  · norm_num [sl, sinLoNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [sl, sinHiNLag, sinTQ, Finset.sum_range_succ]
  · norm_num [cc, delta, sl, a, b, cosHiNLag, cosTQ, Finset.sum_range_succ]

theorem pair_lt (k : Fin 36) : (iOf k : ℕ) < (jOf k : ℕ) := by
  fin_cases k <;> norm_num [iOf, jOf]

def slo (k : Fin 36) : ℚ := -dbm (jOf k).castSucc (iOf k).castSucc
def shi (k : Fin 36) : ℚ := dbm (iOf k).castSucc (jOf k).castSucc

theorem slo_nonneg (k : Fin 36) : 0 ≤ slo k := by
  fin_cases k <;> norm_num [slo, dbm, iOf, jOf]

theorem enlarged_lo (k : Fin 36) : a k ≤
    (((iOf k : ℕ) : ℚ) - ((jOf k : ℕ) : ℚ)) * LQ + Dq * slo k := by
  fin_cases k <;> norm_num [a, iOf, jOf, LQ, Lq, Dq, slo, dbm, RatInterval.piHi]

theorem enlarged_hi (k : Fin 36) :
    (((iOf k : ℕ) : ℚ) - ((jOf k : ℕ) : ℚ)) * Lq + DQ * shi k ≤ b k := by
  fin_cases k <;> norm_num [b, iOf, jOf, Lq, DQ, LQ, shi, dbm, RatInterval.piLo]

theorem arc_mem (y : Fin 9 → ℝ)
    (hcell : FlashLeafSplit.Cell (fun i j => (dbm i j : ℝ)) (FlashLeafSplit.tlift y))
    (k : Fin 36) : zval y (iOf k) (jOf k) ∈ Set.Icc (a k : ℝ) (b k : ℝ) := by
  have h1 := hcell (jOf k).castSucc (iOf k).castSucc
  have h2 := hcell (iOf k).castSucc (jOf k).castSucc
  simp only [← tval_eq_tlift] at h1 h2
  have hlo : (slo k : ℝ) ≤ tval y (jOf k).castSucc - tval y (iOf k).castSucc := by
    simp only [slo, Rat.cast_neg]
    linarith
  have hhi : tval y (jOf k).castSucc - tval y (iOf k).castSucc ≤ (shi k : ℝ) := h2
  have hc := cell_bound (pair_lt k) (slo_nonneg k) L_mem.1 L_mem.2 D_mem.1 D_mem.2 hlo hhi
  have ha : (a k : ℝ) ≤
      ((((iOf k : ℕ) : ℚ) - ((jOf k : ℕ) : ℚ)) * LQ + Dq * slo k : ℚ) := by
    exact_mod_cast enlarged_lo k
  have hb : (((((iOf k : ℕ) : ℚ) - ((jOf k : ℕ) : ℚ)) * Lq + DQ * shi k : ℚ) : ℝ) ≤ (b k : ℝ) := by
    exact_mod_cast enlarged_hi k
  rw [zval_eq]
  exact ⟨le_trans ha hc.1, le_trans hc.2 hb⟩

theorem actual_pair0 (y : Fin 9 → ℝ)
    (hcell : FlashLeafSplit.Cell (fun i j => (dbm i j : ℝ)) (FlashLeafSplit.tlift y)) :
    (sl 0 : ℝ) * zval y (iOf 0) (jOf 0) + ((cc 0 - delta : ℚ) : ℝ) ≤
      1 - Real.cos (zval y (iOf 0) (jOf 0)) :=
  cert0 _ (arc_mem y hcell 0)

theorem all_minorants (k : Fin 36) : ∀ z ∈ Set.Icc (a k : ℝ) (b k : ℝ),
    (sl k : ℝ) * z + ((cc k - delta : ℚ) : ℝ) ≤ 1 - Real.cos z := by
  fin_cases k
  · exact cert0
  · exact cert1
  · exact cert2
  · exact cert3
  · exact cert4
  · exact cert5
  · exact cert6
  · exact cert7
  · exact cert8
  · exact cert9
  · exact cert10
  · exact cert11
  · exact cert12
  · exact cert13
  · exact cert14
  · exact cert15
  · exact cert16
  · exact cert17
  · exact cert18
  · exact cert19
  · exact cert20
  · exact cert21
  · exact cert22
  · exact cert23
  · exact cert24
  · exact cert25
  · exact cert26
  · exact cert27
  · exact cert28
  · exact cert29
  · exact cert30
  · exact cert31
  · exact cert32
  · exact cert33
  · exact cert34
  · exact cert35

theorem weight_nonneg (k : Fin 36) : 0 ≤ wt k := by
  fin_cases k <;> norm_num [wt]

theorem weight_le_tenth (k : Fin 36) : wt k ≤ 1 / 10 := by
  fin_cases k <;> norm_num [wt]

def weightCap : ℚ := 18 / 5

theorem sum_weight_cap : (∑ k : Fin 36, (wt k : ℝ)) ≤ (weightCap : ℝ) := by
  have hh : ∀ k : Fin 36, (wt k : ℝ) ≤ (1 / 10 : ℝ) := fun k => by
    have h : (wt k : ℝ) ≤ ((1 / 10 : ℚ) : ℝ) := by exact_mod_cast weight_le_tenth k
    norm_num at h ⊢
    exact h
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 36))) fun k _ => hh k
  norm_num [weightCap] at h ⊢
  exact h

theorem retained_gt : T^2 < lower284 - delta * weightCap := by
  rw [lower284_eq]
  norm_num [T, delta, weightCap]

noncomputable def pairSafe (y : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 36, (wt k : ℝ) *
    ((sl k : ℝ) * zval y (iOf k) (jOf k) + ((cc k - delta : ℚ) : ℝ))

noncomputable def pairEnergy (y : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 36, (wt k : ℝ) * (1 - Real.cos (zval y (iOf k) (jOf k)))

theorem safe_identity (y : Fin 9 → ℝ) :
    pairSafe y = pairAffine y - (delta : ℝ) * ∑ k : Fin 36, (wt k : ℝ) := by
  simp only [pairSafe, pairAffine, Rat.cast_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem safe_le_energy (y : Fin 9 → ℝ)
    (hcell : FlashLeafSplit.Cell (fun i j => (dbm i j : ℝ)) (FlashLeafSplit.tlift y)) :
    pairSafe y ≤ pairEnergy y := by
  unfold pairSafe pairEnergy
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (all_minorants k _ (arc_mem y hcell k))
    (by exact_mod_cast weight_nonneg k)

/-- Concrete whole-cell 36-pair cosine lower bound. No oracle hypothesis is hidden. -/
theorem leaf284_energy_gt (y : Fin 9 → ℝ)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hcell : FlashLeafSplit.Cell (fun i j => (dbm i j : ℝ)) (FlashLeafSplit.tlift y)) :
    (T : ℝ)^2 < pairEnergy y := by
  have ha : (lower284 : ℝ) ≤ pairAffine y := by
    rw [affine_identity]
    exact affine_lower FlashCosine.Lc FlashCosine.Dc y L_mem D_mem.1 hy0 hy1
      (rows_of_cell y hcell)
  have hret : (T : ℝ)^2 < (lower284 : ℝ) - (delta : ℝ) * (weightCap : ℝ) := by
    exact_mod_cast retained_gt
  have hpen := mul_le_mul_of_nonneg_left sum_weight_cap
    (show (0 : ℝ) ≤ (delta : ℝ) by norm_num [delta])
  have hsafe : (lower284 : ℝ) - (delta : ℝ) * (weightCap : ℝ) ≤ pairSafe y := by
    rw [safe_identity]
    linarith
  exact lt_of_lt_of_le (lt_of_lt_of_le hret hsafe) (safe_le_energy y hcell)

end N11Formalization.FlashCosineLeaf284Energy
#check @N11Formalization.FlashCosineLeaf284Energy.leaf284_energy_gt
#print axioms N11Formalization.FlashCosineLeaf284Energy.all_minorants
#print axioms N11Formalization.FlashCosineLeaf284Energy.arc_mem
#print axioms N11Formalization.FlashCosineLeaf284Energy.retained_gt
#print axioms N11Formalization.FlashCosineLeaf284Energy.safe_identity
#print axioms N11Formalization.FlashCosineLeaf284Energy.safe_le_energy
#print axioms N11Formalization.FlashCosineLeaf284Energy.leaf284_energy_gt
