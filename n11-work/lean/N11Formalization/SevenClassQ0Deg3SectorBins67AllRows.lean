import N11Formalization.SevenClassQ0Deg3SectorBins5AllRows
import N11Formalization.SevenClassQ0Deg3SectorBin6
import N11Formalization.SevenClassQ0Deg3SectorBin7

/-! Lane A: the complete shapes of bins 6 and 7 for every sector row.

The audited witness is the first grid point in both bins for every row.  Thus
the increasing half is vacuous.  Past `3*pi/4` the cosine upper bracket is at
most `-2/3`, while each row's exact derivative threshold is at least that
value; this proves both decreasing halves. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBins67AllRows

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3EdgeShape
open SevenClassQ0Deg3SectorBin6
open SevenClassQ0Deg3SectorBin7
open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness
open SevenClassQ0Deg3SectorCalculus
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables
open N11Formalization.ActualRingLinkBoundaryData

theorem cosHiNLag_nodeQ_1536_le_threshold (i : Fin 9) :
    cosHiNLag (nodeQ RatInterval.piHi 2048 1536) ≤
      (2 * mu (nextSite i) : ℚ) / (19 / 50 : ℚ) ^ 2 := by
  fin_cases i <;> norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ, mu, nextSite, ringSite, nextRing]

theorem cosHiReal_le_threshold_of_nodeQ_1536_le (i : Fin 9) {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 1536 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ 2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 := by
  let q : ℚ := nodeQ RatInterval.piHi 2048 1536
  have hq3 : 3 * Real.pi / 4 ≤ (q : ℝ) := by
    dsimp [q]
    norm_num [nodeQ, RatInterval.piHi]
  have htail : (-(2 / 3) : ℝ) ≤
      (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    fin_cases i <;> norm_num [mu, nextSite, ringSite, nextRing]
  exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le
    (hq3.trans hx0) hx).trans htail

theorem sectorValue_dec_of_bin6 (i : Fin 9) {k l : Fin 2049}
    (hklo : 1536 ≤ k.val) (hkl : k.val ≤ l.val) (hll : l.val ≤ 1791) :
    sectorValue i l ≤ sectorValue i k := by
  have ha : nodeBin k = nodeBin l := by
    rw [nodeBin_eq_six_of_mem_bin6 (by omega) (by omega),
      nodeBin_eq_six_of_mem_bin6 (by omega) (by omega)]
  apply sectorValue_le_of_cos_le i k l ha
    (s := (nodeQ RatInterval.piHi 2048 (1536 : Fin 2049) : ℚ))
    (t := (nodeQ RatInterval.piHi 2048 (1791 : Fin 2049) : ℚ))
  · unfold nodeQ; positivity
  · unfold nodeQ
    have hkq : ((1536 : Fin 2049).val : ℚ) ≤ (k.val : ℚ) := by exact_mod_cast hklo
    have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkq hp) (by norm_num)
  · unfold nodeQ; positivity
  · unfold nodeQ
    have hlq : (l.val : ℕ) ≤ 1791 := by exact_mod_cast hll
    have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlq hp) (by norm_num)
  · intro x hx
    exact cosHiReal_le_threshold_of_nodeQ_1536_le i hx.1.le (by
      have hhi : (nodeQ RatInterval.piHi 2048 (1791 : Fin 2049) : ℚ) ≤
          RatInterval.piHi := by
        unfold nodeQ
        norm_num [RatInterval.piHi]
      exact hx.2.trans hhi)

theorem cosHiNLag_nodeQ_1792_le_threshold (i : Fin 9) :
    cosHiNLag (nodeQ RatInterval.piHi 2048 1792) ≤
      (2 * mu (nextSite i) : ℚ) / (19 / 50 : ℚ) ^ 2 := by
  fin_cases i <;> norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ, mu, nextSite, ringSite, nextRing]

theorem cosHiReal_le_threshold_of_nodeQ_1792_le (i : Fin 9) {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 1792 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ 2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 := by
  let q : ℚ := nodeQ RatInterval.piHi 2048 1792
  have hq3 : 3 * Real.pi / 4 ≤ (q : ℝ) := by
    dsimp [q]
    norm_num [nodeQ, RatInterval.piHi]
  have htail : (-(2 / 3) : ℝ) ≤
      (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    fin_cases i <;> norm_num [mu, nextSite, ringSite, nextRing]
  exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le
    (hq3.trans hx0) hx).trans htail

theorem sectorValue_dec_of_bin7 (i : Fin 9) {k l : Fin 2049}
    (hklo : 1792 ≤ k.val) (hkl : k.val ≤ l.val) (hll : l.val ≤ 2048) :
    sectorValue i l ≤ sectorValue i k := by
  have ha : nodeBin k = nodeBin l := by
    rw [nodeBin_eq_seven_of_mem_bin7 (by omega) (by omega),
      nodeBin_eq_seven_of_mem_bin7 (by omega) (by omega)]
  apply sectorValue_le_of_cos_le i k l ha
    (s := (nodeQ RatInterval.piHi 2048 (1792 : Fin 2049) : ℚ))
    (t := (nodeQ RatInterval.piHi 2048 (2048 : Fin 2049) : ℚ))
  · unfold nodeQ; positivity
  · unfold nodeQ
    have hkq : ((1792 : Fin 2049).val : ℚ) ≤ (k.val : ℚ) := by exact_mod_cast hklo
    have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkq hp) (by norm_num)
  · unfold nodeQ; positivity
  · unfold nodeQ
    have hlq : (l.val : ℕ) ≤ 2048 := by exact_mod_cast hll
    have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlq hp) (by norm_num)
  · intro x hx
    exact cosHiReal_le_threshold_of_nodeQ_1792_le i hx.1.le (by
      have hhi : (nodeQ RatInterval.piHi 2048 (2048 : Fin 2049) : ℚ) ≤
          RatInterval.piHi := by
        unfold nodeQ
        norm_num [RatInterval.piHi]
      exact hx.2.trans hhi)

theorem sectorBinWitness_bin6_eq_1536 (i : Fin 9) :
    (sectorBinWitness i 6).val = 1536 := by
  fin_cases i <;> norm_num [sectorBinWitness]

theorem sectorBinWitness_bin7_eq_1792 (i : Fin 9) :
    (sectorBinWitness i 7).val = 1792 := by
  fin_cases i <;> norm_num [sectorBinWitness]

theorem sectorAt_bin6_inc (i : Fin 9) (n : ℕ)
    (hlo : binFirst (6 : Fin 8) ≤ n) (hn : n < (sectorBinWitness i 6).val) :
    sectorAt i n ≤ sectorAt i (n + 1) := by
  rw [sectorBinWitness_bin6_eq_1536 i] at hn
  norm_num [binFirst] at hlo
  omega

theorem sectorAt_bin6_dec (i : Fin 9) (n : ℕ) (hlo : 1536 ≤ n)
    (hn : n < binLast (6 : Fin 8)) :
    sectorAt i (n + 1) ≤ sectorAt i n := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_dec_of_bin6 i
    (k := (⟨n, by omega⟩ : Fin 2049))
    (l := (⟨n + 1, by omega⟩ : Fin 2049)) (by omega) (by omega) (by
      norm_num [binLast, binHi] at hn ⊢
      omega)
  simpa [sectorAt, hn0, hn1] using h

theorem sectorAt_bin6_unimodal (i : Fin 9) :
    binFirst (6 : Fin 8) ≤ (sectorBinWitness i 6).val ∧
      (sectorBinWitness i 6).val ≤ binLast (6 : Fin 8) ∧
      (∀ n, binFirst (6 : Fin 8) ≤ n → n < (sectorBinWitness i 6).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 6).val ≤ n → n < binLast (6 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  rw [sectorBinWitness_bin6_eq_1536 i]
  refine ⟨by norm_num [binFirst], by norm_num [binLast, binHi], ?_, ?_⟩
  · intro n hnlo hnw
    exact sectorAt_bin6_inc i n hnlo hnw
  · intro n hnw hnlast
    exact sectorAt_bin6_dec i n (by omega) hnlast

theorem sectorAt_bin7_inc (i : Fin 9) (n : ℕ)
    (hlo : binFirst (7 : Fin 8) ≤ n) (hn : n < (sectorBinWitness i 7).val) :
    sectorAt i n ≤ sectorAt i (n + 1) := by
  rw [sectorBinWitness_bin7_eq_1792 i] at hn
  norm_num [binFirst] at hlo
  omega

theorem sectorAt_bin7_dec (i : Fin 9) (n : ℕ) (hlo : 1792 ≤ n)
    (hn : n < binLast (7 : Fin 8)) :
    sectorAt i (n + 1) ≤ sectorAt i n := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_dec_of_bin7 i
    (k := (⟨n, by omega⟩ : Fin 2049))
    (l := (⟨n + 1, by omega⟩ : Fin 2049)) (by omega) (by omega) (by
      norm_num [binLast, binHi] at hn ⊢
      omega)
  simpa [sectorAt, hn0, hn1] using h

theorem sectorAt_bin7_unimodal (i : Fin 9) :
    binFirst (7 : Fin 8) ≤ (sectorBinWitness i 7).val ∧
      (sectorBinWitness i 7).val ≤ binLast (7 : Fin 8) ∧
      (∀ n, binFirst (7 : Fin 8) ≤ n → n < (sectorBinWitness i 7).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 7).val ≤ n → n < binLast (7 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  rw [sectorBinWitness_bin7_eq_1792 i]
  refine ⟨by norm_num [binFirst], by norm_num [binLast, binHi], ?_, ?_⟩
  · intro n hnlo hnw
    exact sectorAt_bin7_inc i n hnlo hnw
  · intro n hnw hnlast
    exact sectorAt_bin7_dec i n (by omega) hnlast

end N11Formalization.SevenClassQ0Deg3SectorBins67AllRows
#check @N11Formalization.SevenClassQ0Deg3SectorBins67AllRows.sectorAt_bin6_unimodal
#check @N11Formalization.SevenClassQ0Deg3SectorBins67AllRows.sectorAt_bin7_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBins67AllRows.sectorAt_bin6_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBins67AllRows.sectorAt_bin7_unimodal
