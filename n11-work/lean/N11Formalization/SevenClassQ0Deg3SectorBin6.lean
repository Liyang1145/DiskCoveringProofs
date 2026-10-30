import N11Formalization.SevenClassQ0Deg3SectorBin5

/-! Lane A: the complete shape of row 0, bin 6.

The audited witness `1536` is the first grid point of the bin, so the
increasing half is vacuous.  On the full bin the cosine upper bracket lies
below row 0's exact derivative threshold; this proves the decreasing half
through `1791`. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBin6

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3Cos
open SevenClassQ0Deg3EdgeShape
open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness
open SevenClassQ0Deg3SectorCalculus
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables
open N11Formalization.ActualRingLinkBoundaryData

theorem nodeBin_eq_six_of_mem_bin6 {k : Fin 2049}
    (hlo : 1536 ≤ k.val) (hhi : k.val ≤ 1791) : nodeBin k = nodeBinAt 6 := by
  have hdiv : k.val / 256 = 6 := by omega
  simp [nodeBin, binIndex, hdiv, nodeBinAt]

theorem cosHiNLag_nodeQ_1536_le_row_zero_ratio :
    cosHiNLag (nodeQ RatInterval.piHi 2048 1536) ≤
      (2 * mu (nextSite 0)) / (19 / 50 : ℚ) ^ 2 := by
  norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ, mu, nextSite, ringSite, nextRing]

theorem cosHiReal_le_row_zero_ratio_of_nodeQ_1536_le {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 1536 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ (2 * ((mu (nextSite 0) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
  let q : ℚ := nodeQ RatInterval.piHi 2048 1536
  have hq3 : 3 * Real.pi / 4 ≤ (q : ℝ) := by
    dsimp [q]
    norm_num [nodeQ, RatInterval.piHi]
  have htail : (-(2 / 3) : ℝ) ≤
      (2 * ((mu (nextSite 0) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    norm_num [mu, nextSite, ringSite, nextRing]
  exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le
    (hq3.trans hx0) hx).trans htail

theorem sectorValue_zero_dec_of_bin6 {k l : Fin 2049}
    (hklo : 1536 ≤ k.val) (hkl : k.val ≤ l.val) (hll : l.val ≤ 1791) :
    sectorValue 0 l ≤ sectorValue 0 k := by
  have ha : nodeBin k = nodeBin l := by
    rw [nodeBin_eq_six_of_mem_bin6 (by omega) (by omega),
      nodeBin_eq_six_of_mem_bin6 (by omega) (by omega)]
  apply sectorValue_le_of_cos_le 0 k l ha
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
    exact cosHiReal_le_row_zero_ratio_of_nodeQ_1536_le hx.1.le (by
      have hhi : (nodeQ RatInterval.piHi 2048 (1791 : Fin 2049) : ℚ) ≤
          RatInterval.piHi := by
        unfold nodeQ
        norm_num [RatInterval.piHi]
      exact hx.2.trans hhi)

theorem sectorAt_zero_bin6_inc (n : ℕ) (hlo : binFirst (6 : Fin 8) ≤ n)
    (hn : n < (sectorBinWitness 0 6).val) :
    sectorAt 0 n ≤ sectorAt 0 (n + 1) := by
  norm_num [sectorBinWitness, binFirst] at hlo hn
  omega

theorem sectorAt_zero_bin6_dec (n : ℕ) (hlo : 1536 ≤ n)
    (hn : n < binLast (6 : Fin 8)) :
    sectorAt 0 (n + 1) ≤ sectorAt 0 n := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_zero_dec_of_bin6
    (k := (⟨n, by omega⟩ : Fin 2049))
    (l := (⟨n + 1, by omega⟩ : Fin 2049)) (by omega) (by omega) (by
      norm_num [binLast, binHi] at hn ⊢
      omega)
  simpa [sectorAt, hn0, hn1] using h

theorem sectorAt_zero_bin6_unimodal :
    binFirst (6 : Fin 8) ≤ (sectorBinWitness 0 6).val ∧
      (sectorBinWitness 0 6).val ≤ binLast (6 : Fin 8) ∧
      (∀ n, binFirst (6 : Fin 8) ≤ n → n < (sectorBinWitness 0 6).val →
        sectorAt 0 n ≤ sectorAt 0 (n + 1)) ∧
      (∀ n, (sectorBinWitness 0 6).val ≤ n → n < binLast (6 : Fin 8) →
        sectorAt 0 (n + 1) ≤ sectorAt 0 n) := by
  refine ⟨by norm_num [sectorBinWitness, binFirst],
    by norm_num [sectorBinWitness, binLast, binHi], ?_, ?_⟩
  · intro n hnlo hnw
    exact sectorAt_zero_bin6_inc n hnlo hnw
  · intro n hnw hnlast
    exact sectorAt_zero_bin6_dec n (by
      norm_num [sectorBinWitness] at hnw
      omega) hnlast

end N11Formalization.SevenClassQ0Deg3SectorBin6
#check @N11Formalization.SevenClassQ0Deg3SectorBin6.sectorAt_zero_bin6_dec
#check @N11Formalization.SevenClassQ0Deg3SectorBin6.sectorAt_zero_bin6_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBin6.sectorAt_zero_bin6_dec
#print axioms N11Formalization.SevenClassQ0Deg3SectorBin6.sectorAt_zero_bin6_unimodal
