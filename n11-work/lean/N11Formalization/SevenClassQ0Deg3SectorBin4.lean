import N11Formalization.SevenClassQ0Deg3SectorBin3

/-! Lane A: the complete shape of row 0, bin 4.

The audited witness `1024` is the first grid point of the bin, so the
increasing half is vacuous.  On the full bin the cosine upper bracket lies
below row 0's exact derivative threshold; this proves the decreasing half
through `1279`. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBin4

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

theorem nodeBin_eq_four_of_mem_bin4 {k : Fin 2049}
    (hlo : 1024 ≤ k.val) (hhi : k.val ≤ 1279) : nodeBin k = nodeBinAt 4 := by
  have hdiv : k.val / 256 = 4 := by omega
  simp [nodeBin, binIndex, hdiv, nodeBinAt]

theorem cosHiNLag_nodeQ_1024_le_row_zero_ratio :
    cosHiNLag (nodeQ RatInterval.piHi 2048 1024) ≤
      (2 * mu (nextSite 0)) / (19 / 50 : ℚ) ^ 2 := by
  norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ, mu, nextSite, ringSite, nextRing]

theorem cosHiReal_le_row_zero_ratio_of_nodeQ_1024_le {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 1024 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ (2 * ((mu (nextSite 0) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
  let q : ℚ := nodeQ RatInterval.piHi 2048 1024
  have hq0 : (0 : ℚ) ≤ q := by unfold q nodeQ; positivity
  have hq3 : (q : ℝ) ≤ 3 * Real.pi / 4 := by
    dsimp [q]
    norm_num [nodeQ, RatInterval.piHi]
  have hcast : ((cosHiNLag q : ℚ) : ℝ) = cosHiReal (q : ℝ) := by
    rw [cosHiNLag_cast, cosHiReal]
    have hq0R : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
    rw [abs_of_nonneg hq0R]
  have hval : cosHiReal (q : ℝ) ≤
      (2 * ((mu (nextSite 0) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    rw [← hcast]
    exact_mod_cast cosHiNLag_nodeQ_1024_le_row_zero_ratio
  have htail : (-(2 / 3) : ℝ) ≤
      (2 * ((mu (nextSite 0) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    norm_num [mu, nextSite, ringSite, nextRing]
  by_cases h34 : x ≤ 3 * Real.pi / 4
  · have hanti := cosHiReal_antitoneOn_up_to_three_pi_div_four hq0 hq3
    exact (hanti ⟨le_rfl, hq3⟩ ⟨hx0, h34⟩ hx0).trans hval
  · exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le
      (le_of_lt (lt_of_not_ge h34)) hx).trans htail

theorem sectorValue_zero_dec_of_bin4 {k l : Fin 2049}
    (hklo : 1024 ≤ k.val) (hkl : k.val ≤ l.val) (hll : l.val ≤ 1279) :
    sectorValue 0 l ≤ sectorValue 0 k := by
  have ha : nodeBin k = nodeBin l := by
    rw [nodeBin_eq_four_of_mem_bin4 (by omega) (by omega),
      nodeBin_eq_four_of_mem_bin4 (by omega) (by omega)]
  apply sectorValue_le_of_cos_le 0 k l ha
    (s := (nodeQ RatInterval.piHi 2048 (1024 : Fin 2049) : ℚ))
    (t := (nodeQ RatInterval.piHi 2048 (1279 : Fin 2049) : ℚ))
  · unfold nodeQ; positivity
  · unfold nodeQ
    have hkq : ((1024 : Fin 2049).val : ℚ) ≤ (k.val : ℚ) := by exact_mod_cast hklo
    have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkq hp) (by norm_num)
  · unfold nodeQ; positivity
  · unfold nodeQ
    have hlq : (l.val : ℚ) ≤ (1279 : ℕ) := by exact_mod_cast hll
    have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlq hp) (by norm_num)
  · intro x hx
    exact cosHiReal_le_row_zero_ratio_of_nodeQ_1024_le hx.1.le (by
      have hhi : (nodeQ RatInterval.piHi 2048 (1279 : Fin 2049) : ℚ) ≤
          RatInterval.piHi := by
        unfold nodeQ
        norm_num [RatInterval.piHi]
      exact hx.2.trans hhi)

theorem sectorAt_zero_bin4_inc (n : ℕ) (hlo : binFirst (4 : Fin 8) ≤ n)
    (hn : n < (sectorBinWitness 0 4).val) :
    sectorAt 0 n ≤ sectorAt 0 (n + 1) := by
  norm_num [sectorBinWitness, binFirst] at hlo hn
  omega

theorem sectorAt_zero_bin4_dec (n : ℕ) (hlo : 1024 ≤ n)
    (hn : n < binLast (4 : Fin 8)) :
    sectorAt 0 (n + 1) ≤ sectorAt 0 n := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_zero_dec_of_bin4
    (k := (⟨n, by omega⟩ : Fin 2049))
    (l := (⟨n + 1, by omega⟩ : Fin 2049)) (by omega) (by omega) (by
      norm_num [binLast, binHi] at hn ⊢
      omega)
  simpa [sectorAt, hn0, hn1] using h

theorem sectorAt_zero_bin4_unimodal :
    binFirst (4 : Fin 8) ≤ (sectorBinWitness 0 4).val ∧
      (sectorBinWitness 0 4).val ≤ binLast (4 : Fin 8) ∧
      (∀ n, binFirst (4 : Fin 8) ≤ n → n < (sectorBinWitness 0 4).val →
        sectorAt 0 n ≤ sectorAt 0 (n + 1)) ∧
      (∀ n, (sectorBinWitness 0 4).val ≤ n → n < binLast (4 : Fin 8) →
        sectorAt 0 (n + 1) ≤ sectorAt 0 n) := by
  refine ⟨by norm_num [sectorBinWitness, binFirst],
    by norm_num [sectorBinWitness, binLast, binHi], ?_, ?_⟩
  · intro n hnlo hnw
    exact sectorAt_zero_bin4_inc n hnlo hnw
  · intro n hnw hnlast
    exact sectorAt_zero_bin4_dec n (by
      norm_num [sectorBinWitness] at hnw
      omega) hnlast

end N11Formalization.SevenClassQ0Deg3SectorBin4
#check @N11Formalization.SevenClassQ0Deg3SectorBin4.sectorAt_zero_bin4_dec
#check @N11Formalization.SevenClassQ0Deg3SectorBin4.sectorAt_zero_bin4_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBin4.sectorAt_zero_bin4_dec
#print axioms N11Formalization.SevenClassQ0Deg3SectorBin4.sectorAt_zero_bin4_unimodal
