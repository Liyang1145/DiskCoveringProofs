import N11Formalization.SevenClassQ0Deg3SectorBin1

/-! Lane A: the complete shape of row 0, bin 2.

The increasing half ends at the audited witness `543`.  The decreasing half
starts with one exact rational step to node `544` and then uses the proved
cosine tail for the row-0 derivative threshold. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBin2

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3EdgeShape
open SevenClassQ0Deg3EdgeSuffixNonpos
open SevenClassQ0Deg3SectorBin0
open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness
open SevenClassQ0Deg3SectorCalculus
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables
open N11Formalization.ActualRingLinkBoundaryData

theorem nodeBin_eq_two_of_mem_bin2 {k : Fin 2049}
    (hlo : 512 ≤ k.val) (hhi : k.val ≤ 767) : nodeBin k = nodeBinAt 2 := by
  have hdiv : k.val / 256 = 2 := by omega
  simp [nodeBin, binIndex, hdiv, nodeBinAt]

theorem nodeQ_le_543_of_le_543 {k : Fin 2049} (hk : k.val ≤ 543) :
    (nodeQ RatInterval.piHi 2048 k : ℚ) ≤
      (nodeQ RatInterval.piHi 2048 (543 : Fin 2049) : ℚ) := by
  unfold nodeQ
  have hkq : (k.val : ℚ) ≤ (543 : ℕ) := by exact_mod_cast hk
  have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hkq hp) (by norm_num)

theorem sectorValue_zero_le_of_bin2 {k l : Fin 2049}
    (hklo : 512 ≤ k.val) (hkl : k.val ≤ 543)
    (hllo : 512 ≤ l.val) (hll : l.val ≤ 543) :
    sectorValue 0 k ≤ sectorValue 0 l := by
  have ha : nodeBin k = nodeBin l := by
    rw [nodeBin_eq_two_of_mem_bin2 hklo (by omega),
      nodeBin_eq_two_of_mem_bin2 hllo (by omega)]
  apply sectorValue_le_of_cos_ge 0 k l ha
    (s := (0 : ℝ))
    (t := (nodeQ RatInterval.piHi 2048 (543 : Fin 2049) : ℚ))
  · unfold nodeQ; positivity
  · exact nodeQ_le_543_of_le_543 (by omega)
  · unfold nodeQ; positivity
  · exact nodeQ_le_543_of_le_543 (by omega)
  · intro x hx
    exact row_zero_threshold_le_edge_zero.trans
      (edge_ratio_le_cosHiReal_of_prefix 0 543
        (by norm_num [nodeQ, RatInterval.piHi])
        edge_ratio_zero_lt_cosT14_nodeQ_543 hx.1 hx.2)

theorem sectorAt_zero_bin2_inc (n : ℕ) (hlo : 512 ≤ n) (hn : n < 543) :
    sectorAt 0 n ≤ sectorAt 0 (n + 1) := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_zero_le_of_bin2
    (k := (⟨n, by omega⟩ : Fin 2049))
    (l := (⟨n + 1, by omega⟩ : Fin 2049)) hlo (by omega) (by omega) (by omega)
  simpa [sectorAt, hn0, hn1] using h

theorem cosHiNLag_nodeQ_544_le_row_zero_ratio :
    cosHiNLag (nodeQ RatInterval.piHi 2048 544) ≤
      (2 * mu (nextSite 0)) / (19 / 50 : ℚ) ^ 2 := by
  norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ, mu, nextSite, ringSite, nextRing]

theorem cosHiReal_le_row_zero_ratio_of_nodeQ_544_le {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 544 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ (2 * ((mu (nextSite 0) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
  let q : ℚ := nodeQ RatInterval.piHi 2048 544
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
    exact_mod_cast cosHiNLag_nodeQ_544_le_row_zero_ratio
  have htail : (-(2 / 3) : ℝ) ≤
      (2 * ((mu (nextSite 0) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    norm_num [mu, nextSite, ringSite, nextRing]
  by_cases h34 : x ≤ 3 * Real.pi / 4
  · have hanti := cosHiReal_antitoneOn_up_to_three_pi_div_four hq0 hq3
    exact (hanti ⟨le_rfl, hq3⟩ ⟨hx0, h34⟩ hx0).trans hval
  · exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le
      (le_of_lt (lt_of_not_ge h34)) hx).trans htail

theorem sectorValue_zero_dec_of_bin2 {k l : Fin 2049}
    (hklo : 544 ≤ k.val) (hkl : k.val ≤ l.val) (hll : l.val ≤ 767) :
    sectorValue 0 l ≤ sectorValue 0 k := by
  have ha : nodeBin k = nodeBin l := by
    rw [nodeBin_eq_two_of_mem_bin2 (by omega) (by omega),
      nodeBin_eq_two_of_mem_bin2 (by omega) (by omega)]
  apply sectorValue_le_of_cos_le 0 k l ha
    (s := (nodeQ RatInterval.piHi 2048 (544 : Fin 2049) : ℚ))
    (t := (nodeQ RatInterval.piHi 2048 (767 : Fin 2049) : ℚ))
  · unfold nodeQ; positivity
  · unfold nodeQ
    have hkq : ((544 : Fin 2049).val : ℚ) ≤ (k.val : ℚ) := by exact_mod_cast hklo
    have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkq hp) (by norm_num)
  · unfold nodeQ; positivity
  · unfold nodeQ
    have hlq : (l.val : ℚ) ≤ (767 : ℕ) := by exact_mod_cast hll
    have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlq hp) (by norm_num)
  · intro x hx
    exact cosHiReal_le_row_zero_ratio_of_nodeQ_544_le hx.1.le (by
      have hhi : (nodeQ RatInterval.piHi 2048 (767 : Fin 2049) : ℚ) ≤ RatInterval.piHi := by
        unfold nodeQ
        norm_num [RatInterval.piHi]
      exact hx.2.trans hhi)

theorem sectorAt_zero_bin2_dec (n : ℕ) (hlo : 543 ≤ n)
    (hn : n < binLast (2 : Fin 8)) :
    sectorAt 0 (n + 1) ≤ sectorAt 0 n := by
  by_cases h543 : n = 543
  · subst n
    norm_num [sectorAt, sectorValue, sectorUpper, areaUpper, nodeBin, nodeBinAt,
      binIndex, mu, lam, nextSite, nodeQ, sinHiNLag, sinLoNLag, sinTQ,
      Finset.sum_range_succ, RatInterval.piHi]
  have hn544 : 544 ≤ n := by omega
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_zero_dec_of_bin2
    (k := (⟨n, by omega⟩ : Fin 2049))
    (l := (⟨n + 1, by omega⟩ : Fin 2049)) hn544 (by omega) (by
      norm_num [binLast, binHi] at hn ⊢
      omega)
  simpa [sectorAt, hn0, hn1] using h

theorem sectorAt_zero_bin2_unimodal :
    binFirst (2 : Fin 8) ≤ (sectorBinWitness 0 2).val ∧
      (sectorBinWitness 0 2).val ≤ binLast (2 : Fin 8) ∧
      (∀ n, binFirst (2 : Fin 8) ≤ n → n < (sectorBinWitness 0 2).val →
        sectorAt 0 n ≤ sectorAt 0 (n + 1)) ∧
      (∀ n, (sectorBinWitness 0 2).val ≤ n → n < binLast (2 : Fin 8) →
        sectorAt 0 (n + 1) ≤ sectorAt 0 n) := by
  refine ⟨by norm_num [sectorBinWitness, binFirst],
    by norm_num [sectorBinWitness, binLast, binHi], ?_, ?_⟩
  · intro n hnlo hnw
    exact sectorAt_zero_bin2_inc n hnlo (by
      norm_num [sectorBinWitness] at hnw
      omega)
  · intro n hnw hnlast
    exact sectorAt_zero_bin2_dec n (by
      norm_num [sectorBinWitness] at hnw
      omega) hnlast

end N11Formalization.SevenClassQ0Deg3SectorBin2
#check @N11Formalization.SevenClassQ0Deg3SectorBin2.sectorAt_zero_bin2_inc
#check @N11Formalization.SevenClassQ0Deg3SectorBin2.sectorAt_zero_bin2_dec
#check @N11Formalization.SevenClassQ0Deg3SectorBin2.sectorAt_zero_bin2_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBin2.sectorAt_zero_bin2_inc
#print axioms N11Formalization.SevenClassQ0Deg3SectorBin2.sectorAt_zero_bin2_unimodal
