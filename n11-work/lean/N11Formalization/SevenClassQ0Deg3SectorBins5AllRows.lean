import N11Formalization.SevenClassQ0Deg3SectorBins4AllRows
import N11Formalization.SevenClassQ0Deg3SectorBin5

/-! Lane A: the complete shape of bin 5 for every sector row.

The audited witness is the first grid point `1280` in every row, so the
increasing half is vacuous.  The cosine upper bracket at `1280` lies below
each row's exact derivative threshold, proving the decreasing half. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBins5AllRows

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3EdgeShape
open SevenClassQ0Deg3SectorBin5
open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness
open SevenClassQ0Deg3SectorCalculus
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables
open N11Formalization.ActualRingLinkBoundaryData

theorem cosHiNLag_nodeQ_1280_le_threshold (i : Fin 9) :
    cosHiNLag (nodeQ RatInterval.piHi 2048 1280) ≤
      (2 * mu (nextSite i) : ℚ) / (19 / 50 : ℚ) ^ 2 := by
  fin_cases i <;> norm_num [cosHiNLag, cosTQ, nodeQ, RatInterval.piHi,
    Finset.sum_range_succ, mu, nextSite, ringSite, nextRing]

theorem cosHiReal_le_threshold_of_nodeQ_1280_le (i : Fin 9) {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 1280 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ 2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 := by
  let q : ℚ := nodeQ RatInterval.piHi 2048 1280
  have hq0 : (0 : ℚ) ≤ q := by unfold q nodeQ; positivity
  have hq3 : (q : ℝ) ≤ 3 * Real.pi / 4 := by
    dsimp [q]
    norm_num [nodeQ, RatInterval.piHi]
  have hcast : ((cosHiNLag q : ℚ) : ℝ) = cosHiReal (q : ℝ) := by
    rw [cosHiNLag_cast, cosHiReal]
    have hq0R : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
    rw [abs_of_nonneg hq0R]
  have hval : cosHiReal (q : ℝ) ≤
      (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    rw [← hcast]
    exact_mod_cast cosHiNLag_nodeQ_1280_le_threshold i
  have htail : (-(2 / 3) : ℝ) ≤
      (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    fin_cases i <;> norm_num [mu, nextSite, ringSite, nextRing]
  by_cases h34 : x ≤ 3 * Real.pi / 4
  · have hanti := cosHiReal_antitoneOn_up_to_three_pi_div_four hq0 hq3
    exact (hanti ⟨le_rfl, hq3⟩ ⟨hx0, h34⟩ hx0).trans hval
  · exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le
      (le_of_lt (lt_of_not_ge h34)) hx).trans htail

theorem sectorValue_dec_of_bin5 (i : Fin 9) {k l : Fin 2049}
    (hklo : 1280 ≤ k.val) (hkl : k.val ≤ l.val) (hll : l.val ≤ 1535) :
    sectorValue i l ≤ sectorValue i k := by
  have ha : nodeBin k = nodeBin l := by
    rw [nodeBin_eq_five_of_mem_bin5 (by omega) (by omega),
      nodeBin_eq_five_of_mem_bin5 (by omega) (by omega)]
  apply sectorValue_le_of_cos_le i k l ha
    (s := (nodeQ RatInterval.piHi 2048 (1280 : Fin 2049) : ℚ))
    (t := (nodeQ RatInterval.piHi 2048 (1535 : Fin 2049) : ℚ))
  · unfold nodeQ; positivity
  · unfold nodeQ
    have hkq : ((1280 : Fin 2049).val : ℚ) ≤ (k.val : ℚ) := by exact_mod_cast hklo
    have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkq hp) (by norm_num)
  · unfold nodeQ; positivity
  · unfold nodeQ
    have hlq : (l.val : ℕ) ≤ 1535 := by exact_mod_cast hll
    have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlq hp) (by norm_num)
  · intro x hx
    exact cosHiReal_le_threshold_of_nodeQ_1280_le i hx.1.le (by
      have hhi : (nodeQ RatInterval.piHi 2048 (1535 : Fin 2049) : ℚ) ≤
          RatInterval.piHi := by
        unfold nodeQ
        norm_num [RatInterval.piHi]
      exact hx.2.trans hhi)

theorem sectorBinWitness_bin5_eq_1280 (i : Fin 9) :
    (sectorBinWitness i 5).val = 1280 := by
  fin_cases i <;> norm_num [sectorBinWitness]

theorem sectorAt_bin5_inc (i : Fin 9) (n : ℕ)
    (hlo : binFirst (5 : Fin 8) ≤ n) (hn : n < (sectorBinWitness i 5).val) :
    sectorAt i n ≤ sectorAt i (n + 1) := by
  rw [sectorBinWitness_bin5_eq_1280 i] at hn
  norm_num [binFirst] at hlo
  omega

theorem sectorAt_bin5_dec (i : Fin 9) (n : ℕ) (hlo : 1280 ≤ n)
    (hn : n < binLast (5 : Fin 8)) :
    sectorAt i (n + 1) ≤ sectorAt i n := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_dec_of_bin5 i
    (k := (⟨n, by omega⟩ : Fin 2049))
    (l := (⟨n + 1, by omega⟩ : Fin 2049)) (by omega) (by omega) (by
      norm_num [binLast, binHi] at hn ⊢
      omega)
  simpa [sectorAt, hn0, hn1] using h

theorem sectorAt_bin5_unimodal (i : Fin 9) :
    binFirst (5 : Fin 8) ≤ (sectorBinWitness i 5).val ∧
      (sectorBinWitness i 5).val ≤ binLast (5 : Fin 8) ∧
      (∀ n, binFirst (5 : Fin 8) ≤ n → n < (sectorBinWitness i 5).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 5).val ≤ n → n < binLast (5 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  rw [sectorBinWitness_bin5_eq_1280 i]
  refine ⟨by norm_num [binFirst], by norm_num [binLast, binHi], ?_, ?_⟩
  · intro n hnlo hnw
    exact sectorAt_bin5_inc i n hnlo hnw
  · intro n hnw hnlast
    exact sectorAt_bin5_dec i n (by omega) hnlast

end N11Formalization.SevenClassQ0Deg3SectorBins5AllRows
#check @N11Formalization.SevenClassQ0Deg3SectorBins5AllRows.sectorAt_bin5_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBins5AllRows.sectorAt_bin5_unimodal
