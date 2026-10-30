import N11Formalization.SevenClassQ0Deg3SectorBins2AllRows
import N11Formalization.SevenClassQ0Deg3SectorBin3

/-! Lane A: the complete shape of bin 3 for every sector row.

Rows 0 and 1 peak at the first grid point `768`, so their increasing half is
vacuous and the exact cosine upper crossing pays the decreasing half.  Rows
2--8 peak at the endpoint `1023`, so their decreasing half is vacuous and the
degree-14 Taylor prefix through `1023` pays the increasing half. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBins3AllRows

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3EdgeShape
open SevenClassQ0Deg3SectorBin3
open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness
open SevenClassQ0Deg3SectorCalculus
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables
open N11Formalization.ActualRingLinkBoundaryData

theorem row_le_one_cosT14_nodeQ_768_le_threshold (i : Fin 9)
    (hi : i.val ≤ 1) :
    cosTQ 14 (nodeQ RatInterval.piHi 2048 768) ≤
      (2 * mu (nextSite i) : ℚ) / (19 / 50 : ℚ) ^ 2 := by
  fin_cases i <;> norm_num [mu, nextSite, ringSite, nextRing, cosTQ, nodeQ,
    RatInterval.piHi, Finset.sum_range_succ] at hi ⊢

theorem row_ge_two_threshold_lt_cosT14_nodeQ_1023 (i : Fin 9)
    (hi : 2 ≤ i.val) :
    (2 * mu (nextSite i) : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 1023) := by
  fin_cases i <;> norm_num [mu, nextSite, ringSite, nextRing, cosTQ, nodeQ,
    RatInterval.piHi, Finset.sum_range_succ] at hi ⊢

theorem row_le_one_cosHiReal_le_threshold_of_nodeQ_768_le (i : Fin 9)
    (hi : i.val ≤ 1) {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 768 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ 2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 := by
  let q : ℚ := nodeQ RatInterval.piHi 2048 768
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
    exact_mod_cast row_le_one_cosT14_nodeQ_768_le_threshold i hi
  have htail : (-(2 / 3) : ℝ) ≤
      (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    fin_cases i <;> norm_num [mu, nextSite, ringSite, nextRing] at hi ⊢
  by_cases h34 : x ≤ 3 * Real.pi / 4
  · have hanti := cosHiReal_antitoneOn_up_to_three_pi_div_four hq0 hq3
    exact (hanti ⟨le_rfl, hq3⟩ ⟨hx0, h34⟩ hx0).trans hval
  · exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le
      (le_of_lt (lt_of_not_ge h34)) hx).trans htail

theorem row_ge_two_threshold_le_cosHiReal_of_prefix_to_1023 (i : Fin 9)
    (hi : 2 ≤ i.val) {x : ℝ}
    (hx0 : 0 ≤ x)
    (hx1 : x ≤ (nodeQ RatInterval.piHi 2048 (1023 : Fin 2049) : ℚ)) :
    2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 ≤ cosHiReal x := by
  have hq_pi2 : (nodeQ RatInterval.piHi 2048 1023 : ℚ) ≤ Real.pi / 2 := by
    norm_num [nodeQ, RatInterval.piHi]
  have hmono := cosT14_antitoneOn
    (show (nodeQ RatInterval.piHi 2048 1023 : ℚ) ∈ Set.Icc 0 (Real.pi / 2) by
      exact ⟨by positivity, hq_pi2⟩)
    (show x ∈ Set.Icc 0 (Real.pi / 2) by
      exact ⟨hx0, hx1.trans hq_pi2⟩)
    hx1
  have hrat : (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 <
      (cosTQ 14 (nodeQ RatInterval.piHi 2048 1023) : ℝ) := by
    exact_mod_cast row_ge_two_threshold_lt_cosT14_nodeQ_1023 i hi
  have htail : 0 ≤ x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) := by positivity
  have hct : cosT 14 x ≤
      cosT 14 (nodeQ RatInterval.piHi 2048 1023 : ℚ) := hmono hx0
  unfold cosHiReal
  linarith

theorem sectorAt_bin3_dec_of_le_one (i : Fin 9) (hi : i.val ≤ 1)
    (n : ℕ) (hlo : 768 ≤ n) (hn : n < binLast (3 : Fin 8)) :
    sectorAt i (n + 1) ≤ sectorAt i n := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_le_of_cos_le i
    (⟨n, by omega⟩ : Fin 2049) (⟨n + 1, by omega⟩ : Fin 2049)
    (by
      rw [nodeBin_eq_three_of_mem_bin3 (by omega) (by omega),
        nodeBin_eq_three_of_mem_bin3 (by omega) (by omega)])
    (s := (nodeQ RatInterval.piHi 2048 768 : ℚ))
    (t := (nodeQ RatInterval.piHi 2048 1023 : ℚ))
    (by unfold nodeQ; positivity)
    (by
      unfold nodeQ
      have hkq : ((768 : Fin 2049).val : ℚ) ≤ (n : ℚ) := by exact_mod_cast hlo
      have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkq hp) (by norm_num))
    (by unfold nodeQ; positivity)
    (by
      unfold nodeQ
      norm_num [binLast, binHi] at hn
      have hlq : ((n + 1 : ℕ) : ℚ) ≤ (1023 : ℕ) := by
        exact_mod_cast (by omega : n + 1 ≤ 1023)
      have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlq hp) (by norm_num))
    (by
      intro x hx
      exact row_le_one_cosHiReal_le_threshold_of_nodeQ_768_le i hi hx.1 (by
        have hhi : (nodeQ RatInterval.piHi 2048 (1023 : Fin 2049) : ℚ) ≤
            RatInterval.piHi := by norm_num [nodeQ, RatInterval.piHi]
        exact hx.2.trans hhi))
  simpa [sectorAt, hn0, hn1] using h

theorem sectorAt_bin3_inc_of_ge_two (i : Fin 9) (hi : 2 ≤ i.val)
    (n : ℕ) (hlo : 768 ≤ n) (hn : n < 1023) :
    sectorAt i n ≤ sectorAt i (n + 1) := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_le_of_cos_ge i
    (⟨n, by omega⟩ : Fin 2049) (⟨n + 1, by omega⟩ : Fin 2049)
    (by
      rw [nodeBin_eq_three_of_mem_bin3 (by omega) (by omega),
        nodeBin_eq_three_of_mem_bin3 (by omega) (by omega)])
    (s := (nodeQ RatInterval.piHi 2048 768 : ℚ))
    (t := (nodeQ RatInterval.piHi 2048 1023 : ℚ))
    (by unfold nodeQ; positivity)
    (by
      unfold nodeQ
      have hkq : ((768 : Fin 2049).val : ℚ) ≤ (n : ℚ) := by exact_mod_cast hlo
      have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkq hp) (by norm_num))
    (by unfold nodeQ; positivity)
    (by
      unfold nodeQ
      have hlq : ((n + 1 : ℕ) : ℚ) ≤ (1023 : ℕ) := by exact_mod_cast (by omega)
      have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlq hp) (by norm_num))
    (by
      intro x hx
      exact row_ge_two_threshold_le_cosHiReal_of_prefix_to_1023 i hi hx.1 (by
        have hhi : (nodeQ RatInterval.piHi 2048 (1023 : Fin 2049) : ℚ) ≤
            RatInterval.piHi := by norm_num [nodeQ, RatInterval.piHi]
        exact hx.2.trans hhi))
  simpa [sectorAt, hn0, hn1] using h

theorem sectorBinWitness_bin3_eq_768_of_le_one (i : Fin 9)
    (hi : i.val ≤ 1) : (sectorBinWitness i 3).val = 768 := by
  fin_cases i <;> norm_num [sectorBinWitness] at hi ⊢

theorem sectorBinWitness_bin3_eq_1023_of_ge_two (i : Fin 9)
    (hi : 2 ≤ i.val) : (sectorBinWitness i 3).val = 1023 := by
  fin_cases i <;> norm_num [sectorBinWitness] at hi ⊢

theorem sectorAt_bin3_unimodal_of_le_one (i : Fin 9) (hi : i.val ≤ 1) :
    binFirst (3 : Fin 8) ≤ (sectorBinWitness i 3).val ∧
      (sectorBinWitness i 3).val ≤ binLast (3 : Fin 8) ∧
      (∀ n, binFirst (3 : Fin 8) ≤ n → n < (sectorBinWitness i 3).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 3).val ≤ n → n < binLast (3 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  rw [sectorBinWitness_bin3_eq_768_of_le_one i hi]
  refine ⟨by norm_num [binFirst], by norm_num [binLast, binHi], ?_, ?_⟩
  · intro n hnlo hnw
    norm_num [binFirst] at hnlo
    omega
  · intro n hnw hnlast
    exact sectorAt_bin3_dec_of_le_one i hi n (by omega) hnlast

theorem sectorAt_bin3_unimodal_of_ge_two (i : Fin 9) (hi : 2 ≤ i.val) :
    binFirst (3 : Fin 8) ≤ (sectorBinWitness i 3).val ∧
      (sectorBinWitness i 3).val ≤ binLast (3 : Fin 8) ∧
      (∀ n, binFirst (3 : Fin 8) ≤ n → n < (sectorBinWitness i 3).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 3).val ≤ n → n < binLast (3 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  rw [sectorBinWitness_bin3_eq_1023_of_ge_two i hi]
  refine ⟨by norm_num [binFirst], by norm_num [binLast, binHi], ?_, ?_⟩
  · intro n hnlo hnw
    exact sectorAt_bin3_inc_of_ge_two i hi n (by omega) (by omega)
  · intro _ _ hnlast
    norm_num [binLast, binHi] at hnlast

theorem sectorAt_bin3_unimodal (i : Fin 9) :
    binFirst (3 : Fin 8) ≤ (sectorBinWitness i 3).val ∧
      (sectorBinWitness i 3).val ≤ binLast (3 : Fin 8) ∧
      (∀ n, binFirst (3 : Fin 8) ≤ n → n < (sectorBinWitness i 3).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 3).val ≤ n → n < binLast (3 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  by_cases hi : i.val ≤ 1
  · exact sectorAt_bin3_unimodal_of_le_one i hi
  · exact sectorAt_bin3_unimodal_of_ge_two i (by omega)

end N11Formalization.SevenClassQ0Deg3SectorBins3AllRows
#check @N11Formalization.SevenClassQ0Deg3SectorBins3AllRows.sectorAt_bin3_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBins3AllRows.sectorAt_bin3_unimodal
