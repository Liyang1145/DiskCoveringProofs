import N11Formalization.SevenClassQ0Deg3SectorBins3AllRows
import N11Formalization.SevenClassQ0Deg3SectorBin4

/-! Lane A: the complete shape of bin 4 for every sector row.

Rows 0 and 1 decrease from the bin start `1024`.  Rows 2--8 have the
row-dependent witnesses `1173,1051,1076,1070,1076,1051,1173`.  Their
calculus prefix ends at `w - 1`; the two grid steps `w - 1 -> w -> w + 1`
are checked exactly, and the decreasing calculus tail starts at `w + 1`. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBins4AllRows

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3EdgeShape
open SevenClassQ0Deg3SectorBin4
open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness
open SevenClassQ0Deg3SectorCalculus
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables
open N11Formalization.ActualRingLinkBoundaryData

theorem row_le_one_cosHiNLag_nodeQ_1024_le_threshold (i : Fin 9)
    (hi : i.val ≤ 1) :
    cosHiNLag (nodeQ RatInterval.piHi 2048 1024) ≤
      (2 * mu (nextSite i) : ℚ) / (19 / 50 : ℚ) ^ 2 := by
  fin_cases i <;> norm_num [mu, nextSite, ringSite, nextRing, cosHiNLag,
    cosTQ, nodeQ, RatInterval.piHi, Finset.sum_range_succ] at hi ⊢

theorem row_le_one_cosHiReal_le_threshold_of_nodeQ_1024_le (i : Fin 9)
    (hi : i.val ≤ 1) {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048 1024 : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ 2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 := by
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
      (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    rw [← hcast]
    exact_mod_cast row_le_one_cosHiNLag_nodeQ_1024_le_threshold i hi
  have htail : (-(2 / 3) : ℝ) ≤
      (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    fin_cases i <;> norm_num [mu, nextSite, ringSite, nextRing] at hi ⊢
  by_cases h34 : x ≤ 3 * Real.pi / 4
  · have hanti := cosHiReal_antitoneOn_up_to_three_pi_div_four hq0 hq3
    exact (hanti ⟨le_rfl, hq3⟩ ⟨hx0, h34⟩ hx0).trans hval
  · exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le
      (le_of_lt (lt_of_not_ge h34)) hx).trans htail

theorem row_ge_two_threshold_lt_cosT14_nodeQ_prev (i : Fin 9)
    (hi : 2 ≤ i.val) :
    (2 * mu (nextSite i) : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048
        ⟨(sectorBinWitness i 4).val - 1, by have := (sectorBinWitness i 4).isLt; omega⟩) := by
  fin_cases i <;> norm_num [sectorBinWitness, mu, nextSite, ringSite, nextRing,
    cosTQ, nodeQ, RatInterval.piHi, Finset.sum_range_succ] at hi ⊢

theorem row_ge_two_cosHiNLag_next_le_threshold (i : Fin 9)
    (hi : 2 ≤ i.val) :
    cosHiNLag (nodeQ RatInterval.piHi 2048
        ⟨(sectorBinWitness i 4).val + 1, by have := (sectorBinWitness i 4).isLt; omega⟩) ≤
      (2 * mu (nextSite i) : ℚ) / (19 / 50 : ℚ) ^ 2 := by
  fin_cases i <;> norm_num [sectorBinWitness, mu, nextSite, ringSite, nextRing,
    cosHiNLag, cosTQ, nodeQ, RatInterval.piHi, Finset.sum_range_succ] at hi ⊢

theorem row_ge_two_threshold_ge_neg_two_thirds (i : Fin 9)
    (hi : 2 ≤ i.val) :
    (-(2 / 3) : ℚ) ≤ (2 * mu (nextSite i) : ℚ) / (19 / 50 : ℚ) ^ 2 := by
  fin_cases i <;> norm_num [mu, nextSite, ringSite, nextRing] at hi ⊢

/-- A strict cosine threshold at the node before a witness pays the analytic
increasing prefix. -/
theorem row_ge_two_threshold_le_cosHiReal_of_prefix_to_prev (i : Fin 9)
    (hi : 2 ≤ i.val) {x : ℝ}
    (hx0 : 0 ≤ x)
    (hx1 : x ≤ (nodeQ RatInterval.piHi 2048
      ⟨(sectorBinWitness i 4).val - 1, by have := (sectorBinWitness i 4).isLt; omega⟩ : ℚ)) :
    2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 ≤ cosHiReal x := by
  let w : Fin 2049 := ⟨(sectorBinWitness i 4).val - 1, by have := (sectorBinWitness i 4).isLt; omega⟩
  have hq3 : (nodeQ RatInterval.piHi 2048 w : ℚ) ≤ 3 * Real.pi / 4 := by
    fin_cases i <;> norm_num [w, sectorBinWitness, nodeQ, RatInterval.piHi] at hi ⊢
  have hmono := cosT14_antitoneOn_three_pi_div_four
    (show (nodeQ RatInterval.piHi 2048 w : ℚ) ∈ Set.Icc 0 (3 * Real.pi / 4) by
      exact ⟨by positivity, hq3⟩)
    (show x ∈ Set.Icc 0 (3 * Real.pi / 4) by
      exact ⟨hx0, hx1.trans hq3⟩)
    hx1
  have hrat : (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 <
      (cosTQ 14 (nodeQ RatInterval.piHi 2048 w) : ℝ) := by
    exact_mod_cast row_ge_two_threshold_lt_cosT14_nodeQ_prev i hi
  have htail : 0 ≤ x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) := by positivity
  have hct : cosT 14 x ≤ cosT 14 (nodeQ RatInterval.piHi 2048 w : ℚ) := hmono hx0
  unfold cosHiReal
  linarith

/-- A node comparison with the exact threshold propagates over the whole
decreasing grid tail. -/
theorem row_ge_two_cosHiReal_le_threshold_of_next_node (i : Fin 9)
    (hi : 2 ≤ i.val) {x : ℝ}
    (hx0 : (nodeQ RatInterval.piHi 2048
      ⟨(sectorBinWitness i 4).val + 1, by have := (sectorBinWitness i 4).isLt; omega⟩ : ℚ) ≤ x)
    (hx : x ≤ (RatInterval.piHi : ℝ)) :
    cosHiReal x ≤ 2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 := by
  let w : Fin 2049 := ⟨(sectorBinWitness i 4).val + 1, by have := (sectorBinWitness i 4).isLt; omega⟩
  have hq0 : (0 : ℚ) ≤ nodeQ RatInterval.piHi 2048 w := by
    unfold nodeQ
    positivity
  have hcast : ((cosHiNLag (nodeQ RatInterval.piHi 2048 w) : ℚ) : ℝ) =
      cosHiReal (nodeQ RatInterval.piHi 2048 w : ℚ) := by
    rw [cosHiNLag_cast, cosHiReal]
    have hq0R : (0 : ℝ) ≤ (nodeQ RatInterval.piHi 2048 w : ℚ) := by
      exact_mod_cast hq0
    rw [abs_of_nonneg hq0R]
  have hvalR : cosHiReal (nodeQ RatInterval.piHi 2048 w : ℚ) ≤
      (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    rw [← hcast]
    exact_mod_cast row_ge_two_cosHiNLag_next_le_threshold i hi
  have htailR : (-(2 / 3) : ℝ) ≤
      (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 := by
    exact_mod_cast row_ge_two_threshold_ge_neg_two_thirds i hi
  have hq3 : (nodeQ RatInterval.piHi 2048 w : ℚ) ≤ 3 * Real.pi / 4 := by
    fin_cases i <;> norm_num [w, sectorBinWitness, nodeQ, RatInterval.piHi] at hi ⊢
  by_cases h34 : x ≤ 3 * Real.pi / 4
  · have hanti := cosHiReal_antitoneOn_up_to_three_pi_div_four hq0 hq3
    exact (hanti ⟨le_rfl, hq3⟩ ⟨hx0, h34⟩ hx0).trans hvalR
  · exact (cosHiReal_le_neg_two_thirds_of_three_pi_div_four_le
      (le_of_lt (lt_of_not_ge h34)) hx).trans htailR

theorem sectorAt_bin4_dec_of_le_one (i : Fin 9) (hi : i.val ≤ 1)
    (n : ℕ) (hlo : 1024 ≤ n) (hn : n < binLast (4 : Fin 8)) :
    sectorAt i (n + 1) ≤ sectorAt i n := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_le_of_cos_le i
    (⟨n, by omega⟩ : Fin 2049) (⟨n + 1, by omega⟩ : Fin 2049)
    (by
      rw [nodeBin_eq_four_of_mem_bin4 (by omega) (by omega),
        nodeBin_eq_four_of_mem_bin4 (by omega) (by omega)])
    (s := (nodeQ RatInterval.piHi 2048 1024 : ℚ))
    (t := (nodeQ RatInterval.piHi 2048 1279 : ℚ))
    (by unfold nodeQ; positivity)
    (by
      unfold nodeQ
      have hkq : ((1024 : Fin 2049).val : ℚ) ≤ (n : ℚ) := by exact_mod_cast hlo
      have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkq hp) (by norm_num))
    (by unfold nodeQ; positivity)
    (by
      unfold nodeQ
      norm_num [binLast, binHi] at hn
      have hlq : ((n + 1 : ℕ) : ℚ) ≤ (1279 : ℕ) := by
        exact_mod_cast (by omega : n + 1 ≤ 1279)
      have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlq hp) (by norm_num))
    (by
      intro x hx
      exact row_le_one_cosHiReal_le_threshold_of_nodeQ_1024_le i hi hx.1 (by
        have hhi : (nodeQ RatInterval.piHi 2048 (1279 : Fin 2049) : ℚ) ≤
            RatInterval.piHi := by norm_num [nodeQ, RatInterval.piHi]
        exact hx.2.trans hhi))
  simpa [sectorAt, hn0, hn1] using h

theorem sectorAt_bin4_exact_steps_of_ge_two (i : Fin 9) (hi : 2 ≤ i.val) :
    sectorAt i ((sectorBinWitness i 4).val - 1) ≤
        sectorAt i (sectorBinWitness i 4).val ∧
      sectorAt i ((sectorBinWitness i 4).val + 1) ≤
        sectorAt i (sectorBinWitness i 4).val := by
  fin_cases i <;> simp at hi ⊢ <;>
    norm_num [sectorAt, sectorValue, sectorUpper, areaUpper, nodeBin,
      nodeBinAt, binIndex, sectorBinWitness, mu, lam, nextSite, ringSite,
      nextRing, nodeQ, sinHiNLag, sinLoNLag, sinTQ, Finset.sum_range_succ,
      RatInterval.piHi]

theorem sectorAt_bin4_inc_of_ge_two (i : Fin 9) (hi : 2 ≤ i.val)
    (n : ℕ) (hlo : 1024 ≤ n) (hn : n < (sectorBinWitness i 4).val) :
    sectorAt i n ≤ sectorAt i (n + 1) := by
  by_cases hprev : n + 1 = (sectorBinWitness i 4).val
  · have hstep := (sectorAt_bin4_exact_steps_of_ge_two i hi).1
    have hsub : (sectorBinWitness i 4).val - 1 = n := by omega
    simpa [hprev, hsub] using hstep
  · have hnprev : n < (sectorBinWitness i 4).val - 1 := by omega
    have hn0 : min n 2048 = n := min_eq_left (by omega)
    have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
    let w : Fin 2049 := ⟨(sectorBinWitness i 4).val - 1, by have := (sectorBinWitness i 4).isLt; omega⟩
    have h := sectorValue_le_of_cos_ge i
      (⟨n, by omega⟩ : Fin 2049) (⟨n + 1, by omega⟩ : Fin 2049)
      (by
        rw [nodeBin_eq_four_of_mem_bin4 (by omega) (by omega),
          nodeBin_eq_four_of_mem_bin4 (by omega) (by omega)])
      (s := (nodeQ RatInterval.piHi 2048 1024 : ℚ))
      (t := (nodeQ RatInterval.piHi 2048 w : ℚ))
      (by unfold nodeQ; positivity)
      (by
        unfold nodeQ
        have hkq : ((1024 : Fin 2049).val : ℚ) ≤ (n : ℚ) := by exact_mod_cast hlo
        have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkq hp) (by norm_num))
      (by unfold nodeQ; positivity)
      (by
        unfold nodeQ w
        have hlq : ((n + 1 : ℕ) : ℚ) ≤
            (((sectorBinWitness i 4).val - 1 : ℕ) : ℚ) := by
          exact_mod_cast (by omega : n + 1 ≤ (sectorBinWitness i 4).val - 1)
        have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlq hp) (by norm_num))
      (by
        intro x hx
        have hq1024 : (0 : ℝ) ≤
            (nodeQ RatInterval.piHi 2048 1024 : ℚ) := by positivity
        exact row_ge_two_threshold_le_cosHiReal_of_prefix_to_prev i hi
          (hq1024.trans (le_of_lt hx.1)) (by
            have hhi : (nodeQ RatInterval.piHi 2048 w : ℚ) ≤ RatInterval.piHi := by
              unfold nodeQ w
              norm_num [RatInterval.piHi]
            exact hx.2.trans hhi))
    simpa [sectorAt, hn0, hn1] using h

theorem sectorAt_bin4_dec_of_ge_two (i : Fin 9) (hi : 2 ≤ i.val)
    (n : ℕ) (hnw : (sectorBinWitness i 4).val ≤ n)
    (hn : n < binLast (4 : Fin 8)) :
    sectorAt i (n + 1) ≤ sectorAt i n := by
  by_cases hpeak : n = (sectorBinWitness i 4).val
  · subst n
    have hstep := (sectorAt_bin4_exact_steps_of_ge_two i hi).2
    simpa using hstep
  · have hnnext : (sectorBinWitness i 4).val + 1 ≤ n := by omega
    have hn0 : min n 2048 = n := min_eq_left (by omega)
    have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
    let w : Fin 2049 := ⟨(sectorBinWitness i 4).val + 1, by have := (sectorBinWitness i 4).isLt; omega⟩
    have h := sectorValue_le_of_cos_le i
      (⟨n, by omega⟩ : Fin 2049) (⟨n + 1, by omega⟩ : Fin 2049)
      (by
        rw [nodeBin_eq_four_of_mem_bin4 (by omega) (by omega),
          nodeBin_eq_four_of_mem_bin4 (by omega) (by omega)])
      (s := (nodeQ RatInterval.piHi 2048 w : ℚ))
      (t := (nodeQ RatInterval.piHi 2048 1279 : ℚ))
      (by unfold nodeQ; positivity)
      (by
        unfold nodeQ w
        have hkq : (((sectorBinWitness i 4).val + 1 : ℕ) : ℚ) ≤ (n : ℚ) := by
          exact_mod_cast hnnext
        have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkq hp) (by norm_num))
      (by unfold nodeQ; positivity)
      (by
        unfold nodeQ
        norm_num [binLast, binHi] at hn
        have hlq : ((n + 1 : ℕ) : ℚ) ≤ (1279 : ℕ) := by
          exact_mod_cast (by omega : n + 1 ≤ 1279)
        have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlq hp) (by norm_num))
      (by
        intro x hx
        exact row_ge_two_cosHiReal_le_threshold_of_next_node i hi hx.1 (by
          have hhi : (nodeQ RatInterval.piHi 2048 (1279 : Fin 2049) : ℚ) ≤
              RatInterval.piHi := by norm_num [nodeQ, RatInterval.piHi]
          exact hx.2.trans hhi))
    simpa [sectorAt, hn0, hn1] using h

theorem sectorBinWitness_bin4_eq_1024_of_le_one (i : Fin 9)
    (hi : i.val ≤ 1) : (sectorBinWitness i 4).val = 1024 := by
  fin_cases i <;> norm_num [sectorBinWitness] at hi ⊢

theorem sectorAt_bin4_unimodal_of_le_one (i : Fin 9) (hi : i.val ≤ 1) :
    binFirst (4 : Fin 8) ≤ (sectorBinWitness i 4).val ∧
      (sectorBinWitness i 4).val ≤ binLast (4 : Fin 8) ∧
      (∀ n, binFirst (4 : Fin 8) ≤ n → n < (sectorBinWitness i 4).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 4).val ≤ n → n < binLast (4 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  rw [sectorBinWitness_bin4_eq_1024_of_le_one i hi]
  refine ⟨by norm_num [binFirst], by norm_num [binLast, binHi], ?_, ?_⟩
  · intro n hnlo hnw
    norm_num [binFirst] at hnlo
    omega
  · intro n hnw hnlast
    exact sectorAt_bin4_dec_of_le_one i hi n (by omega) hnlast

theorem sectorAt_bin4_unimodal_of_ge_two (i : Fin 9) (hi : 2 ≤ i.val) :
    binFirst (4 : Fin 8) ≤ (sectorBinWitness i 4).val ∧
      (sectorBinWitness i 4).val ≤ binLast (4 : Fin 8) ∧
      (∀ n, binFirst (4 : Fin 8) ≤ n → n < (sectorBinWitness i 4).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 4).val ≤ n → n < binLast (4 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  refine ⟨by
      fin_cases i <;> norm_num [sectorBinWitness] at hi ⊢,
    by
      fin_cases i <;> norm_num [sectorBinWitness, binLast, binHi] at hi ⊢, ?_, ?_⟩
  · intro n hnlo hnw
    exact sectorAt_bin4_inc_of_ge_two i hi n (by
      norm_num [binFirst] at hnlo
      omega) hnw
  · intro n hnw hnlast
    exact sectorAt_bin4_dec_of_ge_two i hi n hnw hnlast

theorem sectorAt_bin4_unimodal (i : Fin 9) :
    binFirst (4 : Fin 8) ≤ (sectorBinWitness i 4).val ∧
      (sectorBinWitness i 4).val ≤ binLast (4 : Fin 8) ∧
      (∀ n, binFirst (4 : Fin 8) ≤ n → n < (sectorBinWitness i 4).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 4).val ≤ n → n < binLast (4 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  by_cases hi : i.val ≤ 1
  · exact sectorAt_bin4_unimodal_of_le_one i hi
  · exact sectorAt_bin4_unimodal_of_ge_two i (by omega)

end N11Formalization.SevenClassQ0Deg3SectorBins4AllRows
#check @N11Formalization.SevenClassQ0Deg3SectorBins4AllRows.sectorAt_bin4_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBins4AllRows.sectorAt_bin4_unimodal
