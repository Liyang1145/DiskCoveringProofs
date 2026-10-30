import N11Formalization.SevenClassQ0Deg3SectorBin1

/-! Lane A: the complete shape of bins 0 and 1 for every sector row.

Bins 0 and 1 share the same node-table value, and the cosine prefix through
node 543 dominates the derivative threshold in all nine rows.  Both
audited witnesses (`255` and `511`) are bin endpoints, so both decreasing
halves are vacuous.  This module closes eighteen of the seventy-two
row-bin obligations without making any boundary-jump assumption. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBins01AllRows

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3EdgeShape
open SevenClassQ0Deg3SectorBin1
open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness
open SevenClassQ0Deg3SectorCalculus
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables
open N11Formalization.ActualRingLinkBoundaryData

/-- The exact derivative threshold of every row lies below the degree-14
Taylor value at node 543.  Row 8 is the sharp case. -/
theorem row_threshold_lt_cosT14_nodeQ_543 (i : Fin 9) :
    (2 * mu (nextSite i) : ℚ) / (19 / 50 : ℚ) ^ 2 <
      cosTQ 14 (nodeQ RatInterval.piHi 2048 543) := by
  fin_cases i <;>
    norm_num [mu, nextSite, ringSite, nextRing, cosTQ, nodeQ, RatInterval.piHi,
      Finset.sum_range_succ]

/-- The rational threshold comparison extends to the real cosine bracket on
the prefix through node 543, using antitonality of the degree-14 Taylor
polynomial and discarding the positive remainder. -/
theorem row_threshold_le_cosHiReal_of_prefix (i : Fin 9) {x : ℝ}
    (hx0 : 0 ≤ x)
    (hx1 : x ≤ (nodeQ RatInterval.piHi 2048 (543 : Fin 2049) : ℚ)) :
    2 * ((mu (nextSite i) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 ≤ cosHiReal x := by
  have hq543_pi2 : (nodeQ RatInterval.piHi 2048 543 : ℚ) ≤ Real.pi / 2 := by
    norm_num [nodeQ, RatInterval.piHi]
  have hmono := cosT14_antitoneOn
    (show (nodeQ RatInterval.piHi 2048 543 : ℚ) ∈ Set.Icc 0 (Real.pi / 2) by
      exact ⟨by positivity, hq543_pi2⟩)
    (show x ∈ Set.Icc 0 (Real.pi / 2) by
      exact ⟨hx0, hx1.trans hq543_pi2⟩)
    hx1
  have hrat : (2 * ((mu (nextSite i) : ℚ) : ℝ)) / (19 / 50 : ℝ) ^ 2 <
      (cosTQ 14 (nodeQ RatInterval.piHi 2048 543) : ℝ) := by
    exact_mod_cast row_threshold_lt_cosT14_nodeQ_543 i
  have htail : 0 ≤ x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ) := by positivity
  have hct : cosT 14 x ≤ cosT 14 (nodeQ RatInterval.piHi 2048 543 : ℚ) := by
    exact hmono hx0
  unfold cosHiReal
  linarith

/-- Through node 511 the node table is constant across bins 0 and 1. -/
theorem sectorValue_le_of_bins01 (i : Fin 9) {k l : Fin 2049}
    (hk : k.val ≤ 511) (hl : l.val ≤ 511) :
    sectorValue i k ≤ sectorValue i l := by
  have ha : nodeBin k = nodeBin l := by
    rw [nodeBin_eq_zero_of_le_511 hk, nodeBin_eq_zero_of_le_511 hl]
  apply sectorValue_le_of_cos_ge i k l ha
    (s := (0 : ℝ))
    (t := (nodeQ RatInterval.piHi 2048 (543 : Fin 2049) : ℚ))
  · unfold nodeQ
    positivity
  · exact nodeQ_le_543_of_le_511 hk
  · unfold nodeQ
    positivity
  · exact nodeQ_le_543_of_le_511 hl
  · intro x hx
    exact row_threshold_le_cosHiReal_of_prefix i hx.1 hx.2

/-- Increasing half shared by bins 0 and 1 in every row. -/
theorem sectorAt_bins01_inc (i : Fin 9) (n : ℕ) (hn : n < 511) :
    sectorAt i n ≤ sectorAt i (n + 1) := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_le_of_bins01 i
    (k := (⟨n, by omega⟩ : Fin 2049))
    (l := (⟨n + 1, by omega⟩ : Fin 2049)) (by omega) (by omega)
  simpa [sectorAt, hn0, hn1] using h

/-- Every row's bin 0 is increasing up to its endpoint witness `255`. -/
theorem sectorAt_bin0_unimodal (i : Fin 9) :
    binFirst (0 : Fin 8) ≤ (sectorBinWitness i 0).val ∧
      (sectorBinWitness i 0).val ≤ binLast (0 : Fin 8) ∧
      (∀ n, binFirst (0 : Fin 8) ≤ n → n < (sectorBinWitness i 0).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 0).val ≤ n → n < binLast (0 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  refine ⟨by norm_num [sectorBinWitness, binFirst],
    by norm_num [sectorBinWitness, binLast, binHi], ?_, ?_⟩
  · intro n _ hnw
    apply sectorAt_bins01_inc i n
    norm_num [sectorBinWitness] at hnw
    omega
  · intro _ _ hnlast
    norm_num [binLast, binHi] at hnlast

/-- Every row's bin 1 is increasing up to its endpoint witness `511`. -/
theorem sectorAt_bin1_unimodal (i : Fin 9) :
    binFirst (1 : Fin 8) ≤ (sectorBinWitness i 1).val ∧
      (sectorBinWitness i 1).val ≤ binLast (1 : Fin 8) ∧
      (∀ n, binFirst (1 : Fin 8) ≤ n → n < (sectorBinWitness i 1).val →
        sectorAt i n ≤ sectorAt i (n + 1)) ∧
      (∀ n, (sectorBinWitness i 1).val ≤ n → n < binLast (1 : Fin 8) →
        sectorAt i (n + 1) ≤ sectorAt i n) := by
  refine ⟨by norm_num [sectorBinWitness, binFirst],
    by norm_num [sectorBinWitness, binLast, binHi], ?_, ?_⟩
  · intro n _ hnw
    apply sectorAt_bins01_inc i n
    norm_num [sectorBinWitness] at hnw
    omega
  · intro _ _ hnlast
    norm_num [binLast, binHi] at hnlast

end N11Formalization.SevenClassQ0Deg3SectorBins01AllRows
#check @N11Formalization.SevenClassQ0Deg3SectorBins01AllRows.sectorValue_le_of_bins01
#check @N11Formalization.SevenClassQ0Deg3SectorBins01AllRows.sectorAt_bin0_unimodal
#check @N11Formalization.SevenClassQ0Deg3SectorBins01AllRows.sectorAt_bin1_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBins01AllRows.sectorAt_bin0_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBins01AllRows.sectorAt_bin1_unimodal
