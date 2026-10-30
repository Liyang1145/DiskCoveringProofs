import N11Formalization.SevenClassQ0Deg3SectorBinWitnessBounds

/-! Lane A: the complete shape of the first sector-bin restriction.

The edge-0 cosine prefix already proved in `SevenClassQ0Deg3EdgeShape` is
stronger than the row-0 derivative threshold throughout bin 0.  This closes
all 255 increasing steps in that bin analytically.  The audited witness `255`
is the bin endpoint, so the decreasing half is vacuous.  The remaining 71
row-bin shapes are separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBin0

open MetricAreaRationalCertificate
open SevenClassQ0Deg3EdgeShape
open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness
open SevenClassQ0Deg3SectorCalculus
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables
open N11Formalization.ActualRingLinkBoundaryData

theorem row_zero_threshold_le_edge_zero_rat :
    2 * mu (nextSite 0) ≤ edgeCoeff 0 := by
  norm_num [mu, nextSite, ringSite, nextRing, edgeCoeff, tableEdges, Finset.sum]

theorem row_zero_threshold_le_edge_zero :
    2 * ((mu (nextSite 0) : ℚ) : ℝ) / (19 / 50 : ℝ) ^ 2 ≤
      (edgeCoeff 0 : ℚ) / (19 / 50 : ℝ) ^ 2 := by
  have h : (2 * mu (nextSite 0) : ℚ) ≤ edgeCoeff 0 :=
    row_zero_threshold_le_edge_zero_rat
  have hR : (2 * ((mu (nextSite 0) : ℚ) : ℝ)) ≤ (edgeCoeff 0 : ℚ) := by
    exact_mod_cast h
  exact div_le_div_of_nonneg_right hR (sq_nonneg (19 / 50 : ℝ))

theorem nodeBin_eq_zero_of_le_255 {k : Fin 2049} (hk : k.val ≤ 255) :
    nodeBin k = nodeBinAt 0 := by
  have hdiv : k.val / 256 = 0 := Nat.div_eq_of_lt (by omega)
  simp [nodeBin, binIndex, hdiv, nodeBinAt]

theorem nodeQ_le_543_of_le_255 {k : Fin 2049} (hk : k.val ≤ 255) :
    (nodeQ RatInterval.piHi 2048 k : ℚ) ≤
      (nodeQ RatInterval.piHi 2048 (543 : Fin 2049) : ℚ) := by
  unfold nodeQ
  have hk543 : (k.val : ℚ) ≤ 543 := by
    exact_mod_cast (by omega : k.val ≤ 543)
  have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk543 hp) (by norm_num)

theorem sectorValue_zero_le_of_bin0 {k l : Fin 2049}
    (hk : k.val ≤ 255) (hl : l.val ≤ 255) :
    sectorValue 0 k ≤ sectorValue 0 l := by
  have ha : nodeBin k = nodeBin l := by
    rw [nodeBin_eq_zero_of_le_255 hk, nodeBin_eq_zero_of_le_255 hl]
  apply sectorValue_le_of_cos_ge 0 k l ha
    (s := (0 : ℝ))
    (t := (nodeQ RatInterval.piHi 2048 (543 : Fin 2049) : ℚ))
  · unfold nodeQ
    positivity
  · exact nodeQ_le_543_of_le_255 hk
  · unfold nodeQ
    positivity
  · exact nodeQ_le_543_of_le_255 hl
  · intro x hx
    exact row_zero_threshold_le_edge_zero.trans
      (edge_ratio_le_cosHiReal_of_prefix 0 543
        (by norm_num [nodeQ, RatInterval.piHi])
        edge_ratio_zero_lt_cosT14_nodeQ_543 hx.1 hx.2)

/-- The complete increasing half of row 0, bin 0, through its witness 255. -/
theorem sectorAt_zero_bin0_inc (n : ℕ) (hn : n < 255) :
    sectorAt 0 n ≤ sectorAt 0 (n + 1) := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_zero_le_of_bin0
    (k := (⟨n, by omega⟩ : Fin 2049))
    (l := (⟨n + 1, by omega⟩ : Fin 2049)) (by omega) (by omega)
  simpa [sectorAt, hn0, hn1] using h

/-- The decreasing half at row 0, bin 0 is vacuous: the exact witness `255` is
the last grid point of the bin. -/
theorem sectorAt_zero_bin0_dec (n : ℕ) (hn : n < binLast (0 : Fin 8)) :
    sectorAt 0 (n + 1) ≤ sectorAt 0 n := by
  norm_num [binLast, binHi] at hn

/-- The complete `Fin 8`-bin shape obligation for row 0, bin 0. -/
theorem sectorAt_zero_bin0_unimodal :
    binFirst (0 : Fin 8) ≤ (sectorBinWitness 0 0).val ∧
      (sectorBinWitness 0 0).val ≤ binLast (0 : Fin 8) ∧
      (∀ n, binFirst (0 : Fin 8) ≤ n → n < (sectorBinWitness 0 0).val →
        sectorAt 0 n ≤ sectorAt 0 (n + 1)) ∧
      (∀ n, (sectorBinWitness 0 0).val ≤ n → n < binLast (0 : Fin 8) →
        sectorAt 0 (n + 1) ≤ sectorAt 0 n) := by
  refine ⟨by norm_num [sectorBinWitness, binFirst],
    by norm_num [sectorBinWitness, binLast, binHi], ?_, ?_⟩
  · intro n _ hnw
    exact sectorAt_zero_bin0_inc n (by
      norm_num [sectorBinWitness] at hnw
      omega)
  · intro _ _ hnlast
    exact sectorAt_zero_bin0_dec _ hnlast

end N11Formalization.SevenClassQ0Deg3SectorBin0
#check @N11Formalization.SevenClassQ0Deg3SectorBin0.sectorAt_zero_bin0_inc
#check @N11Formalization.SevenClassQ0Deg3SectorBin0.sectorAt_zero_bin0_dec
#check @N11Formalization.SevenClassQ0Deg3SectorBin0.sectorAt_zero_bin0_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBin0.sectorAt_zero_bin0_inc
#print axioms N11Formalization.SevenClassQ0Deg3SectorBin0.sectorAt_zero_bin0_unimodal
