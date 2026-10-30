import N11Formalization.SevenClassQ0Deg3SectorBin0

/-! Lane A: the complete shape of row 0, bin 1.

The node table has the same value on bins 0 and 1.  The edge-0 cosine prefix
therefore also pays every increasing step from `256` to the bin endpoint `511`.
That endpoint is the audited witness, so the decreasing half is vacuous. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3SectorBin1

open MetricAreaRationalCertificate
open SevenClassQ0Deg3Bins
open SevenClassQ0Deg3EdgeShape
open SevenClassQ0Deg3SectorBin0
open SevenClassQ0Deg3SectorBinShape
open SevenClassQ0Deg3SectorBinWitness
open SevenClassQ0Deg3SectorCalculus
open SevenClassQ0Deg3UpperReductionUnimodal
open SevenClassQ0Deg3UpperTables
open N11Formalization.ActualRingLinkBoundaryData

theorem binIndex_eq_zero_or_one_of_le_511 {k : Fin 2049}
    (hk : k.val ≤ 511) : binIndex k = 0 ∨ binIndex k = 1 := by
  have hqle : k.val / 256 ≤ 1 := by
    have := Nat.div_le_div_right hk (n := 256)
    norm_num at this
    exact this
  have hq : k.val / 256 = 0 ∨ k.val / 256 = 1 := by omega
  rcases hq with hq | hq
  · left
    apply Fin.ext
    simp [binIndex, hq]
  · right
    apply Fin.ext
    simp [binIndex, hq]

theorem nodeBin_eq_zero_of_le_511 {k : Fin 2049} (hk : k.val ≤ 511) :
    nodeBin k = nodeBinAt 0 := by
  rcases binIndex_eq_zero_or_one_of_le_511 hk with h | h
  · simp [nodeBin, h]
  · simp [nodeBin, h, nodeBinAt]

theorem nodeQ_le_543_of_le_511 {k : Fin 2049} (hk : k.val ≤ 511) :
    (nodeQ RatInterval.piHi 2048 k : ℚ) ≤
      (nodeQ RatInterval.piHi 2048 (543 : Fin 2049) : ℚ) := by
  unfold nodeQ
  have hk543 : (k.val : ℚ) ≤ 543 := by
    exact_mod_cast (by omega : k.val ≤ 543)
  have hp : (0 : ℚ) ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk543 hp) (by norm_num)

theorem sectorValue_zero_le_of_bin1 {k l : Fin 2049}
    (hk : k.val ≤ 511) (hl : l.val ≤ 511) :
    sectorValue 0 k ≤ sectorValue 0 l := by
  have ha : nodeBin k = nodeBin l := by
    rw [nodeBin_eq_zero_of_le_511 hk, nodeBin_eq_zero_of_le_511 hl]
  apply sectorValue_le_of_cos_ge 0 k l ha
    (s := (0 : ℝ))
    (t := (nodeQ RatInterval.piHi 2048 (543 : Fin 2049) : ℚ))
  · unfold nodeQ
    positivity
  · exact nodeQ_le_543_of_le_511 hk
  · unfold nodeQ
    positivity
  · exact nodeQ_le_543_of_le_511 hl
  · intro x hx
    exact row_zero_threshold_le_edge_zero.trans
      (edge_ratio_le_cosHiReal_of_prefix 0 543
        (by norm_num [nodeQ, RatInterval.piHi])
        edge_ratio_zero_lt_cosT14_nodeQ_543 hx.1 hx.2)

/-- The complete increasing half of row 0, bin 1, through its witness `511`. -/
theorem sectorAt_zero_bin1_inc (n : ℕ) (hn : n < 511) :
    sectorAt 0 n ≤ sectorAt 0 (n + 1) := by
  have hn0 : min n 2048 = n := min_eq_left (by omega)
  have hn1 : min (n + 1) 2048 = n + 1 := min_eq_left (by omega)
  have h := sectorValue_zero_le_of_bin1
    (k := (⟨n, by omega⟩ : Fin 2049))
    (l := (⟨n + 1, by omega⟩ : Fin 2049)) (by omega) (by omega)
  simpa [sectorAt, hn0, hn1] using h

/-- The decreasing half at row 0, bin 1 is vacuous: witness `511` is the last
grid point of the bin. -/
theorem sectorAt_zero_bin1_dec (n : ℕ) (hn : n < binLast (1 : Fin 8)) :
    sectorAt 0 (n + 1) ≤ sectorAt 0 n := by
  norm_num [binLast, binHi] at hn

/-- The complete `Fin 8`-bin shape obligation for row 0, bin 1. -/
theorem sectorAt_zero_bin1_unimodal :
    binFirst (1 : Fin 8) ≤ (sectorBinWitness 0 1).val ∧
      (sectorBinWitness 0 1).val ≤ binLast (1 : Fin 8) ∧
      (∀ n, binFirst (1 : Fin 8) ≤ n → n < (sectorBinWitness 0 1).val →
        sectorAt 0 n ≤ sectorAt 0 (n + 1)) ∧
      (∀ n, (sectorBinWitness 0 1).val ≤ n → n < binLast (1 : Fin 8) →
        sectorAt 0 (n + 1) ≤ sectorAt 0 n) := by
  refine ⟨by norm_num [sectorBinWitness, binFirst],
    by norm_num [sectorBinWitness, binLast, binHi], ?_, ?_⟩
  · intro n _ hnw
    exact sectorAt_zero_bin1_inc n (by
      norm_num [sectorBinWitness] at hnw
      omega)
  · intro _ _ hnlast
    exact sectorAt_zero_bin1_dec _ hnlast

end N11Formalization.SevenClassQ0Deg3SectorBin1
#check @N11Formalization.SevenClassQ0Deg3SectorBin1.sectorAt_zero_bin1_inc
#check @N11Formalization.SevenClassQ0Deg3SectorBin1.sectorAt_zero_bin1_dec
#check @N11Formalization.SevenClassQ0Deg3SectorBin1.sectorAt_zero_bin1_unimodal
#print axioms N11Formalization.SevenClassQ0Deg3SectorBin1.sectorAt_zero_bin1_inc
#print axioms N11Formalization.SevenClassQ0Deg3SectorBin1.sectorAt_zero_bin1_unimodal
