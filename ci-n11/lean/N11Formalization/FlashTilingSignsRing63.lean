import N11Formalization.FlashTilingSigns
import N11Formalization.FlashTilingCoordBounds

/-!
# FlashTilingSignsRing63 —— 63 条环内定向符号 + 装配 `ringConvex`（生成器输出，勿手改）

`RingConvex (ringCenter u) succ9` 展开为 63 条 `∀ i j, j ≠ i → j ≠ succ9 i → 0 < orient (C i) (C (i+1)) (C j)`。
每条由 `ringCoord` + 36 条十进制端点读数（`FlashTilingCoordBounds`）+ `orient_pos_of_approx`
（`FlashTilingSigns`）得到；末尾 `ringConvex` 用 `fin_cases` + 63 条装配。

数值依据：`R = 1e-4`、`U = 2` ⇒ 阈值 `4R(U+2R)+4UR = 0.00160008`；
中心 determinant 最小 `≈ 0.0540198`（i=1,j=3）⇒ 余量 `≥ 0.0524`。
-/

noncomputable section
set_option maxHeartbeats 8000000

namespace N11Formalization.FlashTilingSigns
open N11Formalization

/-- 环内符号（i=0, j=2）：`0 < orient (C 0) (C 1) (C 2)`。 -/
theorem orient_0_1_2 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 0) (ringCenter u 1) (ringCenter u 2) := by
  have hA := ringCoord u hu 0
  have hB := ringCoord u hu 1
  have hD := ringCoord u hu 2
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.673611 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.694424 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 0) (B := ringCenter u 1) (D := ringCenter u 2)
    (A0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=0, j=3）：`0 < orient (C 0) (C 1) (C 3)`。 -/
theorem orient_0_1_3 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 0) (ringCenter u 1) (ringCenter u 3) := by
  have hA := ringCoord u hu 0
  have hB := ringCoord u hu 1
  have hD := ringCoord u hu 3
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.673611 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.598609 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 0) (B := ringCenter u 1) (D := ringCenter u 3)
    (A0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=0, j=4）：`0 < orient (C 0) (C 1) (C 4)`。 -/
theorem orient_0_1_4 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 0) (ringCenter u 1) (ringCenter u 4) := by
  have hA := ringCoord u hu 0
  have hB := ringCoord u hu 1
  have hD := ringCoord u hu 4
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.673611 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.892522 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 0) (B := ringCenter u 1) (D := ringCenter u 4)
    (A0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (D0 := !₂[(0.892522 : ℝ), (0 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=0, j=5）：`0 < orient (C 0) (C 1) (C 5)`。 -/
theorem orient_0_1_5 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 0) (ringCenter u 1) (ringCenter u 5) := by
  have hA := ringCoord u hu 0
  have hB := ringCoord u hu 1
  have hD := ringCoord u hu 5
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.673611 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.598609 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 0) (B := ringCenter u 1) (D := ringCenter u 5)
    (A0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=0, j=6）：`0 < orient (C 0) (C 1) (C 6)`。 -/
theorem orient_0_1_6 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 0) (ringCenter u 1) (ringCenter u 6) := by
  have hA := ringCoord u hu 0
  have hB := ringCoord u hu 1
  have hD := ringCoord u hu 6
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.673611 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.694424 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 0) (B := ringCenter u 1) (D := ringCenter u 6)
    (A0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=0, j=7）：`0 < orient (C 0) (C 1) (C 7)`。 -/
theorem orient_0_1_7 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 0) (ringCenter u 1) (ringCenter u 7) := by
  have hA := ringCoord u hu 0
  have hB := ringCoord u hu 1
  have hD := ringCoord u hu 7
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.673611 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.673611 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 0) (B := ringCenter u 1) (D := ringCenter u 7)
    (A0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=0, j=8）：`0 < orient (C 0) (C 1) (C 8)`。 -/
theorem orient_0_1_8 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 0) (ringCenter u 1) (ringCenter u 8) := by
  have hA := ringCoord u hu 0
  have hB := ringCoord u hu 1
  have hD := ringCoord u hu 8
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.673611 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.298369 : ℝ) - (-0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 0) (B := ringCenter u 1) (D := ringCenter u 8)
    (A0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=1, j=0）：`0 < orient (C 1) (C 2) (C 0)`。 -/
theorem orient_1_2_0 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 1) (ringCenter u 2) (ringCenter u 0) := by
  have hA := ringCoord u hu 1
  have hB := ringCoord u hu 2
  have hD := ringCoord u hu 0
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.694424 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.298369 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 1) (B := ringCenter u 2) (D := ringCenter u 0)
    (A0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=1, j=3）：`0 < orient (C 1) (C 2) (C 3)`。 -/
theorem orient_1_2_3 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 1) (ringCenter u 2) (ringCenter u 3) := by
  have hA := ringCoord u hu 1
  have hB := ringCoord u hu 2
  have hD := ringCoord u hu 3
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.694424 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.598609 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 1) (B := ringCenter u 2) (D := ringCenter u 3)
    (A0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=1, j=4）：`0 < orient (C 1) (C 2) (C 4)`。 -/
theorem orient_1_2_4 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 1) (ringCenter u 2) (ringCenter u 4) := by
  have hA := ringCoord u hu 1
  have hB := ringCoord u hu 2
  have hD := ringCoord u hu 4
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.694424 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.892522 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 1) (B := ringCenter u 2) (D := ringCenter u 4)
    (A0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (D0 := !₂[(0.892522 : ℝ), (0 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=1, j=5）：`0 < orient (C 1) (C 2) (C 5)`。 -/
theorem orient_1_2_5 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 1) (ringCenter u 2) (ringCenter u 5) := by
  have hA := ringCoord u hu 1
  have hB := ringCoord u hu 2
  have hD := ringCoord u hu 5
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.694424 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.598609 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 1) (B := ringCenter u 2) (D := ringCenter u 5)
    (A0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=1, j=6）：`0 < orient (C 1) (C 2) (C 6)`。 -/
theorem orient_1_2_6 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 1) (ringCenter u 2) (ringCenter u 6) := by
  have hA := ringCoord u hu 1
  have hB := ringCoord u hu 2
  have hD := ringCoord u hu 6
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.694424 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.694424 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 1) (B := ringCenter u 2) (D := ringCenter u 6)
    (A0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=1, j=7）：`0 < orient (C 1) (C 2) (C 7)`。 -/
theorem orient_1_2_7 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 1) (ringCenter u 2) (ringCenter u 7) := by
  have hA := ringCoord u hu 1
  have hB := ringCoord u hu 2
  have hD := ringCoord u hu 7
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.694424 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.673611 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 1) (B := ringCenter u 2) (D := ringCenter u 7)
    (A0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=1, j=8）：`0 < orient (C 1) (C 2) (C 8)`。 -/
theorem orient_1_2_8 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 1) (ringCenter u 2) (ringCenter u 8) := by
  have hA := ringCoord u hu 1
  have hB := ringCoord u hu 2
  have hD := ringCoord u hu 8
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.694424 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.298369 : ℝ) - (-0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 1) (B := ringCenter u 2) (D := ringCenter u 8)
    (A0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=2, j=0）：`0 < orient (C 2) (C 3) (C 0)`。 -/
theorem orient_2_3_0 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 3) (ringCenter u 0) := by
  have hA := ringCoord u hu 2
  have hB := ringCoord u hu 3
  have hD := ringCoord u hu 0
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.598609 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.298369 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 3) (D := ringCenter u 0)
    (A0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=2, j=1）：`0 < orient (C 2) (C 3) (C 1)`。 -/
theorem orient_2_3_1 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 3) (ringCenter u 1) := by
  have hA := ringCoord u hu 2
  have hB := ringCoord u hu 3
  have hD := ringCoord u hu 1
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.598609 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.673611 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 3) (D := ringCenter u 1)
    (A0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=2, j=4）：`0 < orient (C 2) (C 3) (C 4)`。 -/
theorem orient_2_3_4 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 3) (ringCenter u 4) := by
  have hA := ringCoord u hu 2
  have hB := ringCoord u hu 3
  have hD := ringCoord u hu 4
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.598609 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.892522 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 3) (D := ringCenter u 4)
    (A0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (D0 := !₂[(0.892522 : ℝ), (0 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=2, j=5）：`0 < orient (C 2) (C 3) (C 5)`。 -/
theorem orient_2_3_5 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 3) (ringCenter u 5) := by
  have hA := ringCoord u hu 2
  have hB := ringCoord u hu 3
  have hD := ringCoord u hu 5
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.598609 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.598609 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 3) (D := ringCenter u 5)
    (A0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=2, j=6）：`0 < orient (C 2) (C 3) (C 6)`。 -/
theorem orient_2_3_6 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 3) (ringCenter u 6) := by
  have hA := ringCoord u hu 2
  have hB := ringCoord u hu 3
  have hD := ringCoord u hu 6
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.598609 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.694424 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 3) (D := ringCenter u 6)
    (A0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=2, j=7）：`0 < orient (C 2) (C 3) (C 7)`。 -/
theorem orient_2_3_7 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 3) (ringCenter u 7) := by
  have hA := ringCoord u hu 2
  have hB := ringCoord u hu 3
  have hD := ringCoord u hu 7
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.598609 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.673611 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 3) (D := ringCenter u 7)
    (A0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=2, j=8）：`0 < orient (C 2) (C 3) (C 8)`。 -/
theorem orient_2_3_8 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 3) (ringCenter u 8) := by
  have hA := ringCoord u hu 2
  have hB := ringCoord u hu 3
  have hD := ringCoord u hu 8
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.598609 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.298369 : ℝ) - (-0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 2) (B := ringCenter u 3) (D := ringCenter u 8)
    (A0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=3, j=0）：`0 < orient (C 3) (C 4) (C 0)`。 -/
theorem orient_3_4_0 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 3) (ringCenter u 4) (ringCenter u 0) := by
  have hA := ringCoord u hu 3
  have hB := ringCoord u hu 4
  have hD := ringCoord u hu 0
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.892522 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.298369 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 3) (B := ringCenter u 4) (D := ringCenter u 0)
    (A0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (B0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=3, j=1）：`0 < orient (C 3) (C 4) (C 1)`。 -/
theorem orient_3_4_1 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 3) (ringCenter u 4) (ringCenter u 1) := by
  have hA := ringCoord u hu 3
  have hB := ringCoord u hu 4
  have hD := ringCoord u hu 1
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.892522 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.673611 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 3) (B := ringCenter u 4) (D := ringCenter u 1)
    (A0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (B0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=3, j=2）：`0 < orient (C 3) (C 4) (C 2)`。 -/
theorem orient_3_4_2 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 3) (ringCenter u 4) (ringCenter u 2) := by
  have hA := ringCoord u hu 3
  have hB := ringCoord u hu 4
  have hD := ringCoord u hu 2
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.892522 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.694424 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 3) (B := ringCenter u 4) (D := ringCenter u 2)
    (A0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (B0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=3, j=5）：`0 < orient (C 3) (C 4) (C 5)`。 -/
theorem orient_3_4_5 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 3) (ringCenter u 4) (ringCenter u 5) := by
  have hA := ringCoord u hu 3
  have hB := ringCoord u hu 4
  have hD := ringCoord u hu 5
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.892522 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.598609 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 3) (B := ringCenter u 4) (D := ringCenter u 5)
    (A0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (B0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=3, j=6）：`0 < orient (C 3) (C 4) (C 6)`。 -/
theorem orient_3_4_6 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 3) (ringCenter u 4) (ringCenter u 6) := by
  have hA := ringCoord u hu 3
  have hB := ringCoord u hu 4
  have hD := ringCoord u hu 6
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.892522 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.694424 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 3) (B := ringCenter u 4) (D := ringCenter u 6)
    (A0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (B0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=3, j=7）：`0 < orient (C 3) (C 4) (C 7)`。 -/
theorem orient_3_4_7 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 3) (ringCenter u 4) (ringCenter u 7) := by
  have hA := ringCoord u hu 3
  have hB := ringCoord u hu 4
  have hD := ringCoord u hu 7
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.892522 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.673611 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 3) (B := ringCenter u 4) (D := ringCenter u 7)
    (A0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (B0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=3, j=8）：`0 < orient (C 3) (C 4) (C 8)`。 -/
theorem orient_3_4_8 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 3) (ringCenter u 4) (ringCenter u 8) := by
  have hA := ringCoord u hu 3
  have hB := ringCoord u hu 4
  have hD := ringCoord u hu 8
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.892522 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.298369 : ℝ) - (-0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 3) (B := ringCenter u 4) (D := ringCenter u 8)
    (A0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) (B0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=4, j=0）：`0 < orient (C 4) (C 5) (C 0)`。 -/
theorem orient_4_5_0 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 4) (ringCenter u 5) (ringCenter u 0) := by
  have hA := ringCoord u hu 4
  have hB := ringCoord u hu 5
  have hD := ringCoord u hu 0
  have axa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.598609 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.298369 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 4) (B := ringCenter u 5) (D := ringCenter u 0)
    (A0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=4, j=1）：`0 < orient (C 4) (C 5) (C 1)`。 -/
theorem orient_4_5_1 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 4) (ringCenter u 5) (ringCenter u 1) := by
  have hA := ringCoord u hu 4
  have hB := ringCoord u hu 5
  have hD := ringCoord u hu 1
  have axa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.598609 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.673611 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 4) (B := ringCenter u 5) (D := ringCenter u 1)
    (A0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=4, j=2）：`0 < orient (C 4) (C 5) (C 2)`。 -/
theorem orient_4_5_2 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 4) (ringCenter u 5) (ringCenter u 2) := by
  have hA := ringCoord u hu 4
  have hB := ringCoord u hu 5
  have hD := ringCoord u hu 2
  have axa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.598609 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.694424 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 4) (B := ringCenter u 5) (D := ringCenter u 2)
    (A0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=4, j=3）：`0 < orient (C 4) (C 5) (C 3)`。 -/
theorem orient_4_5_3 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 4) (ringCenter u 5) (ringCenter u 3) := by
  have hA := ringCoord u hu 4
  have hB := ringCoord u hu 5
  have hD := ringCoord u hu 3
  have axa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.598609 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.598609 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 4) (B := ringCenter u 5) (D := ringCenter u 3)
    (A0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=4, j=6）：`0 < orient (C 4) (C 5) (C 6)`。 -/
theorem orient_4_5_6 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 4) (ringCenter u 5) (ringCenter u 6) := by
  have hA := ringCoord u hu 4
  have hB := ringCoord u hu 5
  have hD := ringCoord u hu 6
  have axa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.598609 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.694424 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 4) (B := ringCenter u 5) (D := ringCenter u 6)
    (A0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=4, j=7）：`0 < orient (C 4) (C 5) (C 7)`。 -/
theorem orient_4_5_7 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 4) (ringCenter u 5) (ringCenter u 7) := by
  have hA := ringCoord u hu 4
  have hB := ringCoord u hu 5
  have hD := ringCoord u hu 7
  have axa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.598609 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.673611 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 4) (B := ringCenter u 5) (D := ringCenter u 7)
    (A0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=4, j=8）：`0 < orient (C 4) (C 5) (C 8)`。 -/
theorem orient_4_5_8 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 4) (ringCenter u 5) (ringCenter u 8) := by
  have hA := ringCoord u hu 4
  have hB := ringCoord u hu 5
  have hD := ringCoord u hu 8
  have axa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.615812 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.598609 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (0.892522 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.298369 : ℝ) - (0 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.892522 : ℝ), (0 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 4) (B := ringCenter u 5) (D := ringCenter u 8)
    (A0 := !₂[(0.892522 : ℝ), (0 : ℝ)]) (B0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=5, j=0）：`0 < orient (C 5) (C 6) (C 0)`。 -/
theorem orient_5_6_0 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 5) (ringCenter u 6) (ringCenter u 0) := by
  have hA := ringCoord u hu 5
  have hB := ringCoord u hu 6
  have hD := ringCoord u hu 0
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.694424 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.298369 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 5) (B := ringCenter u 6) (D := ringCenter u 0)
    (A0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=5, j=1）：`0 < orient (C 5) (C 6) (C 1)`。 -/
theorem orient_5_6_1 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 5) (ringCenter u 6) (ringCenter u 1) := by
  have hA := ringCoord u hu 5
  have hB := ringCoord u hu 6
  have hD := ringCoord u hu 1
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.694424 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.673611 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 5) (B := ringCenter u 6) (D := ringCenter u 1)
    (A0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=5, j=2）：`0 < orient (C 5) (C 6) (C 2)`。 -/
theorem orient_5_6_2 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 5) (ringCenter u 6) (ringCenter u 2) := by
  have hA := ringCoord u hu 5
  have hB := ringCoord u hu 6
  have hD := ringCoord u hu 2
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.694424 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.694424 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 5) (B := ringCenter u 6) (D := ringCenter u 2)
    (A0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=5, j=3）：`0 < orient (C 5) (C 6) (C 3)`。 -/
theorem orient_5_6_3 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 5) (ringCenter u 6) (ringCenter u 3) := by
  have hA := ringCoord u hu 5
  have hB := ringCoord u hu 6
  have hD := ringCoord u hu 3
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.694424 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.598609 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 5) (B := ringCenter u 6) (D := ringCenter u 3)
    (A0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=5, j=4）：`0 < orient (C 5) (C 6) (C 4)`。 -/
theorem orient_5_6_4 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 5) (ringCenter u 6) (ringCenter u 4) := by
  have hA := ringCoord u hu 5
  have hB := ringCoord u hu 6
  have hD := ringCoord u hu 4
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.694424 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.892522 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 5) (B := ringCenter u 6) (D := ringCenter u 4)
    (A0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (D0 := !₂[(0.892522 : ℝ), (0 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=5, j=7）：`0 < orient (C 5) (C 6) (C 7)`。 -/
theorem orient_5_6_7 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 5) (ringCenter u 6) (ringCenter u 7) := by
  have hA := ringCoord u hu 5
  have hB := ringCoord u hu 6
  have hD := ringCoord u hu 7
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.694424 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.673611 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 5) (B := ringCenter u 6) (D := ringCenter u 7)
    (A0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=5, j=8）：`0 < orient (C 5) (C 6) (C 8)`。 -/
theorem orient_5_6_8 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 5) (ringCenter u 6) (ringCenter u 8) := by
  have hA := ringCoord u hu 5
  have hB := ringCoord u hu 6
  have hD := ringCoord u hu 8
  have axa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(0.094837 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.694424 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (0.615812 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.298369 : ℝ) - (0.598609 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 5) (B := ringCenter u 6) (D := ringCenter u 8)
    (A0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)]) (B0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=6, j=0）：`0 < orient (C 6) (C 7) (C 0)`。 -/
theorem orient_6_7_0 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 7) (ringCenter u 0) := by
  have hA := ringCoord u hu 6
  have hB := ringCoord u hu 7
  have hD := ringCoord u hu 0
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.673611 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.298369 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u 7) (D := ringCenter u 0)
    (A0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=6, j=1）：`0 < orient (C 6) (C 7) (C 1)`。 -/
theorem orient_6_7_1 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 7) (ringCenter u 1) := by
  have hA := ringCoord u hu 6
  have hB := ringCoord u hu 7
  have hD := ringCoord u hu 1
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.673611 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.673611 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u 7) (D := ringCenter u 1)
    (A0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=6, j=2）：`0 < orient (C 6) (C 7) (C 2)`。 -/
theorem orient_6_7_2 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 7) (ringCenter u 2) := by
  have hA := ringCoord u hu 6
  have hB := ringCoord u hu 7
  have hD := ringCoord u hu 2
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.673611 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.694424 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u 7) (D := ringCenter u 2)
    (A0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=6, j=3）：`0 < orient (C 6) (C 7) (C 3)`。 -/
theorem orient_6_7_3 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 7) (ringCenter u 3) := by
  have hA := ringCoord u hu 6
  have hB := ringCoord u hu 7
  have hD := ringCoord u hu 3
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.673611 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.598609 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u 7) (D := ringCenter u 3)
    (A0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=6, j=4）：`0 < orient (C 6) (C 7) (C 4)`。 -/
theorem orient_6_7_4 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 7) (ringCenter u 4) := by
  have hA := ringCoord u hu 6
  have hB := ringCoord u hu 7
  have hD := ringCoord u hu 4
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.673611 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.892522 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u 7) (D := ringCenter u 4)
    (A0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (D0 := !₂[(0.892522 : ℝ), (0 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=6, j=5）：`0 < orient (C 6) (C 7) (C 5)`。 -/
theorem orient_6_7_5 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 7) (ringCenter u 5) := by
  have hA := ringCoord u hu 6
  have hB := ringCoord u hu 7
  have hD := ringCoord u hu 5
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.673611 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.598609 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u 7) (D := ringCenter u 5)
    (A0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=6, j=8）：`0 < orient (C 6) (C 7) (C 8)`。 -/
theorem orient_6_7_8 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 7) (ringCenter u 8) := by
  have hA := ringCoord u hu 6
  have hB := ringCoord u hu 7
  have hD := ringCoord u hu 8
  have axa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.355787 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.673611 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (0.094837 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.298369 : ℝ) - (0.694424 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 6) (B := ringCenter u 7) (D := ringCenter u 8)
    (A0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)]) (B0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=7, j=0）：`0 < orient (C 7) (C 8) (C 0)`。 -/
theorem orient_7_8_0 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 7) (ringCenter u 8) (ringCenter u 0) := by
  have hA := ringCoord u hu 7
  have hB := ringCoord u hu 8
  have hD := ringCoord u hu 0
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.298369 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.764706 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.298369 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 7) (B := ringCenter u 8) (D := ringCenter u 0)
    (A0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (D0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=7, j=1）：`0 < orient (C 7) (C 8) (C 1)`。 -/
theorem orient_7_8_1 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 7) (ringCenter u 8) (ringCenter u 1) := by
  have hA := ringCoord u hu 7
  have hB := ringCoord u hu 8
  have hD := ringCoord u hu 1
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.298369 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.673611 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 7) (B := ringCenter u 8) (D := ringCenter u 1)
    (A0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=7, j=2）：`0 < orient (C 7) (C 8) (C 2)`。 -/
theorem orient_7_8_2 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 7) (ringCenter u 8) (ringCenter u 2) := by
  have hA := ringCoord u hu 7
  have hB := ringCoord u hu 8
  have hD := ringCoord u hu 2
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.298369 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.694424 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 7) (B := ringCenter u 8) (D := ringCenter u 2)
    (A0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=7, j=3）：`0 < orient (C 7) (C 8) (C 3)`。 -/
theorem orient_7_8_3 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 7) (ringCenter u 8) (ringCenter u 3) := by
  have hA := ringCoord u hu 7
  have hB := ringCoord u hu 8
  have hD := ringCoord u hu 3
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.298369 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.598609 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 7) (B := ringCenter u 8) (D := ringCenter u 3)
    (A0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=7, j=4）：`0 < orient (C 7) (C 8) (C 4)`。 -/
theorem orient_7_8_4 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 7) (ringCenter u 8) (ringCenter u 4) := by
  have hA := ringCoord u hu 7
  have hB := ringCoord u hu 8
  have hD := ringCoord u hu 4
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.298369 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.892522 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 7) (B := ringCenter u 8) (D := ringCenter u 4)
    (A0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (D0 := !₂[(0.892522 : ℝ), (0 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=7, j=5）：`0 < orient (C 7) (C 8) (C 5)`。 -/
theorem orient_7_8_5 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 7) (ringCenter u 8) (ringCenter u 5) := by
  have hA := ringCoord u hu 7
  have hB := ringCoord u hu 8
  have hD := ringCoord u hu 5
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.298369 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.598609 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 7) (B := ringCenter u 8) (D := ringCenter u 5)
    (A0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=7, j=6）：`0 < orient (C 7) (C 8) (C 6)`。 -/
theorem orient_7_8_6 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 7) (ringCenter u 8) (ringCenter u 6) := by
  have hA := ringCoord u hu 7
  have hB := ringCoord u hu 8
  have hD := ringCoord u hu 6
  have axa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(0.298369 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (-0.355787 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.694424 : ℝ) - (0.673611 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 7) (B := ringCenter u 8) (D := ringCenter u 6)
    (A0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=8, j=1）：`0 < orient (C 8) (C 0) (C 1)`。 -/
theorem orient_8_0_1 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 8) (ringCenter u 0) (ringCenter u 1) := by
  have hA := ringCoord u hu 8
  have hB := ringCoord u hu 0
  have hD := ringCoord u hu 1
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 1).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd1x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 1).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd1x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.673612 : ℝ) ≤ (ringCenter u 1).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd1y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 1).ofLp 1 ≤ (-0.673611 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd1y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 1).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 1).ofLp 1 - (-0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.298369 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.673611 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(-0.355787 : ℝ), (-0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 8) (B := ringCenter u 0) (D := ringCenter u 1)
    (A0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (-0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=8, j=2）：`0 < orient (C 8) (C 0) (C 2)`。 -/
theorem orient_8_0_2 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 8) (ringCenter u 0) (ringCenter u 2) := by
  have hA := ringCoord u hu 8
  have hB := ringCoord u hu 0
  have hD := ringCoord u hu 2
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 2).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd2x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 2).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd2x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.694425 : ℝ) ≤ (ringCenter u 2).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd2y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 2).ofLp 1 ≤ (-0.694424 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd2y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 2).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 2).ofLp 1 - (-0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.298369 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.694424 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(0.094837 : ℝ), (-0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 8) (B := ringCenter u 0) (D := ringCenter u 2)
    (A0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (-0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=8, j=3）：`0 < orient (C 8) (C 0) (C 3)`。 -/
theorem orient_8_0_3 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 8) (ringCenter u 0) (ringCenter u 3) := by
  have hA := ringCoord u hu 8
  have hB := ringCoord u hu 0
  have hD := ringCoord u hu 3
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 3).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd3x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 3).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd3x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (-0.598609 : ℝ) ≤ (ringCenter u 3).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd3y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 3).ofLp 1 ≤ (-0.598608 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd3y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 3).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 3).ofLp 1 - (-0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.298369 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(-0.598609 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(0.615812 : ℝ), (-0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 8) (B := ringCenter u 0) (D := ringCenter u 3)
    (A0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (-0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=8, j=4）：`0 < orient (C 8) (C 0) (C 4)`。 -/
theorem orient_8_0_4 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 8) (ringCenter u 0) (ringCenter u 4) := by
  have hA := ringCoord u hu 8
  have hB := ringCoord u hu 0
  have hD := ringCoord u hu 4
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.892521 : ℝ) ≤ (ringCenter u 4).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd4x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 4).ofLp 0 ≤ (0.892522 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd4x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0 : ℝ) ≤ (ringCenter u 4).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd4y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 4).ofLp 1 ≤ (0 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd4y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 4).ofLp 0 - (0.892522 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 4).ofLp 1 - (0 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.298369 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.892522 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(0.892522 : ℝ), (0 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 8) (B := ringCenter u 0) (D := ringCenter u 4)
    (A0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (D0 := !₂[(0.892522 : ℝ), (0 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=8, j=5）：`0 < orient (C 8) (C 0) (C 5)`。 -/
theorem orient_8_0_5 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 8) (ringCenter u 0) (ringCenter u 5) := by
  have hA := ringCoord u hu 8
  have hB := ringCoord u hu 0
  have hD := ringCoord u hu 5
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.615811 : ℝ) ≤ (ringCenter u 5).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd5x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 5).ofLp 0 ≤ (0.615812 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd5x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.598608 : ℝ) ≤ (ringCenter u 5).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd5y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 5).ofLp 1 ≤ (0.598609 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd5y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 5).ofLp 0 - (0.615812 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 5).ofLp 1 - (0.598609 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.298369 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.615812 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.598609 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(0.615812 : ℝ), (0.598609 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 8) (B := ringCenter u 0) (D := ringCenter u 5)
    (A0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (D0 := !₂[(0.615812 : ℝ), (0.598609 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=8, j=6）：`0 < orient (C 8) (C 0) (C 6)`。 -/
theorem orient_8_0_6 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 8) (ringCenter u 0) (ringCenter u 6) := by
  have hA := ringCoord u hu 8
  have hB := ringCoord u hu 0
  have hD := ringCoord u hu 6
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (0.094836 : ℝ) ≤ (ringCenter u 6).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd6x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 6).ofLp 0 ≤ (0.094837 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd6x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.694424 : ℝ) ≤ (ringCenter u 6).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd6y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 6).ofLp 1 ≤ (0.694425 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd6y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 6).ofLp 0 - (0.094837 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 6).ofLp 1 - (0.694424 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.298369 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(0.094837 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.694424 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(0.094837 : ℝ), (0.694424 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 8) (B := ringCenter u 0) (D := ringCenter u 6)
    (A0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (D0 := !₂[(0.094837 : ℝ), (0.694424 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

/-- 环内符号（i=8, j=7）：`0 < orient (C 8) (C 0) (C 7)`。 -/
theorem orient_8_0_7 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u) :
    0 < FlashTiling.orient (ringCenter u 8) (ringCenter u 0) (ringCenter u 7) := by
  have hA := ringCoord u hu 8
  have hB := ringCoord u hu 0
  have hD := ringCoord u hu 7
  have axa : (-0.764707 : ℝ) ≤ (ringCenter u 8).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd8x_lo) hA.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have axb : (ringCenter u 8).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hA.2.1 (Rat.cast_le.mpr rd8x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have aya : (0.298369 : ℝ) ≤ (ringCenter u 8).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd8y_lo) hA.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have ayb : (ringCenter u 8).ofLp 1 ≤ (0.298370 : ℝ) := by
    have h := le_trans hA.2.2.2 (Rat.cast_le.mpr rd8y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxa : (-0.764707 : ℝ) ≤ (ringCenter u 0).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd0x_lo) hB.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bxb : (ringCenter u 0).ofLp 0 ≤ (-0.764706 : ℝ) := by
    have h := le_trans hB.2.1 (Rat.cast_le.mpr rd0x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have bya : (-0.298370 : ℝ) ≤ (ringCenter u 0).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd0y_lo) hB.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have byb : (ringCenter u 0).ofLp 1 ≤ (-0.298369 : ℝ) := by
    have h := le_trans hB.2.2.2 (Rat.cast_le.mpr rd0y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxa : (-0.355788 : ℝ) ≤ (ringCenter u 7).ofLp 0 := by
    have h := le_trans (Rat.cast_le.mpr rd7x_lo) hD.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dxb : (ringCenter u 7).ofLp 0 ≤ (-0.355787 : ℝ) := by
    have h := le_trans hD.2.1 (Rat.cast_le.mpr rd7x_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dya : (0.673611 : ℝ) ≤ (ringCenter u 7).ofLp 1 := by
    have h := le_trans (Rat.cast_le.mpr rd7y_lo) hD.2.2.1
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have dyb : (ringCenter u 7).ofLp 1 ≤ (0.673612 : ℝ) := by
    have h := le_trans hD.2.2.2 (Rat.cast_le.mpr rd7y_hi)
    norm_num only [Rat.cast_neg, Rat.cast_ofScientific] at h ⊢
    exact h
  have k1a : |(ringCenter u 8).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [axa, axb]
  have k1b : |(ringCenter u 8).ofLp 1 - (0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [aya, ayb]
  have k3a : |(ringCenter u 0).ofLp 0 - (-0.764706 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bxa, bxb]
  have k3b : |(ringCenter u 0).ofLp 1 - (-0.298369 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [bya, byb]
  have k5a : |(ringCenter u 7).ofLp 0 - (-0.355787 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dxa, dxb]
  have k5b : |(ringCenter u 7).ofLp 1 - (0.673611 : ℝ)| ≤ 1 / 10000 := by
    rw [abs_sub_le_iff]; constructor <;> linarith [dya, dyb]
  have uab : |(-0.764706 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uab2 : |(-0.298369 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have uad : |(-0.355787 : ℝ) - (-0.764706 : ℝ)| ≤ 2 := by norm_num
  have uad2 : |(0.673611 : ℝ) - (0.298369 : ℝ)| ≤ 2 := by norm_num
  have hM : 4 * (1 / 10000 : ℝ) * (2 + 2 * (1 / 10000)) + 4 * 2 * (1 / 10000)
      < FlashTiling.orient (!₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (!₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (!₂[(-0.355787 : ℝ), (0.673611 : ℝ)]) := by
    rw [orient_eq]; norm_num
  exact orient_pos_of_approx (A := ringCenter u 8) (B := ringCenter u 0) (D := ringCenter u 7)
    (A0 := !₂[(-0.764706 : ℝ), (0.298369 : ℝ)]) (B0 := !₂[(-0.764706 : ℝ), (-0.298369 : ℝ)]) (D0 := !₂[(-0.355787 : ℝ), (0.673611 : ℝ)])
    (R := 1 / 10000) (U := 2) k1a k1b k3a k3b k5a k5b uab uab2 uad uad2
    (by norm_num) (by norm_num) hM

end N11Formalization.FlashTilingSigns
