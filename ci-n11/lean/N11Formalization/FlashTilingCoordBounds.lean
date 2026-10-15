import N11Formalization.NondegProof
import N11Formalization.RootRangeBoxFull

/-!
# FlashTilingCoordBounds —— 共享坐标盒读数（出口 + 36 条十进制端点）

**约定（与 lead 已绿的单例一致）**：所有比较值用**十进制 ℚ 字面量** `((-0.764707 : ℚ))`；
下游搬 ℝ 时 `Rat.cast_le.mpr` + `norm_num only [Rat.cast_neg, Rat.cast_ofScientific]` 即可化为 ℝ 数值。

出口 `ringCoord`：`(ringCenter u k).ofLp 0/1` 落在 `ndRingBox ndBox k 0/1` 的 ℝ 端点之间
（由已证包含性 `ndRingBox_mem` 直接给出）。
下游：本组 63 条环内 + caps 的 25 条 hub/弦，统一消费本件，不各自重算 `nd_eval`。
-/

noncomputable section

set_option maxHeartbeats 8000000

namespace N11Formalization.FlashTilingSigns

open N11Formalization

/-- **坐标盒出口**。 -/
theorem ringCoord (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) (k : Fin 9) :
    ((ndRingBox ndBox k 0).lo : ℝ) ≤ (ringCenter u k).ofLp 0 ∧
      (ringCenter u k).ofLp 0 ≤ ((ndRingBox ndBox k 0).hi : ℝ) ∧
    ((ndRingBox ndBox k 1).lo : ℝ) ≤ (ringCenter u k).ofLp 1 ∧
      (ringCenter u k).ofLp 1 ≤ ((ndRingBox ndBox k 1).hi : ℝ) :=
  ⟨RatInterval.mem_lo_le (ndRingBox_mem (RootRangeBoxFull.hQ u hu) k 0),
   RatInterval.mem_le_hi (ndRingBox_mem (RootRangeBoxFull.hQ u hu) k 0),
   RatInterval.mem_lo_le (ndRingBox_mem (RootRangeBoxFull.hQ u hu) k 1),
   RatInterval.mem_le_hi (ndRingBox_mem (RootRangeBoxFull.hQ u hu) k 1)⟩

/-! ## 36 条十进制端点（外向舍入到 6 位；真实端点见 `evidence/flash-slack` 的打印） -/

theorem rd0x_lo : ((-0.764707 : ℚ)) ≤ (ndRingBox ndBox 0 0).lo := by nd_eval
theorem rd0x_hi : (ndRingBox ndBox 0 0).hi ≤ ((-0.764706 : ℚ)) := by nd_eval
theorem rd0y_lo : ((-0.298370 : ℚ)) ≤ (ndRingBox ndBox 0 1).lo := by nd_eval
theorem rd0y_hi : (ndRingBox ndBox 0 1).hi ≤ ((-0.298369 : ℚ)) := by nd_eval
theorem rd1x_lo : ((-0.355788 : ℚ)) ≤ (ndRingBox ndBox 1 0).lo := by nd_eval
theorem rd1x_hi : (ndRingBox ndBox 1 0).hi ≤ ((-0.355787 : ℚ)) := by nd_eval
theorem rd1y_lo : ((-0.673612 : ℚ)) ≤ (ndRingBox ndBox 1 1).lo := by nd_eval
theorem rd1y_hi : (ndRingBox ndBox 1 1).hi ≤ ((-0.673611 : ℚ)) := by nd_eval
theorem rd2x_lo : ((0.094836 : ℚ)) ≤ (ndRingBox ndBox 2 0).lo := by nd_eval
theorem rd2x_hi : (ndRingBox ndBox 2 0).hi ≤ ((0.094837 : ℚ)) := by nd_eval
theorem rd2y_lo : ((-0.694425 : ℚ)) ≤ (ndRingBox ndBox 2 1).lo := by nd_eval
theorem rd2y_hi : (ndRingBox ndBox 2 1).hi ≤ ((-0.694424 : ℚ)) := by nd_eval
theorem rd3x_lo : ((0.615811 : ℚ)) ≤ (ndRingBox ndBox 3 0).lo := by nd_eval
theorem rd3x_hi : (ndRingBox ndBox 3 0).hi ≤ ((0.615812 : ℚ)) := by nd_eval
theorem rd3y_lo : ((-0.598609 : ℚ)) ≤ (ndRingBox ndBox 3 1).lo := by nd_eval
theorem rd3y_hi : (ndRingBox ndBox 3 1).hi ≤ ((-0.598608 : ℚ)) := by nd_eval
theorem rd4x_lo : ((0.892521 : ℚ)) ≤ (ndRingBox ndBox 4 0).lo := by nd_eval
theorem rd4x_hi : (ndRingBox ndBox 4 0).hi ≤ ((0.892522 : ℚ)) := by nd_eval
theorem rd4y_lo : ((0.0 : ℚ)) ≤ (ndRingBox ndBox 4 1).lo := by nd_eval
theorem rd4y_hi : (ndRingBox ndBox 4 1).hi ≤ ((0.0 : ℚ)) := by nd_eval
theorem rd5x_lo : ((0.615811 : ℚ)) ≤ (ndRingBox ndBox 5 0).lo := by nd_eval
theorem rd5x_hi : (ndRingBox ndBox 5 0).hi ≤ ((0.615812 : ℚ)) := by nd_eval
theorem rd5y_lo : ((0.598608 : ℚ)) ≤ (ndRingBox ndBox 5 1).lo := by nd_eval
theorem rd5y_hi : (ndRingBox ndBox 5 1).hi ≤ ((0.598609 : ℚ)) := by nd_eval
theorem rd6x_lo : ((0.094836 : ℚ)) ≤ (ndRingBox ndBox 6 0).lo := by nd_eval
theorem rd6x_hi : (ndRingBox ndBox 6 0).hi ≤ ((0.094837 : ℚ)) := by nd_eval
theorem rd6y_lo : ((0.694424 : ℚ)) ≤ (ndRingBox ndBox 6 1).lo := by nd_eval
theorem rd6y_hi : (ndRingBox ndBox 6 1).hi ≤ ((0.694425 : ℚ)) := by nd_eval
theorem rd7x_lo : ((-0.355788 : ℚ)) ≤ (ndRingBox ndBox 7 0).lo := by nd_eval
theorem rd7x_hi : (ndRingBox ndBox 7 0).hi ≤ ((-0.355787 : ℚ)) := by nd_eval
theorem rd7y_lo : ((0.673611 : ℚ)) ≤ (ndRingBox ndBox 7 1).lo := by nd_eval
theorem rd7y_hi : (ndRingBox ndBox 7 1).hi ≤ ((0.673612 : ℚ)) := by nd_eval
theorem rd8x_lo : ((-0.764707 : ℚ)) ≤ (ndRingBox ndBox 8 0).lo := by nd_eval
theorem rd8x_hi : (ndRingBox ndBox 8 0).hi ≤ ((-0.764706 : ℚ)) := by nd_eval
theorem rd8y_lo : ((0.298369 : ℚ)) ≤ (ndRingBox ndBox 8 1).lo := by nd_eval
theorem rd8y_hi : (ndRingBox ndBox 8 1).hi ≤ ((0.298370 : ℚ)) := by nd_eval

end N11Formalization.FlashTilingSigns
