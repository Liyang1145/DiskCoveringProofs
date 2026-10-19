import N11Formalization.FlashTenBoundaryCoord
import N11Formalization.FlashTenBoundaryBranch

/-!
# C450 第 1 段：**内圆 v-形弧积分**（hub 侧圆的 interval 支）

内圆 = 以 hub `h` 为心、半径 `q = R = 19/50` 的圆；环盘半径也是 `R`。盘心写成
`h + R • w`，其中 `w` 是**相对**中心（归一化）：`‖w‖ = ℓ/R`（源文的 `ℓ = |c − h|`）。

* 归一化后 `r' = R/R = 1`，故 interval 支的半宽满足
  `cos t' = (1 + ‖w‖² − 1)/(2‖w‖) = ‖w‖/2`，即 **`t' = arccos(‖w‖/2)`**（‖w‖ ≤ 2 时可达；
  ‖w‖ > 2 走 `arc_integral_circle_vform_empty`，与源 `c450Q` 内层 `if ℓ < 2R then … else 0` 一致）。
* 方向余弦 = `w₀/‖w‖`，正对应源文的 `cq = cos ψ = (c₀ − e)/ℓ`（在 hub 落在 `(e,0)` 的规范框里）。
* **语法坑（ftbinner4 已踩）**：语句里裸写 `(19 / 50) • angPt θ` 会被 SMul 实例序
  廓成 `(19 : ℕ) / 50`（即 0），与 `arc_integral_circle_vform` 的 ℝ 形态失配。
  修法：语句内半径字面量一律显式写 `(19 : ℝ) / 50`。
* **消费点**：`two_circle_capacity`/`c450_capacity_contradiction` 的逐盘界里
  内圆项 `∫ θ, if dist (h + R•angPt θ) (c i) ≤ R …`，取 `w := R⁻¹ • (c i − h)`
  即归一到本件（`‖w‖ = ℓ/R`，`ℓ ≤ 2R` 支）；`ℓ > 2R` 支用 `arc_integral_circle_vform_empty`。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

section

/-- **内圆 interval 支（v-形）**：`0 < ‖w‖ ≤ 2` 时，hub 圆上该盘截出的弧积分闭式。 -/
theorem inner_arc_vform (W : TrigDensity) (h : Point) {w : Point} (hw : w ≠ 0)
    (hw2 : ‖w‖ ≤ 2) :
    ∫ θ in (0)..(2 * Real.pi),
        (if dist (h + ((19 : ℝ) / 50) • angPt θ) (h + ((19 : ℝ) / 50) • w) ≤ (19 : ℝ) / 50
          then W.toFun θ else 0)
      = 2 * (W.a0 * Real.arccos (‖w‖ / 2)
          + W.a1 * Real.sin (Real.arccos (‖w‖ / 2)) * (w 0 / ‖w‖)
          + W.a2 * Real.sin (2 * Real.arccos (‖w‖ / 2)) * (2 * (w 0 / ‖w‖) ^ 2 - 1) / 2
          + W.a3 * Real.sin (3 * Real.arccos (‖w‖ / 2)) * (4 * (w 0 / ‖w‖) ^ 3 - 3 * (w 0 / ‖w‖)) / 3) := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hq : (0 : ℝ) < 19 / 50 := by norm_num
  have hcos : Real.cos (Real.arccos (‖w‖ / 2))
      = (1 + ‖w‖ ^ 2 - (19 / 50 / (19 / 50)) ^ 2) / (2 * ‖w‖) := by
    rw [div_self (by norm_num : (19 : ℝ) / 50 ≠ 0)]
    have h2 : ‖w‖ / 2 ≤ 1 := by linarith
    have hm1 : -1 ≤ ‖w‖ / 2 := by linarith [norm_nonneg w]
    rw [Real.cos_arccos hm1 h2]
    field_simp
    ring
  exact arc_integral_circle_vform (W := W) (h := h) (q := 19 / 50) (w := w) (r := 19 / 50)
    (t := Real.arccos (‖w‖ / 2)) hq hw (by positivity) (Real.arccos_nonneg _)
    (Real.arccos_le_pi _) hcos

#print axioms N11Formalization.inner_arc_vform

end

end N11Formalization
