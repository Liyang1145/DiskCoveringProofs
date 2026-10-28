import N11Formalization.FlashTenBoundaryScale

/-!
# C450 第 1 段装配：**分支划分** + `ρ' > 0`（Lead 指出的 ρ'=0 退化）

本件只做两件事（最小承重）：

1. **`inner_center_ne_hub`**：触圆环盘的中心与 hub **不可能重合** —— 由
   `‖c‖ ≥ 1 − R`（触圆）与 `‖h‖ ≤ 7/50`（`hub_offset_le`）得 `‖c − h‖ ≥ 1 − R − 7/50 = 24/50 > 0`。
   于是内圆归一参数 `ρ' = ‖c − h‖/R > 0`，**排除** `1 + ρ' ≤ 1`（full）这一可满足退化
   （Lead 复核：`ρ' = 0` 确实满足 full 条件，不能只由 `ρ' ≤ 0` 说不可达；必须由假设推出
   `‖c − h‖ > 0`）。
2. **`outer_branch_interval` / `inner_branch_partition`**：两个测试圆上的分支归属
   （interval / empty），边界归 interval（`t = 0` 退化）。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

open scoped Interval
open MeasureTheory

section

/-- 触圆（单位圆）⇒ 中心范数 `≥ 1 − R`（不依赖 BoundaryCount 的 `Fin 11` 形式）。 -/
theorem one_sub_le_norm_of_touches {c : Point} (htouch : ∃ x : Point, ‖x‖ = 1 ∧ dist x c ≤ 19 / 50) :
    1 - 19 / 50 ≤ ‖c‖ := by
  obtain ⟨x, hx, hd⟩ := htouch
  have h1 : ‖x‖ - ‖c‖ ≤ ‖x - c‖ := le_trans (le_abs_self _) (abs_norm_sub_norm_le x c)
  rw [hx] at h1
  rw [dist_eq_norm] at hd
  linarith

/-- **`ρ' > 0`（排除 ρ'=0 的 full 退化）**：触圆环盘中心 `c` 与 hub `h` 不重合。 -/
theorem inner_center_ne_hub {c h : Point}
    (htouch : ∃ x : Point, ‖x‖ = 1 ∧ dist x c ≤ 19 / 50) (hhub : ‖h‖ ≤ 7 / 50) :
    0 < ‖c - h‖ := by
  have hc := one_sub_le_norm_of_touches htouch
  have h2 : ‖c‖ - ‖h‖ ≤ ‖c - h‖ := le_trans (le_abs_self _) (abs_norm_sub_norm_le c h)
  linarith

/-- **外圆分支**：触圆环盘（`1 − R ≤ ρ ≤ 1 + R`）在单位圆上恒为 **interval 支**
（`|1−ρ| ≤ R` 且 `R < 1+ρ`；端点 `ρ = 1±R` 给 `t = 0`，仍属 interval）。 -/
theorem outer_branch_interval {ρ : ℝ} (h1 : 1 - 19 / 50 ≤ ρ) (h2 : ρ ≤ 1 + 19 / 50) :
    |1 - ρ| ≤ 19 / 50 ∧ 19 / 50 < 1 + ρ := by
  have hpos : 0 < ρ := by linarith [show (0:ℝ) < 19 / 50 by norm_num, show (19:ℝ) / 50 < 1 by norm_num]
  refine ⟨abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩, by linarith⟩

/-- **内圆分支划分**：`ρ' = ‖c − h‖ / R`（由 `inner_center_ne_hub` 得 `> 0`）满足
`ρ' ≤ 2`（interval，半宽 `t' = arccos(ρ'/2)`）**或** `2 < ρ'`（empty，弧积分 0）。
边界 `ρ' = 2` 归 interval（`t' = 0`，两边都给 0）。 -/
theorem inner_branch_partition {ρ' : ℝ} (_hpos : 0 < ρ') :
    ρ' ≤ 2 ∨ 2 < ρ' := by
  by_cases h : ρ' ≤ 2
  · exact Or.inl h
  · exact Or.inr (not_le.mp h)

end

end N11Formalization
