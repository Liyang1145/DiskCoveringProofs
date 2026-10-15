import N11Formalization.FlashTenBoundary
import N11Formalization.FlashTenBoundaryBranch

/-!
# C450 第 1 段：**接口桥**（C450 原子前提 → DiskBound 外圆带 + 内圆 ρ' > 0）

把 `hub_offset_le`（C1536 口径：十盘触 ∂D + 十一盘覆盖 D ⇒ ‖c hub‖ ≤ 7/50）与
每个非 hub 盘的 `MeetsCircle` 事实，一次性对齐到两个下游件的**逐盘前提**：

* **外圆**（`FlashTenBoundaryDiskBound.exists_t_of_rho_mem`/`outer_t_of_rho` 需要
  `1 − R ≤ ‖c i‖ ≤ 1 + R`）：下界 = `one_sub_le_norm_of_meetsCircle`；
  上界 = 三角不等式（本文件补的半边，src 此前无引理承载）。
* **内圆**（`FlashTenBoundaryBranch.inner_center_ne_hub` 需要
  `∃ x, ‖x‖ = 1 ∧ dist x (c i) ≤ R` 与 `‖h‖ ≤ 7/50`）：前者就是 `MeetsCircle` 的
  定义展开，后者 = `hub_offset_le` 的结论。

解锁：对每个 `i ≠ hub`，外圆 `t_i` 界（→ `arcsin_R_le_bound` 的 qBox）与内圆
`ρ'_i = ‖c i − c hub‖/R > 0`（→ `inner_branch_partition` → `inner_arc_vform` /
`arc_integral_circle_vform_empty`）在 C450 原子前提下**无条件可用**——即逐盘 hper
界模块（`two_circle_capacity`/`c450_capacity_contradiction` 声明的下一步）所需的
全部接口前提闭合。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

section

/-- **逐盘接口桥**：C450 前提下，每个非 hub 盘同时满足
外圆数据带（DiskBound 前提）与内圆非退化前提（Branch 的 ρ' > 0）。 -/
theorem per_disk_interface_of_c450 {c : Fin 11 → Point} {hub : Fin 11}
    (htouch : ∀ i : Fin 11, i ≠ hub → MeetsCircle c (19 / 50) i)
    (hcov : ∀ x : Point, ‖x‖ ≤ 1 → ∃ i : Fin 11, dist x (c i) ≤ 19 / 50)
    (i : Fin 11) (hi : i ≠ hub) :
    (1 - 19 / 50 ≤ ‖c i‖ ∧ ‖c i‖ ≤ 1 + 19 / 50) ∧ 0 < ‖c i - c hub‖ := by
  obtain ⟨x, hx, hd⟩ := htouch i hi
  have hlow : 1 - 19 / 50 ≤ ‖c i‖ := one_sub_le_norm_of_meetsCircle ⟨x, hx, hd⟩
  have hup : ‖c i‖ ≤ 1 + 19 / 50 := by
    have h1 : ‖c i‖ ≤ ‖c i - x‖ + ‖x‖ := by
      have ha : ‖c i‖ - ‖x‖ ≤ |‖c i‖ - ‖x‖| := le_abs_self _
      have hb : |‖c i‖ - ‖x‖| ≤ ‖c i - x‖ := abs_norm_sub_norm_le (c i) x
      linarith
    have h2 : ‖c i - x‖ = dist x (c i) := by
      rw [norm_sub_rev, dist_eq_norm]
    rw [hx, h2] at h1
    linarith
  exact ⟨⟨hlow, hup⟩, inner_center_ne_hub ⟨x, hx, hd⟩ (hub_offset_le htouch hcov)⟩

#print axioms N11Formalization.per_disk_interface_of_c450

end

end N11Formalization
