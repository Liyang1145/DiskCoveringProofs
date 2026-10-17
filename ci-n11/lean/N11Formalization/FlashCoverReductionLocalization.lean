/-
# FlashCoverReductionLocalization — 凸闭胞腔的紧致局部化（源 §2 的内核版）

作者：flash-cover-reduction。写域：`lean/N11Formalization/FlashCoverReduction*.lean`。

## 数学内容（源 `VORONOI-BOUNDARY-REDUCTION.md` §2）

设 `C ⊆ Point`（Voronoi 胞腔）**凸**、**闭**，含一点 `x` 且 `‖x‖ < 1`，
并且 `C` 与单位圆**不交**（`∀ y ∈ C, ‖y‖ ≠ 1`）。则
```
C ⊆ {y | ‖y‖ < 1}        （V_h ⊆ int D）
```
**证明**（内核）：反设 `y ∈ C` 且 `‖y‖ ≥ 1`。
- `‖y‖ = 1` 直接与"不交"矛盾；
- `‖y‖ > 1`：取线段 `z(t) = (1−t)x + t y`（`t ∈ [0,1]`），凸性给 `z(t) ∈ C`；
  `t ↦ ‖z(t)‖` 连续，`‖z(0)‖ < 1 < ‖z(1)‖`，介值定理给出 `t₀` 使 `‖z(t₀)‖ = 1`，
  与"不交"矛盾。

第二条（源 §2 的 `V_h ⊆ B(h,r)`）由"覆盖 + h 最近"给出，不需要凸性/紧性；
它属于 witness 接口的用途，见 `NOTE-HUB-CELL-BOUNDED.md` H6。

## 量词

任意 `C : Set Point`（凸、闭）、任意 `x ∈ C`（`‖x‖ < 1`）、
`C` 与单位球的交空；结论对 `C` 的每个点。
-/

import Mathlib
import N11Formalization.Definitions

namespace N11Formalization

/-- **凸闭集不与单位圆相交 ⇒ 整体落在开单位球内**（`V_h ⊆ int D` 的内核形式）。 -/
theorem convex_closed_norm_lt_one {C : Set Point}
    (hconv : Convex ℝ C)
    {x : Point} (hx : x ∈ C) (hx1 : ‖x‖ < 1)
    (hdisj : ∀ y ∈ C, ‖y‖ ≠ 1) :
    ∀ y ∈ C, ‖y‖ < 1 := by
  intro y hy
  by_contra hcon
  push Not at hcon
  rcases lt_or_eq_of_le hcon with hlt | heq
  · -- ‖y‖ > 1：线段上的范数由 <1 变到 >1，介值给出 =1 的点
    have hcont : ContinuousOn (fun t : ℝ => ‖(1 - t) • x + t • y‖) (Set.Icc 0 1) := by
      fun_prop
    have h0 : ‖(1 - (0 : ℝ)) • x + (0 : ℝ) • y‖ < 1 := by simpa using hx1
    have h1 : 1 < ‖(1 - (1 : ℝ)) • x + (1 : ℝ) • y‖ := by simpa using hlt
    obtain ⟨t, ht, htx⟩ :=
      intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcont
        (show (1 : ℝ) ∈ Set.Icc (‖(1 - (0 : ℝ)) • x + (0 : ℝ) • y‖)
            (‖(1 - (1 : ℝ)) • x + (1 : ℝ) • y‖) from ⟨h0.le, h1.le⟩)
    have hmem : (1 - t) • x + t • y ∈ C := by
      refine hconv hx hy ?_ ?_ ?_
      · linarith [ht.2]
      · linarith [ht.1]
      · ring
    exact hdisj _ hmem htx
  · exact hdisj y hy heq.symm

/-- 推论：把 `C` 与单位圆的不交性写成集合形式（用于 hub 胞腔实例化）。 -/
theorem convex_closed_subset_ball {C : Set Point}
    (hconv : Convex ℝ C)
    {x : Point} (hx : x ∈ C) (hx1 : ‖x‖ < 1)
    (hdisj : ∀ y ∈ C, ‖y‖ ≠ 1) :
    C ⊆ {y : Point | ‖y‖ < 1} :=
  fun y hy => convex_closed_norm_lt_one hconv hx hx1 hdisj y hy

end N11Formalization
