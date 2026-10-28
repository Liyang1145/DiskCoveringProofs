/-
n=11 全局最优性形式化 —— 几何桥 CapArc（kernel-checked 核心）

本文件只包含**已证**（无 sorry、无自定义 axiom）的引理：

* (a) `Real.arcsin (19/50) < π/8` 及其推论 `8 * arcsin (19/50) < π`（纯数值内核事实，R0 = 19/50 = 0.38）；
* (b) cap 直径界：落在同一闭盘 `closedBall c r` 里的单位球面两点距离 ≤ 2r（三角不等式）；
* (c) cap 是半平面截圆：`‖x‖ = 1` 时 `dist x c ≤ r ↔ 1 + ‖c‖^2 - r^2 ≤ 2 * ⟪x,c⟫`；
* (d-lite) cap 的角宽 ≤ 2 arcsin r 的**内积形式**（无需 angle 库）：
      `x, y ∈ S¹ ∩ closedBall c r ⟹ ⟪x,y⟫ ≥ cos (2 * arcsin r)`。

约定：`Point := EuclideanSpace ℝ (Fin 2)`，范数/距离/内积都取欧氏结构。
单位：长度以单位圆盘半径 1 为单位；角度以弧度为单位。

文档：research-2026/n11-formalization/evidence/CAP-ARC-REDUCTION.md
-/
import Mathlib
import N11Formalization.Definitions

set_option linter.unusedVariables false

namespace N11Formalization

noncomputable section

/-! 约定：`Point`（以及其欧氏结构）由 `N11Formalization.Definitions` 提供，本文件不重复声明，
避免与集成人员的接口定义同名冲突（GUIDE §9 接口由集成人员维护）。 -/

/-! ## (a) 纯数值内核事实：`arcsin (19/50) < π/8` -/

/-- 关键数值不等式：`arcsin (19/50) < π/8`（R0 = 19/50 = 0.38）。
路线：`arcsin_lt_iff_lt_sin` 化归到 `19/50 < sin (π/8)`，
再用 `sin_pi_div_eight` 与 `√2 < 889/625`（即 `2 < (889/625)^2`）纯有理收尾。 -/
theorem arcsin_R0_lt_pi_div_eight : Real.arcsin ((19 : ℝ) / 50) < Real.pi / 8 := by
  refine (Real.arcsin_lt_iff_lt_sin (x := (19 : ℝ) / 50) (y := Real.pi / 8)
    (by norm_num) (by constructor <;> linarith [Real.pi_pos])).2 ?_
  rw [Real.sin_pi_div_eight]
  have h2 : Real.sqrt 2 < (889 : ℝ) / 625 := by
    rw [Real.sqrt_lt' (show (0 : ℝ) < 889 / 625 by norm_num)]
    norm_num
  have h3 : ((19 : ℝ) / 25) ^ 2 < 2 - Real.sqrt 2 := by nlinarith
  have h4 : (19 : ℝ) / 25 < Real.sqrt (2 - Real.sqrt 2) := Real.lt_sqrt_of_sq_lt h3
  linarith

/-- 装配用的形式：8 条角半宽 `arcsin R0` 的弧总宽不足一整圈。 -/
theorem eight_mul_arcsin_R0_lt_pi : 8 * Real.arcsin ((19 : ℝ) / 50) < Real.pi := by
  linarith [arcsin_R0_lt_pi_div_eight]

/-- `arcsin R0 > 0`，用于非空中介。 -/
theorem arcsin_R0_pos : 0 < Real.arcsin ((19 : ℝ) / 50) :=
  Real.arcsin_pos.mpr (by norm_num)

/-- `0 ≤ arcsin R0`。 -/
theorem arcsin_R0_nonneg : 0 ≤ Real.arcsin ((19 : ℝ) / 50) := arcsin_R0_pos.le

/-- `arcsin R0 ≤ π/2`（`arcsin` 值域），配合 8× 界使用。 -/
theorem arcsin_R0_le_pi_div_two : Real.arcsin ((19 : ℝ) / 50) ≤ Real.pi / 2 :=
  Real.arcsin_le_pi_div_two _

/-! ## (b) cap 直径界 -/

/-- 任一满足 `dist u c ≤ r`、`dist v c ≤ r` 的两点距离 ≤ 2r（纯三角不等式）。 -/
theorem dist_le_two_mul_of_mem_closedBall {u v c : Point} {r : ℝ}
    (huc : dist u c ≤ r) (hvc : dist v c ≤ r) : dist u v ≤ 2 * r := by
  have h1 : dist u v ≤ dist u c + dist c v := dist_triangle u c v
  rw [dist_comm c v] at h1
  linarith

/-- 任务书中给出的接口形式（`‖u‖ = ‖v‖ = 1` 实际上是多余的：结论不依赖它）。
这里保留原签名以便下游按原样调用；`hu`、`hv` 未被使用，真实等级仍为 kernel-proved。 -/
theorem dist_le_two_mul_of_mem_closedBall_circle {u v c : Point} {r : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huc : dist u c ≤ r) (hvc : dist v c ≤ r) :
    dist u v ≤ 2 * r :=
  dist_le_two_mul_of_mem_closedBall huc hvc

/-- cap 的弦长版本：同一条 cap（`S¹ ∩ closedBall c r`）里任意两点距离 ≤ 2r。 -/
theorem cap_chord_le {u v c : Point} {r : ℝ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huc : dist u c ≤ r) (hvc : dist v c ≤ r) : dist u v ≤ 2 * r :=
  dist_le_two_mul_of_mem_closedBall huc hvc

/-! ## (c) cap = 半平面截圆 -/

/-- `‖x‖ = 1`、`0 ≤ r` 时，`dist x c ≤ r` 等价于内积半平面条件（把弧变成区间的那一行）。 -/
theorem mem_sphere_closedBall_iff {x c : Point} {r : ℝ} (hr : 0 ≤ r) (hx : ‖x‖ = 1) :
    dist x c ≤ r ↔ 1 + ‖c‖ ^ 2 - r ^ 2 ≤ 2 * inner ℝ x c := by
  have hsq : dist x c ^ 2 = 1 + ‖c‖ ^ 2 - 2 * inner ℝ x c := by
    rw [dist_eq_norm, norm_sub_sq_real, hx]
    ring
  have hiff : dist x c ≤ r ↔ dist x c ^ 2 ≤ r ^ 2 := by
    constructor
    · intro h
      nlinarith [(dist_nonneg : (0 : ℝ) ≤ dist x c), h]
    · intro h
      nlinarith [(dist_nonneg : (0 : ℝ) ≤ dist x c), hr, h]
  rw [hiff, hsq]
  constructor <;> intro h <;> linarith

/-- 同一条 cap 的另一种写法（half-space 形式的方向翻转版，装配时更好用）。 -/
theorem mem_sphere_closedBall_iff' {x c : Point} {r : ℝ} (hr : 0 ≤ r) (hx : ‖x‖ = 1) :
    dist x c ≤ r ↔ 1 + ‖c‖ ^ 2 - r ^ 2 ≤ 2 * inner ℝ x c :=
  mem_sphere_closedBall_iff hr hx

/-! ## (d-lite) cap 的角宽 ≤ 2 arcsin r（内积形式，不引入 angle 库） -/

/-- `cos (2 arcsin r) = 1 - 2 r²`（`0 ≤ r ≤ 1`）。 -/
theorem cos_two_arcsin (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.cos (2 * Real.arcsin r) = 1 - 2 * r ^ 2 := by
  rw [Real.cos_two_mul, Real.cos_arcsin, Real.sq_sqrt (by nlinarith)]
  ring

/-- **cap 的角宽界（内积形式）**：`S¹ ∩ closedBall c r` 中任意两点 `x, y` 满足
`⟪x,y⟫ ≥ cos (2 arcsin r)`，即单位圆上它们的中心角 ≤ `2 arcsin r`。
这是把 `2 arcsin r` 与 cap 几何真正连接起来的一步（弦 ≤ 2r ⟹ 角 ≤ 2 arcsin r）。 -/
theorem inner_ge_cos_two_arcsin_of_mem_cap {x y c : Point} {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxc : dist x c ≤ r)
    (hyc : dist y c ≤ r) : Real.cos (2 * Real.arcsin r) ≤ inner ℝ x y := by
  have hd : dist x y ≤ 2 * r := dist_le_two_mul_of_mem_closedBall hxc hyc
  have hd2 : dist x y ^ 2 ≤ (2 * r) ^ 2 := by
    have h0 : (0:ℝ) ≤ dist x y := dist_nonneg
    nlinarith
  have hsq : dist x y ^ 2 = 2 - 2 * inner ℝ x y := by
    rw [dist_eq_norm, norm_sub_sq_real, hx, hy]
    ring
  rw [cos_two_arcsin r hr0 hr1]
  nlinarith

/-- 弦 ≤ 2r ⟹ `⟪x,y⟫ ≥ 1 - 2r²` 的纯内积版本（不含 arcsin），有时更方便调用。 -/
theorem inner_ge_one_sub_two_mul_sq {x y c : Point} {r : ℝ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxc : dist x c ≤ r) (hyc : dist y c ≤ r) : 1 - 2 * r ^ 2 ≤ inner ℝ x y := by
  have hd : dist x y ≤ 2 * r := dist_le_two_mul_of_mem_closedBall hxc hyc
  have hd2 : dist x y ^ 2 ≤ (2 * r) ^ 2 := by
    have h0 : (0:ℝ) ≤ dist x y := dist_nonneg
    nlinarith
  have hsq : dist x y ^ 2 = 2 - 2 * inner ℝ x y := by
    rw [dist_eq_norm, norm_sub_sq_real, hx, hy]
    ring
  nlinarith

end

/-! ## 可信基础：主引理的公理依赖（`#print axioms`） -/

#print axioms N11Formalization.arcsin_R0_lt_pi_div_eight
#print axioms N11Formalization.eight_mul_arcsin_R0_lt_pi
#print axioms N11Formalization.dist_le_two_mul_of_mem_closedBall_circle
#print axioms N11Formalization.mem_sphere_closedBall_iff
#print axioms N11Formalization.cos_two_arcsin
#print axioms N11Formalization.inner_ge_cos_two_arcsin_of_mem_cap

end N11Formalization
