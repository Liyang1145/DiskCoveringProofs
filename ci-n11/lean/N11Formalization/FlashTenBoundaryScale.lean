import N11Formalization.FlashTenBoundaryArcCases

/-!
# C450 解析 consumer（第五层）：**任意测试圆半径 `q` 的标度归约**

L1（`circle_integral_le_sum_arc_integrals_circle`）的测试圆是**圆心 `h`、半径 `q`** 的圆
`h + q • angPt θ`；而冻结的 Arc/Cases 件给的是**单位圆**（`angPt θ`）上的弧闭式。
本件补上两者之间的**标度桥**（源文内圆用 `q ↓ R`、中心 `c hub` 的圆，半径 `q ≠ 1`）：

> `dist (h + q•angPt θ) (h + q•w) ≤ r  ↔  dist (angPt θ) w ≤ r/q`   （`q > 0`）

**为什么必须有这一步（Lead 复核）**：把单位圆的界直接当 `q ≠ 1` 的界的读数是**错的**；
内圆对象是 `ρ = ‖c − h‖/q`、半径 `r/q` 的单位圆问题，故必须显式标度。

## 情形的**闭**半宽范围（按 type；更正此前报告里的 `[-1,1)` 写法）

`t` 与 `q := (1+ρ²-(r/q)²)/(2ρ)` 的关系（`ρ > 0`）：

* `q > 1`（`⇔ r < |1-ρ|·q`）：**empty**（无交）；
* `q < -1`（`⇔ r > (1+ρ)·q`）：**full**（整圆）；
* `q ∈ [-1, 1]`（**闭**）：`t = arccos q ∈ [0, π]`，其中
  * `q = 1 ⇔ t = 0`：退化单点弧（内切于最近点），闭式给 `0`；
  * `q = -1 ⇔ t = π`：满弧（外切于最远点），闭式与 full 情形**一致**（`sin(kπ) = 0`）。
  两件闭式的 type 都取 `t ∈ [0,π]` 闭区间（`ht0 : 0 ≤ t`、`htπ : t ≤ π`），与上面一致。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

open scoped Interval
open MeasureTheory

section

/-- 平移不变：`dist (h+a) (h+b) = dist a b`。 -/
theorem dist_add_left_eq (h a b : Point) : dist (h + a) (h + b) = dist a b := by
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub]

/-- 正标度：`dist (q•a) (q•b) = q * dist a b`（`q ≥ 0`）。 -/
theorem dist_smul_of_nonneg {q : ℝ} (hq : 0 ≤ q) (a b : Point) :
    dist (q • a) (q • b) = q * dist a b := by
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]

/-- **标度归约**（本层的核心）：圆心 `h` 半径 `q > 0` 的测试圆与"平移 + 标度后的盘"
的交，等于单位圆与标度后中心 `w`、半径 `r/q` 的盘的交。 -/
theorem arc_scale {h : Point} {q : ℝ} (hq : 0 < q) (w : Point) {r : ℝ} (θ : ℝ) :
    dist (h + q • angPt θ) (h + q • w) ≤ r ↔ dist (angPt θ) w ≤ r / q := by
  rw [dist_add_left_eq, dist_smul_of_nonneg hq.le]
  constructor
  · intro h
    rw [le_div_iff₀ hq]
    linarith
  · intro h
    have := (le_div_iff₀ hq).mp h
    linarith

/-- **标度后的弧积分闭式（interval 情形）**：把 Cases 件的单位圆闭式搬到
圆心 `h`、半径 `q` 的测试圆上；此时有效参数是 `ρ = ‖c-h‖/q`、半径 `r/q`。 -/
theorem arc_integral_scale_interval (W : TrigDensity) (h : Point) {q : ℝ} (hq : 0 < q)
    {ρ r φ t : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r) (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi)
    (hcos : Real.cos t = (1 + ρ ^ 2 - (r / q) ^ 2) / (2 * ρ)) :
    ∫ θ in (0)..(2 * Real.pi),
        (if dist (h + q • angPt θ) (h + q • !₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r
          then W.toFun θ else 0)
      = 2 * (W.a0 * t + W.a1 * Real.sin t * Real.cos φ
          + W.a2 * Real.sin (2 * t) * Real.cos (2 * φ) / 2
          + W.a3 * Real.sin (3 * t) * Real.cos (3 * φ) / 3) := by
  have hfun : (fun θ : ℝ => (if dist (h + q • angPt θ)
        (h + q • !₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r then W.toFun θ else 0))
      = fun θ : ℝ => (if dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r / q
          then W.toFun θ else 0) := by
    funext θ
    by_cases hθ : dist (h + q • angPt θ) (h + q • !₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r
    · have h2 : dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r / q :=
        (arc_scale hq _ θ).mp hθ
      simp only [hθ, if_true, h2]
    · have h2 : ¬ dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r / q :=
        fun hh => hθ ((arc_scale hq _ θ).mpr hh)
      simp only [hθ, if_false, h2, if_false]
  rw [hfun]
  exact arc_integral_interval W hρ (by positivity) ht0 htπ hcos

/-- **标度后的 full 情形**：`(1+ρ)·q ≤ r` 时标度盘盖住整个测试圆。 -/
theorem arc_scale_full {h : Point} {q : ℝ} (hq : 0 < q) {ρ r φ : ℝ}
    (hr : (1 + |ρ|) * q ≤ r) (θ : ℝ) :
    dist (h + q • angPt θ) (h + q • !₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r := by
  rw [arc_scale hq _ θ]
  have h2 : 1 + |ρ| ≤ r / q := by rw [le_div_iff₀ hq]; linarith
  exact arc_full h2 θ

/-- **标度后的 empty 情形**：`r < abs (1 - |ρ|) * q` 时标度盘与测试圆不相交。 -/
theorem arc_scale_empty {h : Point} {q : ℝ} (hq : 0 < q) {ρ r φ : ℝ}
    (hr : r < abs (1 - |ρ|) * q) (θ : ℝ) :
    r < dist (h + q • angPt θ) (h + q • !₂[ρ * Real.cos φ, ρ * Real.sin φ]) := by
  rw [← not_le, arc_scale hq _ θ, not_le]
  have h2 : r / q < abs (1 - |ρ|) := by rw [div_lt_iff₀ hq]; linarith
  exact arc_empty h2 θ

/-- **clamp 合一**（本层的消费形状）：对任意 `ρ ≥ 0`、`q > 0`、`r ≥ 0`，测试圆上的
弧积分由**三分支**给出 —— full（整圆）/ empty（空弧）/ interval（半宽 `t = arccos ·`）。
`ρ = 0` 时第三支不可达（`1 ≤ r` 走 full、`r < 1` 走 empty），故 `2ρ` 出现在不可达支里无害。

`-1 ≤ arg ≤ 1` 由两个分支条件的**否定**给出：`¬ full` ⇒ `r/q < 1+ρ`（arg ≥ -1），
`¬ empty` ⇒ `|1-ρ| ≤ r/q`（arg ≤ 1）。 -/
theorem arc_integral_scale_clamp (W : TrigDensity) (h : Point) {q : ℝ} (hq : 0 < q)
    {ρ r φ : ℝ} (hρ0 : 0 ≤ ρ) (hr0 : 0 ≤ r) :
    (∫ θ in (0)..(2 * Real.pi),
        (if dist (h + q • angPt θ) (h + q • !₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r
          then W.toFun θ else 0))
      = if (1 + ρ) * q ≤ r then 2 * Real.pi * W.a0
        else if r < |1 - ρ| * q then 0
        else let t := Real.arccos ((1 + ρ ^ 2 - (r / q) ^ 2) / (2 * ρ))
          2 * (W.a0 * t + W.a1 * Real.sin t * Real.cos φ
            + W.a2 * Real.sin (2 * t) * Real.cos (2 * φ) / 2
            + W.a3 * Real.sin (3 * t) * Real.cos (3 * φ) / 3) := by
  by_cases hfull : (1 + ρ) * q ≤ r
  · rw [if_pos hfull]
    have hfull' : (1 + |ρ|) * q ≤ r := by rw [abs_of_nonneg hρ0]; exact hfull
    have hcongr : (∫ θ in (0)..(2 * Real.pi),
        (if dist (h + q • angPt θ) (h + q • !₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r
          then W.toFun θ else 0)) = ∫ θ in (0)..(2 * Real.pi), W.toFun θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [if_pos (arc_scale_full hq hfull' θ)]
    rw [hcongr, W.integral_toFun]
  · rw [if_neg hfull]
    have hr_lt : r < (1 + ρ) * q := not_le.mp hfull
    by_cases hemp : r < |1 - ρ| * q
    · rw [if_pos hemp]
      have hemp' : r < abs (1 - |ρ|) * q := by rw [abs_of_nonneg hρ0]; exact hemp
      have hcongr : (∫ θ in (0)..(2 * Real.pi),
          (if dist (h + q • angPt θ) (h + q • !₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r
            then W.toFun θ else 0)) = ∫ θ in (0)..(2 * Real.pi), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        simp only [if_neg (not_le.mpr (arc_scale_empty hq hemp' θ))]
      rw [hcongr, intervalIntegral.integral_zero]
    · rw [if_neg hemp]
      have hge : |1 - ρ| * q ≤ r := not_lt.mp hemp
      have hρpos : 0 < ρ := by
        by_contra hcon
        have h0 : ρ = 0 := le_antisymm (not_lt.mp hcon) hρ0
        rw [h0] at hr_lt hge
        simp at hr_lt hge
        linarith
      have hle1 : r / q ≤ 1 + ρ := by rw [div_le_iff₀ hq]; linarith
      have hge1 : |1 - ρ| ≤ r / q := by rw [le_div_iff₀ hq]; linarith
      have hargle : (1 + ρ ^ 2 - (r / q) ^ 2) / (2 * ρ) ≤ 1 := by
        rw [div_le_iff₀ (by positivity)]
        have hsq : (1 - ρ) ^ 2 ≤ (r / q) ^ 2 := by
          have hge1' : |1 - ρ| ≤ |r / q| := by
            rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ r / q)]
          exact sq_le_sq.mpr hge1'
        nlinarith [hsq]
      have hargge : -1 ≤ (1 + ρ ^ 2 - (r / q) ^ 2) / (2 * ρ) := by
        rw [le_div_iff₀ (by positivity)]
        have hsq : (r / q) ^ 2 ≤ (1 + ρ) ^ 2 := by
          have h1 : |r / q| ≤ |1 + ρ| := by
            rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ r / q),
              abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + ρ)]
            exact hle1
          exact sq_le_sq.mpr h1
        nlinarith [hsq]
      have hmain : (∫ θ in (0)..(2 * Real.pi),
            (if dist (h + q • angPt θ) (h + q • !₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r
              then W.toFun θ else 0))
          = 2 * (W.a0 * Real.arccos ((1 + ρ ^ 2 - (r / q) ^ 2) / (2 * ρ))
              + W.a1 * Real.sin (Real.arccos ((1 + ρ ^ 2 - (r / q) ^ 2) / (2 * ρ))) * Real.cos φ
              + W.a2 * Real.sin (2 * Real.arccos ((1 + ρ ^ 2 - (r / q) ^ 2) / (2 * ρ)))
                  * Real.cos (2 * φ) / 2
              + W.a3 * Real.sin (3 * Real.arccos ((1 + ρ ^ 2 - (r / q) ^ 2) / (2 * ρ)))
                  * Real.cos (3 * φ) / 3) :=
        arc_integral_scale_interval W h hq hρpos hr0 (Real.arccos_nonneg _)
          (Real.arccos_le_pi _) (by rw [Real.cos_arccos hargge hargle])
      exact hmain

end

end N11Formalization
