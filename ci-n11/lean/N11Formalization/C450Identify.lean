import N11Formalization.FlashTenBoundaryCoord
import N11Formalization.FlashTenBoundaryInner

/-!
# C450 十边界支：**实际弧积分 → 规范框架变量身份**（真 consumer 件）

**本文件不含 C450 的排除结论。** 它把 live consumer
`FlashTenBoundaryTwoCircle.c450_capacity_contradiction` 的**逐盘项**（`hper` 左端）

```
外_i + 内_i
  = (∫θ∈(0)..(2π) 1[dist (angPt θ) c ≤ R] · W0.toFun θ)
  + (∫θ∈(0)..(2π) 1[dist (!₂[e,0] + R • angPt θ) c ≤ R] · W1.toFun θ)
```

**恒等**认成源证书 `c450Q` 的两个闭式（规范框架 `h = !₂[e,0]`、`R = 19/50`）：

* 外：`Coord.arc_integral_unit_vform`（`t = arccos((1+ρ²−R²)/(2ρ))`、`v = c₀/ρ`）；
* 内：`Inner.inner_arc_vform`（`b = arccos(ℓ/(2R))`、`cq = (c₀−e)/ℓ`，`ℓ = ‖c − !₂[e,0]‖`、`ℓ ≤ 2R`）
  与 `Coord.arc_integral_circle_vform_empty`（`2R < ℓ` ⇒ 0）两支；边界 `ℓ = 2R` 归 interval 支（两支都给 0）。

## 口径 / 消去条件

* `R = 19/50` 精确有理；**所有 `SMul` 标量显式写 `(19 : ℝ)/50`**（DEAD 记录的坑：裸 `(19/50) • x` 会廓成 `(0:ℕ) • x = 0`）。
* 内圆归一化 `innerW c e := R⁻¹ • (c − !₂[e,0])`（`‖innerW‖ = ℓ/R`）；`!₂[e,0] + R • innerW = c` 在件内证。
* **零 ρ′ = 0 退化（ℓ = 0）**：由 `ℓ ≥ (1−R) − 7/50 = 24/50 > 0` 在件内排除（前提 `e ≤ 7/50`
  来自 `hub_offset_le`；`1−R ≤ ‖c‖` 来自触圆）。故 `inner_arc_vform` 的 `w ≠ 0` 与
  `cq = (c₀−e)/ℓ` 的分母合法，证书里 `if ℓ = 0 then 1` 支不可达。
* 旋转角不出现在任何 statement 里：`h = !₂[e,0]` 是**前提**（由 `C450FrameBridge.exists_rot_axis` 供给）。

## 不主张

* 不证/不声称十边界支已排除；本文件只给**恒等式**（两侧都真实存在）。
* 源 §4 的逐段盒不等式（把 `(t,v,sign)` 参数化下的 `c450Q` 压到 `π(a₀₀+a₁₀)/10` 以下）**不在本文件**。

## V2 相对 `lead/identify-gate1.log` exit1 的修复（5 处）

| gate1 位置 | 错误 | V2 修法 |
|---|---|---|
| L65:64 | `ell_pos_canonical` 用 `le_trans` 从 `e ≤ 7/50` 硬推 `0 ≤ e`（类型不成立） | **补全真 domain**：前提显式写 `(he0 : 0 ≤ e)` + `(he7 : e ≤ 7/50)`；消费端由 `norm_nonneg (c hub)` 与 `hub_offset_le` 供给；`ell_pos_canonical`/`inner_arc_canonical_le`/`inner_arc_canonical`/`pair_canonical` 同步加 `he0` 并透传 |
| L119:29 | `sq_le_sq.mpr habs` 要 `|·| ≤ |·|`，`habs : |‖c‖−1| ≤ 19/50` 右端不是 abs 形 | 用 `abs_le.mp` 取两侧 `hle1/hle2`，`mul_nonneg` 造 `(R−x)(R+x) ≥ 0`，再 `nlinarith` 得 `x² ≤ R²`（等价于 Lead 建议的 nlinarith+abs_le 路线） |
| L176:4 / L183:4 | `field_simp` 已关掉目标，随后的 `ring` 报 "No goals to be solved" | 改 `field_simp <;> ring`（无目标时自动跳过） |
| L199:4 | `rwa [h2] at h1` 后 `assumption` 失败：h1 是 `… * R⁻¹`，目标是 `R⁻¹ * …`（因子顺序不同） | 改 `rw [h2] at h1`，补 `hcomm : ℓ * R⁻¹ = R⁻¹ * ℓ := mul_comm _ _`，`linarith [h1, hcomm]` |
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

open scoped Interval
open MeasureTheory

section

/-! ## §0 工具 -/

theorem R_pos' : (0 : ℝ) < 19 / 50 := by norm_num

theorem R_ne' : (19 / 50 : ℝ) ≠ 0 := ne_of_gt R_pos'

/-- `‖!₂[e,0]‖ = e`（`e ≥ 0`）。 -/
theorem norm_pair_zero {e : ℝ} (he : 0 ≤ e) : ‖(!₂[e, 0] : Point)‖ = e := by
  have h := norm_sq_coord (!₂[e, 0] : Point)
  have h0 : (!₂[e, 0] : Point) 0 = e := by simp
  have h1 : (!₂[e, 0] : Point) 1 = 0 := by simp
  rw [h0, h1] at h
  have hsq : ‖(!₂[e, 0] : Point)‖ ^ 2 = e ^ 2 := by rw [h]; ring
  have h2 := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg he] at h2

/-- **`ℓ > 0`**（零 `ρ′` 退化的排除；前提 = 触圆 + **`0 ≤ e` 与 `e ≤ 7/50`**）。
`e = ‖h‖ ≥ 0` 由消费端 `norm_nonneg (c hub)` 供给，`e ≤ 7/50` 由 `hub_offset_le` 供给。 -/
theorem ell_pos_canonical {c : Point} {e : ℝ} (he0 : 0 ≤ e) (he7 : e ≤ 7 / 50)
    (hc1 : 1 - 19/50 ≤ ‖c‖) : 0 < ‖c - !₂[e, 0]‖ := by
  have h1 : ‖c‖ - ‖(!₂[e, 0] : Point)‖ ≤ ‖c - !₂[e, 0]‖ :=
    le_trans (le_abs_self _) (abs_norm_sub_norm_le c _)
  rw [norm_pair_zero he0] at h1
  linarith

/-- 内圆归一化点：`w := R⁻¹ • (c − !₂[e,0])`（`‖w‖ = ℓ/R`）。 -/
noncomputable def innerW (c : Point) (e : ℝ) : Point :=
  ((19 : ℝ) / 50)⁻¹ • (c - !₂[e, 0])

theorem norm_innerW (c : Point) (e : ℝ) :
    ‖innerW c e‖ = ((19 : ℝ) / 50)⁻¹ * ‖c - !₂[e, 0]‖ := by
  rw [innerW, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- `h + R • w = c`（归一化的目的）。 -/
theorem add_smul_innerW (c : Point) (e : ℝ) :
    (!₂[e, 0] : Point) + ((19 : ℝ) / 50) • innerW c e = c := by
  rw [innerW, smul_smul, mul_inv_cancel₀ R_ne', one_smul, add_sub_cancel]

/-! ## §1 外圆：实际弧积分 = `arc_integral_unit_vform` 的闭式 -/

/-- 源证书外圆量（规范框架）：`v = c₀/ρ`、`t = arccos((1+ρ²−R²)/(2ρ))`。 -/
noncomputable def c450Outer (W : TrigDensity) (c : Point) : ℝ :=
  W.a0 * Real.arccos ((1 + ‖c‖ ^ 2 - ((19 : ℝ) / 50) ^ 2) / (2 * ‖c‖))
    + W.a1 * Real.sin (Real.arccos ((1 + ‖c‖ ^ 2 - ((19 : ℝ) / 50) ^ 2) / (2 * ‖c‖)))
        * (c 0 / ‖c‖)
    + W.a2 * Real.sin (2 * Real.arccos ((1 + ‖c‖ ^ 2 - ((19 : ℝ) / 50) ^ 2) / (2 * ‖c‖)))
        * (2 * (c 0 / ‖c‖) ^ 2 - 1) / 2
    + W.a3 * Real.sin (3 * Real.arccos ((1 + ‖c‖ ^ 2 - ((19 : ℝ) / 50) ^ 2) / (2 * ‖c‖)))
        * (4 * (c 0 / ‖c‖) ^ 3 - 3 * (c 0 / ‖c‖)) / 3

/-- **外圆实际弧积分 = 2 × 源证书外圆量**（`arc_integral_unit_vform`）。 -/
theorem outer_arc_canonical (W : TrigDensity) {c : Point}
    (hc1 : 1 - 19/50 ≤ ‖c‖) (hc2 : ‖c‖ ≤ 1 + 19/50) :
    (∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) c ≤ (19 : ℝ) / 50 then W.toFun θ else 0))
      = 2 * c450Outer W c := by
  have hρ : 0 < ‖c‖ := by linarith [show (0 : ℝ) < 1 - 19 / 50 by norm_num]
  have hcne : c ≠ 0 := norm_pos_iff.mp hρ
  have hargge : -1 ≤ (1 + ‖c‖ ^ 2 - ((19 : ℝ) / 50) ^ 2) / (2 * ‖c‖) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ‖c‖)]
    have h2 : ((19 : ℝ) / 50) ^ 2 ≤ (‖c‖ + 1) ^ 2 := by
      have hle : |((19 : ℝ) / 50)| ≤ |‖c‖ + 1| := by
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (19 : ℝ) / 50),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖c‖ + 1)]
        linarith [norm_nonneg c]
      exact sq_le_sq.mpr hle
    nlinarith [h2]
  have hargle : (1 + ‖c‖ ^ 2 - ((19 : ℝ) / 50) ^ 2) / (2 * ‖c‖) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ‖c‖)]
    have habs : |‖c‖ - 1| ≤ (19 : ℝ) / 50 := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hsq : (‖c‖ - 1) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2 := by
      have hle1 : ‖c‖ - 1 ≤ (19 : ℝ) / 50 := (abs_le.mp habs).2
      have hle2 : -((19 : ℝ) / 50) ≤ ‖c‖ - 1 := (abs_le.mp habs).1
      have hR1 : 0 ≤ ((19 : ℝ) / 50) - (‖c‖ - 1) := by linarith
      have hR2 : 0 ≤ ((19 : ℝ) / 50) + (‖c‖ - 1) := by linarith
      nlinarith [mul_nonneg hR1 hR2]
    nlinarith [hsq]
  unfold c450Outer
  refine arc_integral_unit_vform W hcne (by norm_num : (0 : ℝ) ≤ (19 : ℝ) / 50)
    (Real.arccos_nonneg _) (Real.arccos_le_pi _) ?_
  exact Real.cos_arccos hargge hargle

/-! ## §2 内圆：两个分支（`ℓ ≤ 2R` 用 `inner_arc_vform`；`2R < ℓ` 用 empty 支） -/

/-- 源证书内圆半宽 `b`（规范框架；`ℓ = ‖c − !₂[e,0]‖`）。 -/
noncomputable def c450B (c : Point) (e : ℝ) : ℝ :=
  if ‖c - !₂[e, 0]‖ < 2 * ((19 : ℝ) / 50) then
    Real.arccos (‖c - !₂[e, 0]‖ / (2 * ((19 : ℝ) / 50)))
  else 0

/-- 源证书内圆方向余弦 `cq = (ρv − e)/ℓ = (c₀ − e)/ℓ`。 -/
noncomputable def c450Cq (c : Point) (e : ℝ) : ℝ := (c 0 - e) / ‖c - !₂[e, 0]‖

/-- 源证书内圆量（规范框架）。 -/
noncomputable def c450Inner (W : TrigDensity) (c : Point) (e : ℝ) : ℝ :=
  W.a0 * c450B c e + W.a1 * Real.sin (c450B c e) * c450Cq c e
    + W.a2 * Real.sin (2 * c450B c e) * (2 * c450Cq c e ^ 2 - 1) / 2
    + W.a3 * Real.sin (3 * c450B c e) * (4 * c450Cq c e ^ 3 - 3 * c450Cq c e) / 3

/-- **内圆 `ℓ ≤ 2R` 支**：实际弧积分 = 2 × 内圆闭式（`inner_arc_vform`）。 -/
theorem inner_arc_canonical_le (W : TrigDensity) {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7 / 50) (hc1 : 1 - 19/50 ≤ ‖c‖)
    (hle : ‖c - !₂[e, 0]‖ ≤ 2 * ((19 : ℝ) / 50)) :
    (∫ θ in (0)..(2 * Real.pi),
        (if dist (!₂[e, 0] + ((19 : ℝ) / 50) • angPt θ) c ≤ (19 : ℝ) / 50
          then W.toFun θ else 0))
      = 2 * (W.a0 * Real.arccos (‖c - !₂[e, 0]‖ / (2 * ((19 : ℝ) / 50)))
          + W.a1 * Real.sin (Real.arccos (‖c - !₂[e, 0]‖ / (2 * ((19 : ℝ) / 50))))
              * ((c 0 - e) / ‖c - !₂[e, 0]‖)
          + W.a2 * Real.sin (2 * Real.arccos (‖c - !₂[e, 0]‖ / (2 * ((19 : ℝ) / 50))))
              * (2 * ((c 0 - e) / ‖c - !₂[e, 0]‖) ^ 2 - 1) / 2
          + W.a3 * Real.sin (3 * Real.arccos (‖c - !₂[e, 0]‖ / (2 * ((19 : ℝ) / 50))))
              * (4 * ((c 0 - e) / ‖c - !₂[e, 0]‖) ^ 3
                - 3 * ((c 0 - e) / ‖c - !₂[e, 0]‖)) / 3) := by
  have hell : 0 < ‖c - !₂[e, 0]‖ := ell_pos_canonical he0 he7 hc1
  have hwne : innerW c e ≠ 0 := by
    rw [← norm_pos_iff, norm_innerW]
    exact mul_pos (by positivity) hell
  have hw2 : ‖innerW c e‖ ≤ 2 := by
    rw [norm_innerW]
    have h3 : ((19 : ℝ) / 50)⁻¹ * ‖c - !₂[e, 0]‖
        ≤ ((19 : ℝ) / 50)⁻¹ * (2 * ((19 : ℝ) / 50)) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have h4 : ((19 : ℝ) / 50)⁻¹ * (2 * ((19 : ℝ) / 50)) = 2 := by field_simp
    linarith [h3, h4]
  have key := inner_arc_vform W (!₂[e, 0] : Point) (w := innerW c e) hwne hw2
  have hsmul : (!₂[e, 0] : Point) + ((19 : ℝ) / 50) • innerW c e = c := add_smul_innerW c e
  rw [hsmul] at key
  have harg : ‖innerW c e‖ / 2 = ‖c - !₂[e, 0]‖ / (2 * ((19 : ℝ) / 50)) := by
    rw [norm_innerW]
    field_simp <;> ring
  have hcomp : (innerW c e) 0 = ((19 : ℝ) / 50)⁻¹ * (c 0 - e) := by
    rw [innerW]
    simp
  have hcq : (innerW c e) 0 / ‖innerW c e‖ = (c 0 - e) / ‖c - !₂[e, 0]‖ := by
    rw [hcomp, norm_innerW]
    field_simp <;> ring
  rw [harg, hcq] at key
  exact key

/-- **内圆 `2R < ℓ` 支**：实际弧积分 = 0（`arc_integral_circle_vform_empty`）。 -/
theorem inner_arc_canonical_gt (W : TrigDensity) {c : Point} {e : ℝ}
    (hgt : 2 * ((19 : ℝ) / 50) < ‖c - !₂[e, 0]‖) :
    (∫ θ in (0)..(2 * Real.pi),
        (if dist (!₂[e, 0] + ((19 : ℝ) / 50) • angPt θ) c ≤ (19 : ℝ) / 50
          then W.toFun θ else 0)) = 0 := by
  have hw2 : 2 < ‖innerW c e‖ := by
    rw [norm_innerW]
    have h1 : (2 * ((19 : ℝ) / 50)) * ((19 : ℝ) / 50)⁻¹
        < ‖c - !₂[e, 0]‖ * ((19 : ℝ) / 50)⁻¹ :=
      mul_lt_mul_of_pos_right hgt (by positivity)
    have h2 : (2 * ((19 : ℝ) / 50)) * ((19 : ℝ) / 50)⁻¹ = 2 := by field_simp
    rw [h2] at h1
    have hcomm : ‖c - !₂[e, 0]‖ * ((19 : ℝ) / 50)⁻¹
        = ((19 : ℝ) / 50)⁻¹ * ‖c - !₂[e, 0]‖ := mul_comm _ _
    linarith [h1, hcomm]
  have hr : (19 : ℝ) / 50 < (‖innerW c e‖ - 1) * ((19 : ℝ) / 50) := by
    rw [norm_innerW]
    have h1 : ((19 : ℝ) / 50)⁻¹ * ‖c - !₂[e, 0]‖ * ((19 : ℝ) / 50) = ‖c - !₂[e, 0]‖ := by
      field_simp
    rw [sub_mul, h1, one_mul]
    linarith
  have key := arc_integral_circle_vform_empty W (!₂[e, 0] : Point) (q := (19 : ℝ) / 50)
    R_pos' (w := innerW c e) hw2 (r := (19 : ℝ) / 50) hr
  have hsmul : (!₂[e, 0] : Point) + ((19 : ℝ) / 50) • innerW c e = c := add_smul_innerW c e
  rwa [hsmul] at key

/-- **内圆合计（`if ℓ < 2R` 形式）**：`c450B`/`c450Inner` 两支合一。 -/
theorem inner_arc_canonical (W : TrigDensity) {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7 / 50) (hc1 : 1 - 19/50 ≤ ‖c‖) :
    (∫ θ in (0)..(2 * Real.pi),
        (if dist (!₂[e, 0] + ((19 : ℝ) / 50) • angPt θ) c ≤ (19 : ℝ) / 50
          then W.toFun θ else 0))
      = 2 * c450Inner W c e := by
  unfold c450Inner
  by_cases hlt : ‖c - !₂[e, 0]‖ < 2 * ((19 : ℝ) / 50)
  · rw [c450B, if_pos hlt, c450Cq]
    exact inner_arc_canonical_le W he0 he7 hc1 hlt.le
  · rw [c450B, if_neg hlt, c450Cq]
    have hge : 2 * ((19 : ℝ) / 50) ≤ ‖c - !₂[e, 0]‖ := not_lt.mp hlt
    have hzero : W.a0 * 0 + W.a1 * Real.sin 0 * ((c 0 - e) / ‖c - !₂[e, 0]‖)
        + W.a2 * Real.sin (2 * 0) * (2 * ((c 0 - e) / ‖c - !₂[e, 0]‖) ^ 2 - 1) / 2
        + W.a3 * Real.sin (3 * 0)
            * (4 * ((c 0 - e) / ‖c - !₂[e, 0]‖) ^ 3
              - 3 * ((c 0 - e) / ‖c - !₂[e, 0]‖)) / 3 = 0 := by
      simp
    rw [hzero, mul_zero]
    rcases eq_or_lt_of_le hge with heq | hlt'
    · have hle : ‖c - !₂[e, 0]‖ ≤ 2 * ((19 : ℝ) / 50) := heq.ge
      rw [inner_arc_canonical_le W he0 he7 hc1 hle]
      have hA : ‖c - !₂[e, 0]‖ / (2 * ((19 : ℝ) / 50)) = 1 := by
        rw [heq]
        field_simp
      have harg : Real.arccos (‖c - !₂[e, 0]‖ / (2 * ((19 : ℝ) / 50))) = 0 := by
        rw [hA, Real.arccos_one]
      rw [harg]
      simp
    · exact inner_arc_canonical_gt W hlt'

/-! ## §3 合计：两圆实际弧积分和 = 2 × (外圆量 + 内圆量) -/

/-- **真 consumer 恒等式**（`c450_capacity_contradiction` 的 `hper` 左端 ↔ 源证书闭式）。 -/
theorem pair_canonical (W0 W1 : TrigDensity) {c : Point} {e : ℝ}
    (he0 : 0 ≤ e) (he7 : e ≤ 7 / 50) (hc1 : 1 - 19/50 ≤ ‖c‖) (hc2 : ‖c‖ ≤ 1 + 19/50) :
    (∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) c ≤ (19 : ℝ) / 50 then W0.toFun θ else 0))
      + (∫ θ in (0)..(2 * Real.pi),
        (if dist (!₂[e, 0] + ((19 : ℝ) / 50) • angPt θ) c ≤ (19 : ℝ) / 50
          then W1.toFun θ else 0))
      = 2 * c450Outer W0 c + 2 * c450Inner W1 c e := by
  rw [outer_arc_canonical W0 hc1 hc2, inner_arc_canonical W1 he0 he7 hc1]

#check @N11Formalization.norm_pair_zero
#check @N11Formalization.ell_pos_canonical
#check @N11Formalization.outer_arc_canonical
#check @N11Formalization.inner_arc_canonical_le
#check @N11Formalization.inner_arc_canonical_gt
#check @N11Formalization.inner_arc_canonical
#check @N11Formalization.pair_canonical

#print axioms N11Formalization.norm_pair_zero
#print axioms N11Formalization.ell_pos_canonical
#print axioms N11Formalization.outer_arc_canonical
#print axioms N11Formalization.inner_arc_canonical
#print axioms N11Formalization.pair_canonical

end

end N11Formalization
