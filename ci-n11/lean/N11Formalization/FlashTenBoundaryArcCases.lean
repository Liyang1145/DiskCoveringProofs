import N11Formalization.FlashTenBoundaryArc

/-!
# C450 解析 consumer（第四层）：弧积分的**分情形闭式**（clamp / full / empty）

`FlashTenBoundaryArc`（冻结件）给出的是：当半宽 `t ∈ [0,π]` 由 `cos t = (1+ρ²-r²)/(2ρ)`
给出时，**单区间** `[φ-t, φ+t]` 上的积分闭式。本件补上**另外两种情形与退化**，
使"盘与单位圆的交弧"对**任意** `ρ ≥ 0, r ≥ 0` 都有确定结论：

| 情形 | 条件（`ρ ≥ 0`） | 弧 | 弧积分 |
|---|---|---|---|
| **full**（盘盖住整个单位圆） | `1 + ρ ≤ r` | 整圆 | `2π a_0` |
| **empty**（盘不碰单位圆） | `r ≤ |1 - ρ|` | 空/单点（零测） | `0` |
| **interval**（一般情形） | `|1-ρ| < r < 1+ρ`，`t = arccos((1+ρ²-r²)/(2ρ)) ∈ (0,π)` | 单区间 `[φ-t, φ+t]` | `2(a_0 t + Σ a_k sin(kt)cos(kφ)/k)` |

**为什么必须分情形（Lead 复核）**：`cos t = (1+ρ²-r²)/(2ρ)` 只定义在
`-1 ≤ (1+ρ²-r²)/(2ρ) ≤ 1`，即 `|1-ρ| ≤ r ≤ 1+ρ`；当 `r > 1+ρ` 时
`(1+ρ²-r²)/(2ρ) < -1`（**clamp** 到整圆），当 `r < |1-ρ|` 时 `> 1`（空弧）。
容量归一流程里内圆取 `ρ/s, r/s`，这两个越界情形**确实会出现**，
所以不能由 `hcos` 一形宣称"满盘/空弧已含在内"。
`ρ = 0`（盘心在原点）由上表两行直接覆盖（`1+0 ≤ r` 给整圆；`r ≤ 1` 给空弧）。

**与 `ρ = 0` 的衔接**：`ρ = 0` 时 `interval` 行不使用（`2ρ` 为 0，`t` 无定义），
故 `rho_eq_zero_full/empty` 已穷尽。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

open scoped Interval
open MeasureTheory

section

/-- **记账引理**：`Icc (φ-t)(φ+t)` 的指示函数在以 `φ` 为中心的整周区间上的积分
等于子区间 `[φ-t, φ+t]` 上的积分（`f` 连续即可；`t ∈ [0,π]`）。 -/
theorem integral_Icc_indicator_interval {f : ℝ → ℝ} (hf : Continuous f) {φ t : ℝ}
    (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) :
    ∫ θ in (φ - Real.pi)..(φ + Real.pi),
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)
      = ∫ θ in (φ - t)..(φ + t), f θ := by
  have hpt : ∀ θ ∈ Set.uIcc (φ - t) (φ + t),
      (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0) = f θ := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith)] at hθ
    simp [hθ]
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun θ : ℝ =>
      (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)) volume a b := by
    intro a b
    have hbase : IntervalIntegrable f volume a b := hf.intervalIntegrable (μ := volume) a b
    have hgm : AEStronglyMeasurable (fun θ : ℝ =>
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0))
        (volume.restrict (Ι a b)) :=
      (Measurable.ite measurableSet_Icc hf.measurable measurable_const).aestronglyMeasurable
    refine hbase.mono_fun hgm ?_
    filter_upwards with θ
    by_cases h : θ ∈ Set.Icc (φ - t) (φ + t)
    · simp only [h, if_true]; exact le_rfl
    · simp only [h, if_false, norm_zero]; exact norm_nonneg _
  have hsplit1 : ∫ θ in (φ - Real.pi)..(φ + Real.pi),
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)
      = (∫ θ in (φ - Real.pi)..(φ - t), (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0))
        + (∫ θ in (φ - t)..(φ + Real.pi), (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hint (φ - Real.pi) (φ - t)) (hint (φ - t) (φ + Real.pi))).symm
  have hsplit2 : ∫ θ in (φ - t)..(φ + Real.pi),
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)
      = (∫ θ in (φ - t)..(φ + t), (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0))
        + (∫ θ in (φ + t)..(φ + Real.pi), (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hint (φ - t) (φ + t)) (hint (φ + t) (φ + Real.pi))).symm
  have hmin_left : min (φ - Real.pi) (φ - t) = φ - Real.pi := min_eq_left (by linarith)
  have hmax_left : max (φ - Real.pi) (φ - t) = φ - t := max_eq_right (by linarith)
  have hmin_right : min (φ + t) (φ + Real.pi) = φ + t := min_eq_left (by linarith)
  have hmax_right : max (φ + t) (φ + Real.pi) = φ + Real.pi := max_eq_right (by linarith)
  have hz_left : ∫ θ in (φ - Real.pi)..(φ - t),
      (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0) = 0 := by
    have hae : ∀ᵐ θ ∂volume, θ ∈ Ι (φ - Real.pi) (φ - t) →
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0) = 0 := by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (by simp : volume ({φ - t} : Set ℝ) = 0)]
        with θ hθne hθin
      have h2 : θ ≤ φ - t := by
        have := hθin.2; rwa [hmax_left] at this
      have hnot : θ ∉ Set.Icc (φ - t) (φ + t) := fun hmem => hθne (le_antisymm h2 hmem.1)
      simp [hnot]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_zero]
  have hz_right : ∫ θ in (φ + t)..(φ + Real.pi),
      (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0) = 0 := by
    have hae : ∀ᵐ θ ∂volume, θ ∈ Ι (φ + t) (φ + Real.pi) →
        (if θ ∈ Set.Icc (φ - t) (φ + t) then f θ else 0) = 0 := by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (by simp : volume ({φ + t} : Set ℝ) = 0)]
        with θ hθne hθin
      have h1 : φ + t < θ := by
        have := hθin.1; rwa [hmin_right] at this
      have hnot : θ ∉ Set.Icc (φ - t) (φ + t) :=
        fun hmem => hθne (le_antisymm hmem.2 (le_of_lt h1))
      simp [hnot]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_zero]
  rw [hsplit1, hsplit2, hz_left, hz_right, zero_add,
    intervalIntegral.integral_congr hpt, add_zero]

/-- !₂[a,b] 的范数平方（与 dist_angPt_sq 同法）。 -/
theorem norm_ofLp_two_sq (a b : ℝ) : ‖(!₂[a, b] : Point)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp
  rw [Real.sq_sqrt (by positivity)]

theorem norm_ofLp_two (a b : ℝ) : ‖(!₂[a, b] : Point)‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_ofLp_two_sq]

/-- 盘心模：‖!₂[ρ cos φ, ρ sin φ]‖ = |ρ|（对 ρ 的符号也成立）。 -/
theorem norm_center (ρ φ : ℝ) : ‖(!₂[ρ * Real.cos φ, ρ * Real.sin φ] : Point)‖ = |ρ| := by
  rw [norm_ofLp_two, ← Real.sqrt_sq_eq_abs]
  congr 1
  rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]

/-- **full 情形**：1 + |ρ| ≤ r 时整个单位圆都在盘内（对 ρ 的符号也成立）。 -/
theorem arc_full {ρ r φ : ℝ} (hr : 1 + |ρ| ≤ r) (θ : ℝ) :
    dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r := by
  have h1 : dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ])
      ≤ ‖angPt θ‖ + ‖(!₂[ρ * Real.cos φ, ρ * Real.sin φ] : Point)‖ := dist_le_norm_add_norm _ _
  rw [norm_angPt θ, norm_center ρ φ] at h1
  linarith

/-- **empty 情形**： < abs (1 - |ρ|) 时盘与单位圆不相交（‖c‖ = |ρ| 到单位圆的距离是 bs (1 - |ρ|)）。 -/
theorem arc_empty {ρ r φ : ℝ} (hr : r < abs (1 - |ρ|)) (θ : ℝ) :
    r < dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) := by
  have h1 : |‖(!₂[ρ * Real.cos φ, ρ * Real.sin φ] : Point)‖ - ‖angPt θ‖|
      ≤ dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) := by
    calc |‖(!₂[ρ * Real.cos φ, ρ * Real.sin φ] : Point)‖ - ‖angPt θ‖|
        ≤ ‖(!₂[ρ * Real.cos φ, ρ * Real.sin φ] : Point) - angPt θ‖ := abs_norm_sub_norm_le _ _
      _ = dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) := by
          rw [dist_eq_norm, norm_sub_rev]
  rw [norm_center ρ φ, norm_angPt θ] at h1
  have h2 : abs (1 - |ρ|) = abs (|ρ| - 1) := by
    rw [show (1:ℝ) - |ρ| = -(|ρ| - 1) from by ring, abs_neg]
  rw [h2] at hr
  linarith
/-- **interval 情形的完整弧积分**：把 `[0,2π]` 上的弧积分化到
`[φ-π, φ+π]`（2π-周期平移）再用冻结件 `arc_iff_mem_Icc` + 闭式。 -/
theorem arc_integral_interval (W : TrigDensity) {ρ r φ t : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi)
    (hcos : Real.cos t = (1 + ρ ^ 2 - r ^ 2) / (2 * ρ)) :
    ∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r then W.toFun θ else 0)
      = 2 * (W.a0 * t + W.a1 * Real.sin t * Real.cos φ
          + W.a2 * Real.sin (2 * t) * Real.cos (2 * φ) / 2
          + W.a3 * Real.sin (3 * t) * Real.cos (3 * φ) / 3) := by
  let g : ℝ → ℝ := fun θ =>
    (if dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r then W.toFun θ else 0)
  have hper : Function.Periodic g (2 * Real.pi) := by
    intro θ
    simp only [g, angPt_add_two_pi θ, W.toFun_add_two_pi θ]
  have hshift := hper.intervalIntegral_add_eq 0 (φ - Real.pi)
  rw [zero_add, show φ - Real.pi + 2 * Real.pi = φ + Real.pi from by ring] at hshift
  have hcongr : ∫ θ in (φ - Real.pi)..(φ + Real.pi), g θ
      = ∫ θ in (φ - Real.pi)..(φ + Real.pi),
          (if θ ∈ Set.Icc (φ - t) (φ + t) then W.toFun θ else 0) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' : θ ∈ Set.Icc (φ - Real.pi) (φ + Real.pi) := by
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
      exact hθ
    have hiff := arc_iff_mem_Icc hρ hr ht0 htπ hcos hθ'
    simp only [g]
    by_cases h : dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r
    · simp only [h, if_true, hiff.mp h, if_true]
    · have h2 : θ ∉ Set.Icc (φ - t) (φ + t) := fun hh => h (hiff.mpr hh)
      simp only [h, if_false, h2, if_false]
  rw [show (∫ θ in (0)..(2 * Real.pi), g θ) = ∫ θ in (φ - Real.pi)..(φ + Real.pi), g θ from hshift,
    hcongr, integral_Icc_indicator_interval W.continuous_toFun ht0 htπ,
    integral_trigDensity_Icc W φ t]

/-- **full 情形的弧积分** = 总质量 2π a_0。 -/
theorem arc_integral_full (W : TrigDensity) {ρ r φ : ℝ} (hr : 1 + |ρ| ≤ r) :
    ∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r then W.toFun θ else 0)
      = 2 * Real.pi * W.a0 := by
  have h : ∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r then W.toFun θ else 0)
      = ∫ θ in (0)..(2 * Real.pi), W.toFun θ := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [if_pos (arc_full hr θ)]
  rw [h, W.integral_toFun]

/-- **empty 情形的弧积分** =  （空弧或单点弧，零测）。 -/
theorem arc_integral_empty (W : TrigDensity) {ρ r φ : ℝ} (hr : r < abs (1 - |ρ|)) :
    ∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r then W.toFun θ else 0)
      = 0 := by
  have h : ∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r then W.toFun θ else 0)
      = ∫ θ in (0)..(2 * Real.pi), (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [if_neg (not_le.mpr (arc_empty hr θ))]
  rw [h, intervalIntegral.integral_zero]

end

end N11Formalization