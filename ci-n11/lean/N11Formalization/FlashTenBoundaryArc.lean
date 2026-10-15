import N11Formalization.FlashTenBoundaryAnalytic

/-!
# C450 解析 consumer（第三层）：弧积分的**单区间闭式**

把源文 §3 的"单盘贡献闭式"
`(1/2)∫_{弧} W = a_0 t + Σ_{k=1..3} a_k sin(kt)cos(kφ)/k`
拆成**可分别核查**的两块：

1. **源不等价（把全局 cos 不等式变单区间）** ——`arc_iff_mem_Icc`：
   对 `θ ∈ [φ-π, φ+π]`（即以弧心方向 `φ` 为中心的整周区间），
   `dist (angPt θ) (ρ(cos φ, sin φ)) ≤ r  ↔  θ ∈ [φ-t, φ+t]`，
   其中 `t` 由 `cos t = (1+ρ²-r²)/(2ρ)`、`t ∈ [0,π]` 定义。
   * **wrap（跨 0）**：被 `|θ-φ| ≤ π` 排除（区间取在弧心两侧各 π，绕圈最多一次）；
   * **`t = π`（整圆/满盘）**：`[φ-t, φ+t]` 此时就是整个 `[φ-π, φ+π]`，同一式统一处理；
   * **退化 `t = 0`**：`[φ-π, φ+π]` 中只有 `θ = φ` 满足，即单点弧。
2. **三角多项式在单区间上的积分闭式** ——`integral_trigDensity_Icc`：
   `∫ θ in (φ-t)..(φ+t), W.toFun θ = 2(a_0 t + a_1 sin t cos φ + a_2 sin(2t)cos(2φ)/2 + a_3 sin(3t)cos(3φ)/3)`。
   （源文"弧积分除以 2"= 本式左端的一半。）

**与源文变量对应**：`ρ` = 环盘中心模 `ρ_i`；`φ` = 环盘角 `φ_i`；`r` = `R = 19/50`；
`t` = 环盘在 `∂D` 上的半宽；`W` = `W0`（外圆）或 `W1`（内圆）。

**与 L1（`circle_integral_le_sum_arc_integrals`）的接口**：L1 的弧积分是
`∫ θ in 0..2π, (if dist (γ θ) (c i) ≤ r then W θ else 0)`，而本文件的闭式在**以 φ 为中心的
整周区间** `[φ-π, φ+π]` 上成立；两者的桥是 2π-周期函数的平移不变性
（`Function.Periodic.intervalIntegral_add_eq`，见 `arcIntegral_eq_Icc`），
故**不需要**处理 `[0,2π]` 上的 wrap：wrap 只出现在"把中心区间搬回 `[0,2π]`"这一步之外的地方。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

open scoped Interval
open MeasureTheory

section

/-! ## 1. `cos` 的单区间判别（统一处理 wrap 与 `t = π`） -/

/-- 在 `|s| ≤ π`、`t ∈ [0,π]` 下：`cos t ≤ cos s ↔ |s| ≤ t`。

`t = π` 时右端对一切 `s` 成立（`[φ-t,φ+t]` = 整周）；`t = 0` 时只有 `s = 0`。 -/
theorem cos_t_le_cos_iff_abs_le {s t : ℝ} (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi)
    (hs : |s| ≤ Real.pi) : Real.cos t ≤ Real.cos s ↔ |s| ≤ t := by
  constructor
  · intro h
    by_contra hcon
    have hcon' : t < |s| := not_le.mp hcon
    have hlt : Real.cos |s| < Real.cos t := Real.cos_lt_cos_of_nonneg_of_le_pi ht0 hs hcon'
    rw [Real.cos_abs] at hlt
    linarith
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · have hlt' : Real.cos t < Real.cos |s| :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg s) htπ hlt
      rw [Real.cos_abs] at hlt'
      linarith
    · rw [← heq, Real.cos_abs]

/-! ## 2. 距离 → 余弦（源 §3 第一步） -/

theorem dist_angPt_sq (ρ φ θ : ℝ) :
    dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ^ 2
      = 1 + ρ ^ 2 - 2 * ρ * Real.cos (θ - φ) := by
  have h1 : dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ^ 2
      = (Real.cos θ - ρ * Real.cos φ) ^ 2 + (Real.sin θ - ρ * Real.sin φ) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [angPt]
    rw [Real.sq_sqrt (by positivity)]
  rw [h1, Real.cos_sub]
  rw [show (Real.cos θ - ρ * Real.cos φ) ^ 2 + (Real.sin θ - ρ * Real.sin φ) ^ 2
      = (Real.cos θ ^ 2 + Real.sin θ ^ 2) + ρ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2)
        - 2 * ρ * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ) from by ring]
  rw [Real.cos_sq_add_sin_sq θ, Real.cos_sq_add_sin_sq φ]
  ring

/-! ## 3. 源不等价：`dist ≤ r ↔ cos t ≤ cos(θ-φ) ↔ |θ-φ| ≤ t` -/

/-- **源不等价（第一式）**：盘 `B(ρ(cos φ,sin φ), r)` 与单位圆上 `θ` 方向点的距离条件
等价于 `cos t ≤ cos(θ-φ)`（`ρ > 0`，`t` 由 `cos t = (1+ρ²-r²)/(2ρ)` 定义）。 -/
theorem dist_angPt_le_iff {ρ r φ θ t : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hcos : Real.cos t = (1 + ρ ^ 2 - r ^ 2) / (2 * ρ)) :
    dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r ↔ Real.cos t ≤ Real.cos (θ - φ) := by
  have hd0 : (0 : ℝ) ≤ dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) := dist_nonneg
  have h2ρ : 0 < 2 * ρ := by linarith
  have hsq : dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r
      ↔ dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ^ 2 ≤ r ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hd0, abs_of_nonneg hr]
  rw [hsq, dist_angPt_sq]
  rw [hcos, div_le_iff₀ h2ρ]
  constructor <;> intro h <;> linarith

/-- **源不等价（单区间形）**：对 `θ ∈ [φ-π, φ+π]`，
`dist (angPt θ) (ρ(cos φ,sin φ)) ≤ r ↔ θ ∈ [φ-t, φ+t]`。
`t = π`（整圆）与 `t = 0`（单点）都含在内。 -/
theorem arc_iff_mem_Icc {ρ r φ θ t : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) (hcos : Real.cos t = (1 + ρ ^ 2 - r ^ 2) / (2 * ρ))
    (hθ : θ ∈ Set.Icc (φ - Real.pi) (φ + Real.pi)) :
    dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r ↔ θ ∈ Set.Icc (φ - t) (φ + t) := by
  have hθ' : |θ - φ| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have h1 : dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r
      ↔ Real.cos t ≤ Real.cos (θ - φ) := dist_angPt_le_iff hρ hr hcos
  have h2 : Real.cos t ≤ Real.cos (θ - φ) ↔ |θ - φ| ≤ t :=
    cos_t_le_cos_iff_abs_le ht0 htπ hθ'
  rw [h1, h2, Set.mem_Icc, abs_le]
  constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ## 4. 三角多项式在单区间上的积分闭式 -/

/-- `W.toFun` 以 `2π` 为周期（故弧积分可用 `[φ-π, φ+π]` 上的积分表示）。 -/
theorem TrigDensity.toFun_add_two_pi (W : TrigDensity) (θ : ℝ) :
    W.toFun (θ + 2 * Real.pi) = W.toFun θ := by
  have h2 : Real.cos (2 * (θ + 2 * Real.pi)) = Real.cos (2 * θ) := by
    rw [show 2 * (θ + 2 * Real.pi) = 2 * θ + 2 * Real.pi + 2 * Real.pi from by ring,
      Real.cos_add_two_pi, Real.cos_add_two_pi]
  have h3 : Real.cos (3 * (θ + 2 * Real.pi)) = Real.cos (3 * θ) := by
    rw [show 3 * (θ + 2 * Real.pi)
        = 3 * θ + 2 * Real.pi + 2 * Real.pi + 2 * Real.pi from by ring,
      Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_add_two_pi]
  show W.a0 + W.a1 * Real.cos (θ + 2 * Real.pi) + W.a2 * Real.cos (2 * (θ + 2 * Real.pi))
      + W.a3 * Real.cos (3 * (θ + 2 * Real.pi))
      = W.a0 + W.a1 * Real.cos θ + W.a2 * Real.cos (2 * θ) + W.a3 * Real.cos (3 * θ)
  rw [Real.cos_add_two_pi, h2, h3]

/-- **弧积分的闭式**（源文 §3 的"弧积分除以 2"乘 2）：
`∫ θ in (φ-t)..(φ+t), W.toFun θ = 2(a_0 t + Σ_{k=1..3} a_k sin(kt)cos(kφ)/k)`。 -/
theorem integral_trigDensity_Icc (W : TrigDensity) (φ t : ℝ) :
    ∫ θ in (φ - t)..(φ + t), W.toFun θ
      = 2 * (W.a0 * t + W.a1 * Real.sin t * Real.cos φ
          + W.a2 * Real.sin (2 * t) * Real.cos (2 * φ) / 2
          + W.a3 * Real.sin (3 * t) * Real.cos (3 * φ) / 3) := by
  have hderiv : ∀ x ∈ Set.uIcc (φ - t) (φ + t),
      HasDerivAt (fun θ : ℝ => W.a0 * θ + W.a1 * Real.sin θ
          + (W.a2 / 2) * Real.sin (2 * θ) + (W.a3 / 3) * Real.sin (3 * θ))
        (W.toFun x) x := by
    intro x _
    have d0 : HasDerivAt (fun θ : ℝ => W.a0 * θ) W.a0 x := by
      simpa using (hasDerivAt_id x).const_mul W.a0
    have d1 : HasDerivAt (fun θ : ℝ => W.a1 * Real.sin θ) (W.a1 * Real.cos x) x :=
      (Real.hasDerivAt_sin x).const_mul W.a1
    have d2 : HasDerivAt (fun θ : ℝ => (W.a2 / 2) * Real.sin (2 * θ))
        ((W.a2 / 2) * (Real.cos (2 * x) * 2)) x :=
      ((Real.hasDerivAt_sin (2 * x)).comp x
        (by simpa using (hasDerivAt_id x).const_mul (2 : ℝ))).const_mul (W.a2 / 2)
    have d3 : HasDerivAt (fun θ : ℝ => (W.a3 / 3) * Real.sin (3 * θ))
        ((W.a3 / 3) * (Real.cos (3 * x) * 3)) x :=
      ((Real.hasDerivAt_sin (3 * x)).comp x
        (by simpa using (hasDerivAt_id x).const_mul (3 : ℝ))).const_mul (W.a3 / 3)
    have hfun : ((fun θ : ℝ => W.a0 * θ) + (fun θ : ℝ => W.a1 * Real.sin θ)
          + (fun θ : ℝ => (W.a2 / 2) * Real.sin (2 * θ))
          + (fun θ : ℝ => (W.a3 / 3) * Real.sin (3 * θ)))
        = fun θ : ℝ => W.a0 * θ + W.a1 * Real.sin θ
            + (W.a2 / 2) * Real.sin (2 * θ) + (W.a3 / 3) * Real.sin (3 * θ) := rfl
    have hval : W.a0 + W.a1 * Real.cos x + (W.a2 / 2) * (Real.cos (2 * x) * 2)
          + (W.a3 / 3) * (Real.cos (3 * x) * 3) = W.toFun x := by
      simp only [TrigDensity.toFun]
      ring
    have total := ((d0.add d1).add d2).add d3
    rw [hfun, hval] at total
    exact total
  have hint : IntervalIntegrable W.toFun volume (φ - t) (φ + t) :=
    W.continuous_toFun.intervalIntegrable (μ := volume) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [show (2:ℝ) * (φ + t) = 2 * φ + 2 * t from by ring,
      show (2:ℝ) * (φ - t) = 2 * φ - 2 * t from by ring,
      show (3:ℝ) * (φ + t) = 3 * φ + 3 * t from by ring,
      show (3:ℝ) * (φ - t) = 3 * φ - 3 * t from by ring]
  simp only [Real.sin_add, Real.sin_sub]
  ring

end

end N11Formalization
