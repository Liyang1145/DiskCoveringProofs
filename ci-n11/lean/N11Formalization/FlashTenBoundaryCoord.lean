import N11Formalization.FlashTenBoundarySeg1

/-!
# C450 第 1 段 consumer：坐标形桥（①）

本件付清 Lead 指定的两条桥：

* **① 坐标形 dist 平方**：`dist (angPt θ) w ^ 2 = 1 + ‖w‖² − 2(w₀ cos θ + w₁ sin θ)`
  （任意 `w : Point`；与 Arc 层的极坐标版 `dist_angPt_sq` 同法，但中心不再是 `!₂[ρcos φ,ρsin φ]`）；
* **极坐标见证**：任意 `w ≠ 0` 存在 `φ` 使 `cos φ = w₀/‖w‖` 且 `sin φ = w₁/‖w‖`
  （`κ := w₀/‖w‖`，`φ := ±arccos κ` 按 `w₁` 的符号取号）——于是 Arc/Scale 层的"角度形"闭式
  可以套到**任意**真实盘心上，接 `C450Seg1Data` 时只需 `v = w₀/‖w‖`。

辅助：`norm_sq_coord`（`‖w‖² = w₀² + w₁²`）、`abs_coord_le_norm`（`|w₀| ≤ ‖w‖`）。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

open scoped Interval
open MeasureTheory

section

/-- `!₂` 范数的坐标分解：`‖w‖² = w₀² + w₁²`。 -/
theorem norm_sq_coord (w : Point) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt (by positivity)]

/-- 单坐标界：`|w₀| ≤ ‖w‖`（由上一式）。 -/
theorem abs_coord_le_norm (w : Point) : |w 0| ≤ ‖w‖ := by
  have h := norm_sq_coord w
  have h2 : w 0 ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [sq_nonneg (w 1)]
  calc |w 0| = Real.sqrt (w 0 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖w‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖w‖ := Real.sqrt_sq (norm_nonneg w)

theorem abs_coord_one_le_norm (w : Point) : |w 1| ≤ ‖w‖ := by
  have h := norm_sq_coord w
  have h2 : w 1 ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [sq_nonneg (w 0)]
  calc |w 1| = Real.sqrt (w 1 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖w‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖w‖ := Real.sqrt_sq (norm_nonneg w)

/-- **① 坐标形**：`dist (angPt θ) w ^ 2 = 1 + ‖w‖² − 2(w₀ cos θ + w₁ sin θ)`。 -/
theorem dist_angPt_sq_coord (w : Point) (θ : ℝ) :
    dist (angPt θ) w ^ 2 = 1 + ‖w‖ ^ 2 - 2 * (w 0 * Real.cos θ + w 1 * Real.sin θ) := by
  have h1 : dist (angPt θ) w ^ 2 = (Real.cos θ - w 0) ^ 2 + (Real.sin θ - w 1) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [angPt, Real.norm_eq_abs, sq_abs]
    rw [Real.sq_sqrt (by positivity)]
  rw [h1, norm_sq_coord w]
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- **极坐标见证**（任意非零 `w`）：存在 `φ` 使 `cos φ = w₀/‖w‖`、`sin φ = w₁/‖w‖`。

构造：`κ := w₀/‖w‖ ∈ [-1,1]`，`φ := if 0 ≤ w₁ then arccos κ else -(arccos κ)`。 -/
theorem exists_angle_of_point (w : Point) (hw : w ≠ 0) :
    ∃ φ : ℝ, Real.cos φ = w 0 / ‖w‖ ∧ Real.sin φ = w 1 / ‖w‖ := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set κ : ℝ := w 0 / ‖w‖ with hκ
  have hκ1 : κ ≤ 1 := by
    rw [hκ, div_le_one hpos]
    exact le_of_abs_le (abs_coord_le_norm w)
  have hκm1 : -1 ≤ κ := by
    rw [hκ, le_div_iff₀ hpos]
    linarith [neg_le_abs (w 0), abs_coord_le_norm w]
  have hfrac : (1:ℝ) - w 0 ^ 2 / ‖w‖ ^ 2 = (‖w‖ ^ 2 - w 0 ^ 2) / ‖w‖ ^ 2 := by
    rw [show (1:ℝ) = ‖w‖ ^ 2 / ‖w‖ ^ 2 from (div_self (ne_of_gt (pow_pos hpos 2))).symm,
      ← sub_div]
  have hnum : ‖w‖ ^ 2 - w 0 ^ 2 = w 1 ^ 2 := by
    have := norm_sq_coord w; linarith
  have hsq : 1 - κ ^ 2 = (w 1 / ‖w‖) ^ 2 := by
    rw [hκ, div_pow, hfrac, hnum]
    ring
  refine ⟨if 0 ≤ w 1 then Real.arccos κ else -(Real.arccos κ), ?_, ?_⟩
  · by_cases h : 0 ≤ w 1
    · simp only [h, if_true]
      exact Real.cos_arccos hκm1 hκ1
    · simp only [h, if_false]
      rw [Real.cos_neg]
      exact Real.cos_arccos hκm1 hκ1
  · by_cases h : 0 ≤ w 1
    · simp only [h, if_true]
      rw [Real.sin_arccos κ, hsq, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ w 1 / ‖w‖)]
    · simp only [h, if_false]
      rw [Real.sin_neg, Real.sin_arccos κ, hsq, Real.sqrt_sq_eq_abs,
        abs_of_neg (div_neg_of_neg_of_pos (not_le.mp h) hpos)]
      ring

/-! ## 3. v-形弧积分（②③）：把角度形闭式搬到任意盘心，并把 `cos kφ` 换成 `v = w₀/‖w‖` 的 Chebyshev -/

/-- 由极坐标见证重建点。 -/
theorem eq_ofLp_of_angle {w : Point} {ρ φ : ℝ} (hw : w ≠ 0) (hρ : ρ = ‖w‖)
    (hc : Real.cos φ = w 0 / ρ) (hs : Real.sin φ = w 1 / ρ) :
    (!₂[ρ * Real.cos φ, ρ * Real.sin φ] : Point) = w := by
  have hρpos : 0 < ρ := by rw [hρ]; exact norm_pos_iff.mpr hw
  have hne : ρ ≠ 0 := ne_of_gt hρpos
  ext i
  fin_cases i <;> simp [hc, hs, mul_div_cancel₀, hne]

/-- **单位圆上的 v-形弧积分**（盘心 `w`、半径 `r`；`v = w₀/‖w‖`、`cos t = (1+‖w‖²−r²)/(2‖w‖)`）。 -/
theorem arc_integral_unit_vform (W : TrigDensity) {w : Point} (hw : w ≠ 0) {r t : ℝ}
    (hr : 0 ≤ r) (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi)
    (hcos : Real.cos t = (1 + ‖w‖ ^ 2 - r ^ 2) / (2 * ‖w‖)) :
    ∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) w ≤ r then W.toFun θ else 0)
      = 2 * (W.a0 * t + W.a1 * Real.sin t * (w 0 / ‖w‖)
          + W.a2 * Real.sin (2 * t) * (2 * (w 0 / ‖w‖) ^ 2 - 1) / 2
          + W.a3 * Real.sin (3 * t) * (4 * (w 0 / ‖w‖) ^ 3 - 3 * (w 0 / ‖w‖)) / 3) := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨φ, hc, hs⟩ := exists_angle_of_point w hw
  have hwit : (!₂[‖w‖ * Real.cos φ, ‖w‖ * Real.sin φ] : Point) = w :=
    eq_ofLp_of_angle hw rfl hc hs
  have hcongr : (∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) w ≤ r then W.toFun θ else 0))
      = ∫ θ in (0)..(2 * Real.pi),
        (if dist (angPt θ) (!₂[‖w‖ * Real.cos φ, ‖w‖ * Real.sin φ]) ≤ r
          then W.toFun θ else 0) := by
    rw [hwit]
  rw [hcongr, arc_integral_interval W hpos hr ht0 htπ hcos, hc,
    cos_two_mul_of_cos hc, cos_three_mul_of_cos hc]

/-- **任意测试圆上的 v-形弧积分**（圆心 `h`、半径 `q>0`；盘心 `h + q•w`，有效 `ρ = ‖w‖`、半径 `r/q`）。 -/
theorem arc_integral_circle_vform (W : TrigDensity) (h : Point) {q : ℝ} (hq : 0 < q)
    {w : Point} (hw : w ≠ 0) {r t : ℝ} (hr : 0 ≤ r) (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi)
    (hcos : Real.cos t = (1 + ‖w‖ ^ 2 - (r / q) ^ 2) / (2 * ‖w‖)) :
    ∫ θ in (0)..(2 * Real.pi),
        (if dist (h + q • angPt θ) (h + q • w) ≤ r then W.toFun θ else 0)
      = 2 * (W.a0 * t + W.a1 * Real.sin t * (w 0 / ‖w‖)
          + W.a2 * Real.sin (2 * t) * (2 * (w 0 / ‖w‖) ^ 2 - 1) / 2
          + W.a3 * Real.sin (3 * t) * (4 * (w 0 / ‖w‖) ^ 3 - 3 * (w 0 / ‖w‖)) / 3) := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨φ, hc, hs⟩ := exists_angle_of_point w hw
  have hwit : (!₂[‖w‖ * Real.cos φ, ‖w‖ * Real.sin φ] : Point) = w :=
    eq_ofLp_of_angle hw rfl hc hs
  have hcongr : (∫ θ in (0)..(2 * Real.pi),
        (if dist (h + q • angPt θ) (h + q • w) ≤ r then W.toFun θ else 0))
      = ∫ θ in (0)..(2 * Real.pi),
        (if dist (h + q • angPt θ) (h + q • !₂[‖w‖ * Real.cos φ, ‖w‖ * Real.sin φ]) ≤ r
          then W.toFun θ else 0) := by
    rw [hwit]
  rw [hcongr, arc_integral_scale_interval W h hq hpos hr ht0 htπ hcos, hc,
    cos_two_mul_of_cos hc, cos_three_mul_of_cos hc]

end

/-! ## 4. empty 支（v-形）：`‖w‖ > 2`（即 `ℓ > 2R`）时内圆截不到弧，弧积分 = 0

与源 `c450Q` 内层 `b = if ℓ < 2R then arccos(ℓ/(2R)) else 0` 的 `else` 支一致；
边界 `‖w‖ = 2`（`ℓ = 2R`）落在 interval 支且 `t' = 0`，两者都给 0，不冲突。 -/

theorem arc_integral_circle_vform_empty (W : TrigDensity) (h : Point) {q : ℝ} (hq : 0 < q)
    {w : Point} (hw : 2 < ‖w‖) {r : ℝ} (hr : r < (‖w‖ - 1) * q) :
    ∫ θ in (0)..(2 * Real.pi),
        (if dist (h + q • angPt θ) (h + q • w) ≤ r then W.toFun θ else 0) = 0 := by
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw
    linarith
  obtain ⟨φ, hc, hs⟩ := exists_angle_of_point w hw0
  have hwit : (!₂[‖w‖ * Real.cos φ, ‖w‖ * Real.sin φ] : Point) = w :=
    eq_ofLp_of_angle hw0 rfl hc hs
  have hfun : (fun θ : ℝ =>
        (if dist (h + q • angPt θ) (h + q • w) ≤ r then W.toFun θ else 0))
      = fun θ : ℝ =>
        (if dist (h + q • angPt θ) (h + q • !₂[‖w‖ * Real.cos φ, ‖w‖ * Real.sin φ]) ≤ r
          then W.toFun θ else 0) := by
    rw [hwit]
  rw [hfun]
  have habs : |1 - ‖w‖| = ‖w‖ - 1 := by
    rw [abs_of_neg (by linarith)]
    ring
  have hempty : ∀ θ : ℝ,
      ¬ (dist (h + q • angPt θ) (h + q • !₂[‖w‖ * Real.cos φ, ‖w‖ * Real.sin φ]) ≤ r) := by
    intro θ
    rw [arc_scale hq _ θ, not_le]
    rw [hwit]
    have h1 : r / q < |1 - ‖w‖| := by
      rw [habs, div_lt_iff₀ hq]
      linarith
    have h2 : |‖angPt θ‖ - ‖w‖| ≤ dist (angPt θ) w := by
      calc |‖angPt θ‖ - ‖w‖| ≤ ‖angPt θ - w‖ := abs_norm_sub_norm_le _ _
        _ = dist (angPt θ) w := (dist_eq_norm _ _).symm
    rw [norm_angPt θ] at h2
    exact lt_of_lt_of_le h1 h2
  have hz : (fun θ : ℝ => (if dist (h + q • angPt θ)
        (h + q • !₂[‖w‖ * Real.cos φ, ‖w‖ * Real.sin φ]) ≤ r then W.toFun θ else 0))
      = fun _ : ℝ => (0 : ℝ) := by
    funext θ
    exact if_neg (hempty θ)
  rw [hz, intervalIntegral.integral_zero]

end N11Formalization
