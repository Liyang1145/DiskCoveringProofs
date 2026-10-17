import N11Formalization.FlashTenBoundaryScale

/-!
# C450 第 1 段 consumer 桥（①–③ 的基础引理）

源证书以 `t ∈ [0, arcsin R]`（最大角参数）与**两个根分支** `ρ = cos t ± √(R² - sin²t)`
参数化环盘；本件把"真实环盘的中心模 `ρ`、方向 `v = cos φ`"与源变量对上：

* `halfwidth_cos`：若 `ρ = cos t ± √(R² − sin²t)`（`t ∈ [0,π]`），则
  `(1 + ρ² − R²)/(2ρ) = cos t`（即 `t` **就是**弧半宽，源 §3 的 `t` 与我的 clamp 里的
  `arccos((1+ρ²−(r/q)²)/(2ρ))` 一致）；
* `halfwidth_arccos`：于是 `arccos((1+ρ²−R²)/(2ρ)) = t`（`t ∈ [0,π]`）；
* **`exists_t_sign_of_rho`**（Lead 强调的"两分支完整覆盖"）：对任意 `ρ ∈ [1−R, 1+R]`
  **存在** `t ∈ [0, arcsin R]` 与符号 `s`，使 `ρ = cos t + s·√(R² − sin²t)`；
* `sqrt_one_sub_cos_sq`：`√(1 − cos²φ) = |sin φ|`（`v`-形与角度形的对接，源证书以 `v` 为自由变量）。

这些是 `C450Seg1Data`（源变量形）与 clamp 闭式（几何变量形）之间**必须**先付的桥；
**在它们过内核之前，接口仍有实质 gap**（不把它说成"一步之遥"）。
-/

namespace N11Formalization

set_option maxHeartbeats 1000000

open scoped Interval
open MeasureTheory

section

/-- `R = 19/50` 在 `(0,1)` 内（后续用）。 -/
theorem R_pos : (0 : ℝ) < 19 / 50 := by norm_num

theorem R_lt_one : (19 : ℝ) / 50 < 1 := by norm_num

/-- **半宽恒等式**：`ρ = cos t ± √(R² − sin²t)` ⟹ `(1+ρ²−R²)/(2ρ) = cos t`。

（代数核心：`ρ = κ ± √(R²−sin²t)` 且 `κ = cos t` ⟹ `(ρ−κ)² = R²−sin²t = R²−1+κ²`。） -/
theorem halfwidth_cos {ρ t : ℝ} (hρ : ρ ≠ 0) {s : ℝ}
    (hs : s ^ 2 = 1) (hsin : (Real.sin t) ^ 2 ≤ (19 : ℝ) ^ 2 / 50 ^ 2)
    (hroot : ρ = Real.cos t + s * Real.sqrt ((19 : ℝ) ^ 2 / 50 ^ 2 - (Real.sin t) ^ 2)) :
    (1 + ρ ^ 2 - (19 : ℝ) ^ 2 / 50 ^ 2) / (2 * ρ) = Real.cos t := by
  have hR : ((19 : ℝ) ^ 2 / 50 ^ 2) = (19 / 50) ^ 2 := by ring
  rw [hR] at hroot ⊢
  have hD : 0 ≤ (19 / 50) ^ 2 - (Real.sin t) ^ 2 := by
    rw [hR] at hsin; linarith
  have h2 : (ρ - Real.cos t) ^ 2 = (19 / 50) ^ 2 - (Real.sin t) ^ 2 := by
    rw [hroot]
    rw [show Real.cos t + s * Real.sqrt ((19 / 50) ^ 2 - (Real.sin t) ^ 2) - Real.cos t
        = s * Real.sqrt ((19 / 50) ^ 2 - (Real.sin t) ^ 2) from by ring]
    rw [mul_pow, hs, one_mul, Real.sq_sqrt hD]
  field_simp
  nlinarith [h2, Real.sin_sq t, sq_nonneg (Real.sin t)]

/-- **半宽 = `arccos` 形**：把上一式套上 `arccos`（`t ∈ [0,π]`），得到 clamp 里出现的那个量。 -/
theorem halfwidth_arccos {ρ t : ℝ} (hρ : ρ ≠ 0) {s : ℝ} (hs : s ^ 2 = 1)
    (hsin : (Real.sin t) ^ 2 ≤ (19 : ℝ) ^ 2 / 50 ^ 2) (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi)
    (hroot : ρ = Real.cos t + s * Real.sqrt ((19 : ℝ) ^ 2 / 50 ^ 2 - (Real.sin t) ^ 2)) :
    Real.arccos ((1 + ρ ^ 2 - (19 : ℝ) ^ 2 / 50 ^ 2) / (2 * ρ)) = t := by
  rw [halfwidth_cos hρ hs hsin hroot]
  exact Real.arccos_cos ht0 htπ

/-- **两分支完整覆盖**（Lead 强调）：对任意 ρ ∈ [1−R, 1+R]，存在 	 ∈ [0, arcsin R]
使 ρ 等于 cos t ± √(R² − sin²t) 之一（符号由 ρ - cos t 的符号决定）。

证明：取 	 := arccos((1+ρ²−R²)/(2ρ))；由 AM-GM
(ρ + (1−R²)/ρ)/2 ≥ √(1−R²) = cos(arcsin R) 与 rccos 反单调得 	 ≤ arcsin R；
再由 (ρ−cos t)² = R² − sin²t 取 √· 得 √(R²−sin²t) = |ρ−cos t|。 -/
theorem exists_t_of_rho {ρ : ℝ} (hρ1 : 1 - 19 / 50 ≤ ρ) (hρ2 : ρ ≤ 1 + 19 / 50) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ Real.arcsin (19 / 50) ∧ t ∈ Set.Icc 0 Real.pi ∧
      (ρ = Real.cos t + Real.sqrt ((19 / 50) ^ 2 - (Real.sin t) ^ 2)
        ∨ ρ = Real.cos t - Real.sqrt ((19 / 50) ^ 2 - (Real.sin t) ^ 2)) := by
  have hρpos : 0 < ρ := by linarith [R_pos, R_lt_one]
  set κ : ℝ := (1 + ρ ^ 2 - (19 / 50) ^ 2) / (2 * ρ) with hκ
  have hsqrt1R : Real.cos (Real.arcsin (19 / 50)) = Real.sqrt (1 - (19 / 50) ^ 2) :=
    Real.cos_arcsin (19 / 50)
  have hAM : Real.sqrt (1 - (19 / 50) ^ 2) ≤ κ := by
    have hρ' : 0 < 2 * ρ := by linarith
    rw [hκ, le_div_iff₀ hρ']
    have hs1 : Real.sqrt (1 - (19/50)^2) * (2 * ρ) ≤ 1 + ρ ^ 2 - (19/50)^2 := by
      nlinarith [sq_nonneg (ρ - Real.sqrt (1 - (19/50)^2)),
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1 - (19/50)^2),
        Real.sqrt_nonneg (1 - (19/50)^2)]
    linarith
  refine ⟨Real.arccos κ, Real.arccos_nonneg κ, ?_, ⟨Real.arccos_nonneg κ, Real.arccos_le_pi κ⟩, ?_⟩
  · have h := Real.arccos_le_arccos hAM
    rw [← hsqrt1R] at h
    rwa [Real.arccos_cos
      (le_trans (Real.arcsin_nonneg.mpr (by norm_num : (0:ℝ) ≤ 19 / 50))
        (by linarith [Real.pi_pos]))
      (le_trans (Real.arcsin_le_pi_div_two (19 / 50)) (by linarith [Real.pi_pos]))] at h
  · have hcos : Real.cos (Real.arccos κ) = κ :=
      Real.cos_arccos (by
        rw [hκ]
        have h2ρ : 0 < 2 * ρ := by linarith
        rw [le_div_iff₀ h2ρ]
        nlinarith [R_pos, hρ1, hρ2, sq_nonneg (ρ - 1)])
        (by
        rw [hκ]
        have h2ρ : 0 < 2 * ρ := by linarith
        rw [div_le_iff₀ h2ρ]
        nlinarith [R_pos, hρ1, hρ2, sq_nonneg (ρ + 1)])
    have hkey : (ρ - κ) ^ 2 = (19 / 50) ^ 2 - (Real.sin (Real.arccos κ)) ^ 2 := by
      have hsin : (Real.sin (Real.arccos κ)) ^ 2 = 1 - κ ^ 2 := by
        rw [Real.sin_sq, hcos]
      rw [hsin, hκ]
      field_simp
      ring
    have hsqrt : Real.sqrt ((19 / 50) ^ 2 - (Real.sin (Real.arccos κ)) ^ 2) = |ρ - κ| := by
      rw [← hkey, Real.sqrt_sq_eq_abs]
    by_cases hsgn : 0 ≤ ρ - κ
    · left
      rw [hsqrt, abs_of_nonneg hsgn, hcos]
      ring
    · right
      rw [hsqrt, abs_of_neg (not_le.mp hsgn), hcos]
      ring
/-- `v`-形与角度形的对接：`√(1 − cos²φ) = |sin φ|`。 -/
theorem sqrt_one_sub_cos_sq (φ : ℝ) :
    Real.sqrt (1 - Real.cos φ ^ 2) = |Real.sin φ| := by
  rw [← Real.sin_sq, Real.sqrt_sq_eq_abs]

end

end N11Formalization
