/-
  N11Formalization.Interval.Shift
  ===============================

  **M5b / R2：移位选择引理（单独成件，可独立复用与复核）**

  `∀ q : ℚ, |q| ≤ 10 → ∃ k : ℤ, |q − k·(π/2)| ≤ 1`。

  构造（全用 20 位 π 下界 `piLo`）：
  * `d := q − 1`；定位量 `shiftPad q := 2d/piLo + 1/8`；`k := ⌊shiftPad q⌋ + 1`。
  * 只要 `2d/π ≤ shiftPad q`（即 `d ≥ 0` 时用 `piLo ≤ π`；`d < 0` 时用
    π 的 20 位夹逼把误差 `2|d|(π−piLo)/(π·piLo) ≈ 10⁻¹⁹` 吃掉），
    就有 `k > shiftPad q ≥ 2d/π` 与 `k ≤ shiftPad q + 1`，配合 `(9/8)·(π/2) < 2`
    （即 `π < 32/9`，由 20 位界给出）得 `|q − k·(π/2)| ≤ 1`。

  **为什么取 `|q| ≤ 10`**：源构型里 `sin/cos` 的参数只有
  `angleVec u k ∈ [0, π]`（且 `Σ_k a_k = π`）与 `thetaOf … ∈ [−π, π]`
  （`θ_4 = 0`，递推 `θ_{k+1} − θ_k = a_k + a_{k+1}`，部分和绝对值 ≤ π），
  故 `|参数| ≤ 4 < 10`。这是**实用充分条件**，不是本质限制；
  一般 `q` 的版本只需把常数 `1/8` 换成随 `|q−1|` 线性增长的项
  （见 `INTERVAL-GAPS.md` §3.1 的 R2 注记）。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval`。
-/
import Mathlib
import N11Formalization.Interval.Trig

namespace N11Formalization

namespace RatInterval

/-! ## 1. 数值准备（全部来自 20 位 π 夹逼） -/

theorem piHi_sub_piLo : piHi - piLo = 1 / 10 ^ 20 := by norm_num [piHi, piLo]

theorem three_lt_pi : (3 : ℝ) < Real.pi := Real.pi_gt_three

theorem three_le_pi : (3 : ℝ) ≤ Real.pi := le_of_lt three_lt_pi

theorem pi_pos' : (0 : ℝ) < Real.pi := lt_trans (by norm_num) three_lt_pi

theorem three_le_piLo : (3 : ℝ) ≤ ((piLo : ℚ) : ℝ) := by norm_num [piLo]

theorem piLo_pos : (0 : ℝ) < ((piLo : ℚ) : ℝ) := lt_of_lt_of_le (by norm_num) three_le_piLo

/-- `π − piLo ≤ 10⁻²⁰`。 -/
theorem pi_sub_piLo_le : Real.pi - ((piLo : ℚ) : ℝ) ≤ 1 / 10 ^ 20 := by
  have h := pi_lt_piHi
  have hcast : ((piHi : ℚ) : ℝ) - ((piLo : ℚ) : ℝ) = 1 / 10 ^ 20 := by
    rw [← Rat.cast_sub, piHi_sub_piLo]
    norm_num
  linarith

/-- `π < 32/9`（等价于 `(9/8)·(π/2) < 2`）。 -/
theorem pi_lt_32_9 : Real.pi < (32 : ℝ) / 9 := by
  have h := pi_lt_piHi
  have hlt : ((piHi : ℚ) : ℝ) < (32 : ℝ) / 9 := by
    have : (((32 : ℚ) / 9 : ℚ) : ℝ) = (32 : ℝ) / 9 := by push_cast; ring
    rw [← this]
    norm_num [piHi]
  linarith

/-- `(9/8)·(π/2) < 2`。 -/
theorem nine_eighth_pi_half_lt_two : 9 * Real.pi / 16 < 2 := by
  have h := pi_lt_32_9
  linarith

/-- `5π/8 < 2`（等价于 `π < 16/5`）。 -/
theorem five_pi_div_eight_lt_two : 5 * Real.pi / 8 < 2 := by
  have h : Real.pi < (16 : ℝ) / 5 := by
    have h' := pi_lt_piHi
    have hlt : ((piHi : ℚ) : ℝ) < (16 : ℝ) / 5 := by
      have : (((16 : ℚ) / 5 : ℚ) : ℝ) = (16 : ℝ) / 5 := by push_cast; ring
      rw [← this]
      norm_num [piHi]
    linarith
  linarith

/-! ## 2. 定位量与移位选择 -/

/-- 定位量（ℚ）：`2(q−1)/piLo + 1/8`。 -/
def shiftPad (q : ℚ) : ℚ := 2 * (q - 1) / piLo + 1 / 8

/-- **关键不等式**：`2d/π ≤ 2d/piLo + 1/8`（`|q| ≤ 10`）。 -/
theorem shiftPad_key {d : ℝ} (hd : |d| ≤ 11) :
    2 * d / Real.pi ≤ 2 * d / ((piLo : ℚ) : ℝ) + 1 / 8 := by
  have hpi : (0 : ℝ) < Real.pi := pi_pos'
  have hlo : (0 : ℝ) < ((piLo : ℚ) : ℝ) := piLo_pos
  have hden : (0 : ℝ) < Real.pi * ((piLo : ℚ) : ℝ) := mul_pos hpi hlo
  have hdiff : 2 * d / ((piLo : ℚ) : ℝ) + 1 / 8 - 2 * d / Real.pi
      = (2 * d * (Real.pi - ((piLo : ℚ) : ℝ)) + (1 / 8) * (Real.pi * ((piLo : ℚ) : ℝ)))
          / (Real.pi * ((piLo : ℚ) : ℝ)) := by
    field_simp
    ring
  have hnonneg : 0 ≤ 2 * d * (Real.pi - ((piLo : ℚ) : ℝ))
      + (1 / 8) * (Real.pi * ((piLo : ℚ) : ℝ)) := by
    have hpp : (0 : ℝ) ≤ Real.pi - ((piLo : ℚ) : ℝ) := sub_nonneg.mpr (le_of_lt piLo_lt_pi)
    -- `2d(π − piLo) ≥ -2|d|(π − piLo)`
    have h1 : -2 * |d| * (Real.pi - ((piLo : ℚ) : ℝ))
        ≤ 2 * d * (Real.pi - ((piLo : ℚ) : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_right (neg_abs_le d) hpp
      nlinarith [hm]
    have h2 : 2 * |d| * (Real.pi - ((piLo : ℚ) : ℝ))
        ≤ (1 / 8) * (Real.pi * ((piLo : ℚ) : ℝ)) := by
      have hm : 2 * |d| * (Real.pi - ((piLo : ℚ) : ℝ)) ≤ 2 * 11 * (1 / 10 ^ 20) := by
        nlinarith [hd, hpp, pi_sub_piLo_le]
      have hnum : 2 * 11 * (1 / 10 ^ 20 : ℝ) ≤ (1 / 8) * (Real.pi * ((piLo : ℚ) : ℝ)) := by
        nlinarith [three_le_pi, three_le_piLo]
      linarith
    linarith [h1, h2]
  have := div_nonneg hnonneg hden.le
  linarith [hdiff, this]

/-- **关键不等式（上界侧）**：`2d/piLo + 1/8 ≤ 2d/π + 1/4`（`|d| ≤ 11`）。
（`d ≥ 0` 时差为 `2d(π−piLo)/(π·piLo) ≈ 10⁻¹⁹ ≤ 1/8`；`d < 0` 时差为负。） -/
theorem shiftPad_le_key {d : ℝ} (hd : |d| ≤ 11) :
    2 * d / ((piLo : ℚ) : ℝ) + 1 / 8 ≤ 2 * d / Real.pi + 1 / 4 := by
  have hpi : (0 : ℝ) < Real.pi := pi_pos'
  have hlo : (0 : ℝ) < ((piLo : ℚ) : ℝ) := piLo_pos
  have hden : (0 : ℝ) < Real.pi * ((piLo : ℚ) : ℝ) := mul_pos hpi hlo
  have hpp : (0 : ℝ) ≤ Real.pi - ((piLo : ℚ) : ℝ) := sub_nonneg.mpr (le_of_lt piLo_lt_pi)
  have hbound : 2 * d * (Real.pi - ((piLo : ℚ) : ℝ))
      ≤ (1 / 8) * (Real.pi * ((piLo : ℚ) : ℝ)) := by
    by_cases hd0 : 0 ≤ d
    · have hm : 2 * d * (Real.pi - ((piLo : ℚ) : ℝ))
          ≤ 2 * |d| * (Real.pi - ((piLo : ℚ) : ℝ)) := by
        have := mul_le_mul_of_nonneg_right (le_abs_self d) hpp
        nlinarith [this]
      have hm2 : 2 * |d| * (Real.pi - ((piLo : ℚ) : ℝ)) ≤ 2 * 11 * (1 / 10 ^ 20) := by
        nlinarith [hd, hpp, pi_sub_piLo_le]
      have hnum : 2 * 11 * (1 / 10 ^ 20 : ℝ) ≤ (1 / 8) * (Real.pi * ((piLo : ℚ) : ℝ)) := by
        nlinarith [three_le_pi, three_le_piLo]
      linarith
    · have hdneg : d < 0 := not_le.mp hd0
      nlinarith [hdneg, hpp, three_le_pi, three_le_piLo]
  have hdiff : 2 * d / ((piLo : ℚ) : ℝ) - 2 * d / Real.pi
      = (2 * d * (Real.pi - ((piLo : ℚ) : ℝ))) / (Real.pi * ((piLo : ℚ) : ℝ)) := by
    field_simp
    try ring
  have hstep : (2 * d * (Real.pi - ((piLo : ℚ) : ℝ))) / (Real.pi * ((piLo : ℚ) : ℝ)) ≤ 1 / 8 := by
    have h' := div_le_div_of_nonneg_right hbound hden.le
    have heq : ((1 / 8) * (Real.pi * ((piLo : ℚ) : ℝ))) / (Real.pi * ((piLo : ℚ) : ℝ)) = 1 / 8 := by
      field_simp
    linarith [h', heq]
  linarith [hdiff, hstep]

/-- **R2**：`|q| ≤ 10` 时存在整数 `k` 使 `|q − k·(π/2)| ≤ 1`。 -/
theorem exists_shift_halfPi (q : ℚ) (hq : |q| ≤ 10) :
    ∃ k : ℤ, |(q : ℝ) - (k : ℝ) * (Real.pi / 2)| ≤ 1 := by
  set k : ℤ := ⌊shiftPad q⌋ + 1 with hkdef
  refine ⟨k, ?_⟩
  have hpi : (0 : ℝ) < Real.pi := pi_pos'
  have hhalf : (0 : ℝ) < Real.pi / 2 := by linarith
  -- `k` 的 floor 两侧
  have hgt : ((shiftPad q : ℚ) : ℝ) < (k : ℝ) := by
    have h := Int.lt_floor_add_one (shiftPad q)
    rw [hkdef]
    push_cast
    exact_mod_cast h
  have hle : (k : ℝ) ≤ ((shiftPad q : ℚ) : ℝ) + 1 := by
    have h := Int.floor_le (shiftPad q)
    rw [hkdef]
    push_cast
    have : ((⌊shiftPad q⌋ : ℤ) : ℝ) ≤ ((shiftPad q : ℚ) : ℝ) := by exact_mod_cast h
    linarith
  -- `|q − 1| ≤ 11`
  have hd11 : |((q : ℝ) - 1)| ≤ 11 := by
    have h2 : |(q : ℝ)| ≤ 10 := by exact_mod_cast hq
    have h3 : -(10 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ 10 := abs_le.mp h2
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2]
  have hkey : 2 * ((q : ℝ) - 1) / Real.pi ≤ ((shiftPad q : ℚ) : ℝ) := by
    have hcast : ((shiftPad q : ℚ) : ℝ) = 2 * ((q : ℝ) - 1) / ((piLo : ℚ) : ℝ) + 1 / 8 := by
      rw [shiftPad]
      push_cast
      ring
    rw [hcast]
    exact shiftPad_key hd11
  have hId1 : (2 * ((q : ℝ) - 1) / Real.pi + 9 / 8) * (Real.pi / 2)
      = ((q : ℝ) - 1) + 9 * Real.pi / 16 := by
    field_simp
    try ring
  have hId2 : (2 * ((q : ℝ) - 1) / Real.pi) * (Real.pi / 2) = (q : ℝ) - 1 := by
    field_simp
    try ring
  have hhalf : (0 : ℝ) < Real.pi / 2 := by linarith [pi_pos']
  refine abs_le.mpr ⟨?_, ?_⟩
  · -- 第一合取 `−1 ≤ q − k·(π/2)`：用 `k` 的**上界**（`k ≤ shiftPad + 1 ≤ 2d/π + 5/4`）
    have hup : 2 * ((q : ℝ) - 1) / ((piLo : ℚ) : ℝ) + 1 / 8
        ≤ 2 * ((q : ℝ) - 1) / Real.pi + 1 / 4 := shiftPad_le_key hd11
    have hcastQ : ((shiftPad q : ℚ) : ℝ) = 2 * ((q : ℝ) - 1) / ((piLo : ℚ) : ℝ) + 1 / 8 := by
      rw [shiftPad]
      push_cast
      ring
    have h4 : (k : ℝ) ≤ 2 * ((q : ℝ) - 1) / Real.pi + 5 / 4 := by
      have : (k : ℝ) ≤ ((shiftPad q : ℚ) : ℝ) + 1 := hle
      linarith [this, hcastQ, hup]
    have h3 : (k : ℝ) * (Real.pi / 2)
        ≤ (2 * ((q : ℝ) - 1) / Real.pi + 5 / 4) * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_right h4 hhalf.le
    have hId3 : (2 * ((q : ℝ) - 1) / Real.pi + 5 / 4) * (Real.pi / 2)
        = ((q : ℝ) - 1) + 5 * Real.pi / 8 := by
      field_simp
      try ring
    rw [hId3] at h3
    have h5 := five_pi_div_eight_lt_two
    linarith
  · -- 第二合取 `q − k·(π/2) ≤ 1`：用 `k` 的**下界**（`k > shiftPad ≥ 2d/π`）
    have h1 : 2 * ((q : ℝ) - 1) / Real.pi < (k : ℝ) := lt_of_le_of_lt hkey hgt
    have h2 : (2 * ((q : ℝ) - 1) / Real.pi) * (Real.pi / 2) < (k : ℝ) * (Real.pi / 2) :=
      mul_lt_mul_of_pos_right h1 hhalf
    rw [hId2] at h2
    linarith

end RatInterval

end N11Formalization

