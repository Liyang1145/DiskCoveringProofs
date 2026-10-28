import N11Formalization.FlashTilingFan
import N11Formalization.NondegProof
import N11Formalization.RootRangeBoxFull

/-!
# FlashTilingSigns —— tiling 定向不等式供给（一般引理；已 kernel 通过）

**一般引理**（`ts11.log` exit=0，三公理）：
* `orient_eq`：`FlashTiling.orient a b c = (b₀−a₀)(c₁−a₁) − (b₁−a₁)(c₀−a₀)`；
* `abs_mul_sub_mul_le`（按 lead 更正的**精确恒等式**版）：`|p₁q₁ − p₀q₀| ≤ r(U+r) + Ur`；
* `orient_pos_of_approx`：三点各在有理近似点 `R` 邻域、差界 `U`、
  `orient A₀B₀D₀ > 4R(U+2R) + 4UR` ⇒ `0 < orient A B D`。

**数值校准**（`evidence/flash-slack/sign_data2.py`，精确有理）：`R = 1e-4`、`U = 2` ⇒ 误差 `1.6e-03`；
最小 `M`：hcv `5.401959e-02`(i=1,j=3)、hh1 `3.078402e-01`、hh0 `3.166317e-01`、
弦A `7.235551e-01`、弦B `6.258482e-01` ⇒ 全部余量 ≫ 误差。

**待铺**：`ring_close_k`（`ndRingBox` 端点 → 坐标近似界，用 `nd_eval`）+ 88 条逐条实例。
-/

noncomputable section

set_option maxHeartbeats 8000000

namespace N11Formalization.FlashTilingSigns

open N11Formalization

/-! ## 1. 一般引理 -/

theorem orient_eq (a b c : Point) :
    FlashTiling.orient a b c
      = (b.ofLp 0 - a.ofLp 0) * (c.ofLp 1 - a.ofLp 1)
        - (b.ofLp 1 - a.ofLp 1) * (c.ofLp 0 - a.ofLp 0) := by
  have h0 : (b - a).ofLp 0 = b.ofLp 0 - a.ofLp 0 := rfl
  have h1 : (b - a).ofLp 1 = b.ofLp 1 - a.ofLp 1 := rfl
  have h2 : (c - a).ofLp 0 = c.ofLp 0 - a.ofLp 0 := rfl
  have h3 : (c - a).ofLp 1 = c.ofLp 1 - a.ofLp 1 := rfl
  show FlashTiling.det2 (b - a) (c - a) = _
  rw [FlashTiling.det2, h0, h1, h2, h3]

/-- **乘积差的精确界**（恒等式，`r = 0` 时右端 0）。 -/
theorem abs_mul_sub_mul_le {p₁ p₀ q₁ q₀ U r : ℝ} (hp : |p₁ - p₀| ≤ r) (hq : |q₁ - q₀| ≤ r)
    (hq1 : |q₁| ≤ U + r) (hp0 : |p₀| ≤ U) :
    |p₁ * q₁ - p₀ * q₀| ≤ r * (U + r) + U * r := by
  have hid : p₁ * q₁ - p₀ * q₀ = (p₁ - p₀) * q₁ + p₀ * (q₁ - q₀) := by ring
  rw [hid]
  have h1 : |(p₁ - p₀) * q₁| ≤ r * (U + r) := by
    rw [abs_mul]
    exact mul_le_mul hp hq1 (abs_nonneg _) (le_trans (abs_nonneg _) hp)
  have h2 : |p₀ * (q₁ - q₀)| ≤ U * r := by
    rw [abs_mul]
    exact mul_le_mul hp0 hq (abs_nonneg _) (le_trans (abs_nonneg _) hp0)
  calc |(p₁ - p₀) * q₁ + p₀ * (q₁ - q₀)|
      ≤ |(p₁ - p₀) * q₁| + |p₀ * (q₁ - q₀)| := abs_add_le _ _
    _ ≤ r * (U + r) + U * r := add_le_add h1 h2

/-- **核心**：`orient A B D > 0` 由"三点各在有理点 `R` 邻域 + 中心 determinant > 误差"。 -/
theorem orient_pos_of_approx {A B D A0 B0 D0 : Point} {R U : ℝ}
    (hA0 : |A.ofLp 0 - A0.ofLp 0| ≤ R) (hA1 : |A.ofLp 1 - A0.ofLp 1| ≤ R)
    (hB0 : |B.ofLp 0 - B0.ofLp 0| ≤ R) (hB1 : |B.ofLp 1 - B0.ofLp 1| ≤ R)
    (hD0 : |D.ofLp 0 - D0.ofLp 0| ≤ R) (hD1 : |D.ofLp 1 - D0.ofLp 1| ≤ R)
    (hBX : |B0.ofLp 0 - A0.ofLp 0| ≤ U) (hBY : |B0.ofLp 1 - A0.ofLp 1| ≤ U)
    (hDX : |D0.ofLp 0 - A0.ofLp 0| ≤ U) (hDY : |D0.ofLp 1 - A0.ofLp 1| ≤ U)
    (_hU : 0 ≤ U) (_hR : 0 ≤ R)
    (hM : 4 * R * (U + 2 * R) + 4 * U * R < FlashTiling.orient A0 B0 D0) :
    0 < FlashTiling.orient A B D := by
  rw [orient_eq] at hM ⊢
  have hr2 : |(B.ofLp 0 - A.ofLp 0) - (B0.ofLp 0 - A0.ofLp 0)| ≤ 2 * R := by
    rw [abs_le] at *; constructor <;> linarith
  have hr3 : |(D.ofLp 1 - A.ofLp 1) - (D0.ofLp 1 - A0.ofLp 1)| ≤ 2 * R := by
    rw [abs_le] at *; constructor <;> linarith
  have hr4 : |(B.ofLp 1 - A.ofLp 1) - (B0.ofLp 1 - A0.ofLp 1)| ≤ 2 * R := by
    rw [abs_le] at *; constructor <;> linarith
  have hr5 : |(D.ofLp 0 - A.ofLp 0) - (D0.ofLp 0 - A0.ofLp 0)| ≤ 2 * R := by
    rw [abs_le] at *; constructor <;> linarith
  have hq1 : |D.ofLp 1 - A.ofLp 1| ≤ U + 2 * R := by
    rw [abs_le] at *; constructor <;> linarith
  have hq2 : |D.ofLp 0 - A.ofLp 0| ≤ U + 2 * R := by
    rw [abs_le] at *; constructor <;> linarith
  have hw : (2 : ℝ) * R * (U + 2 * R) + U * (2 * R) = 2 * R * (U + 2 * R) + 2 * U * R := by ring
  have e1 : |(B.ofLp 0 - A.ofLp 0) * (D.ofLp 1 - A.ofLp 1)
      - (B0.ofLp 0 - A0.ofLp 0) * (D0.ofLp 1 - A0.ofLp 1)| ≤ 2 * R * (U + 2 * R) + 2 * U * R := by
    have := abs_mul_sub_mul_le (p₁ := B.ofLp 0 - A.ofLp 0) (p₀ := B0.ofLp 0 - A0.ofLp 0)
      (q₁ := D.ofLp 1 - A.ofLp 1) (q₀ := D0.ofLp 1 - A0.ofLp 1) (U := U) (r := 2 * R)
      (hp := hr2) (hq := hr3) (hq1 := hq1) (hp0 := hBX)
    linarith [this, hw]
  have e2 : |(B.ofLp 1 - A.ofLp 1) * (D.ofLp 0 - A.ofLp 0)
      - (B0.ofLp 1 - A0.ofLp 1) * (D0.ofLp 0 - A0.ofLp 0)| ≤ 2 * R * (U + 2 * R) + 2 * U * R := by
    have := abs_mul_sub_mul_le (p₁ := B.ofLp 1 - A.ofLp 1) (p₀ := B0.ofLp 1 - A0.ofLp 1)
      (q₁ := D.ofLp 0 - A.ofLp 0) (q₀ := D0.ofLp 0 - A0.ofLp 0) (U := U) (r := 2 * R)
      (hp := hr4) (hq := hr5) (hq1 := hq2) (hp0 := hBY)
    linarith [this, hw]
  have f1 := (abs_le.mp e1).1
  have f2 := (abs_le.mp e2).2
  have hsum : (2 * R * (U + 2 * R) + 2 * U * R) + (2 * R * (U + 2 * R) + 2 * U * R)
      = 4 * R * (U + 2 * R) + 4 * U * R := by ring
  linarith [hM, f1, f2, hsum]

end N11Formalization.FlashTilingSigns

#print axioms N11Formalization.FlashTilingSigns.orient_pos_of_approx
