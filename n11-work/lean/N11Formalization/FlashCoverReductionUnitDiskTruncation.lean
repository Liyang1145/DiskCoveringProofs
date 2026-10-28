/-
# FlashCoverReductionUnitDiskTruncation — `X ∈ unitDisk` 对平分线参数的截线区间

作者：flash-cover-reduction。写域：`lean/N11Formalization/FlashCoverReduction*.lean`。
**前置（已冻结）**：`FlashCoverReductionBlockerGeometry.lean`
（§6 单竞争者差式、§7 多竞争者 1D Helly、§8 受限 Voronoi 透镜见证判据）。

## 本文件补上 lead 指出的缺失项 (i)：`X ∈ unitDisk`

§8 的判据只给"等距 + `‖X−A‖ ≤ r` + `A` 不弱于所有竞争者"，**不含** `X ∈ unitDisk`。
在平分线参数 `X = M + τ•u` 下，`X ∈ unitDisk` 等价于
```
‖M + τ•u‖² ≤ 1   ⟺   (τ + ⟪M,u⟫)² ≤ 1 + ⟪M,u⟫² − ‖M‖² =: D
```
即 τ 轴上的**截线区间** `[−⟪M,u⟫ − √D, −⟪M,u⟫ + √D]`（`D ≥ 0` 时；否则为空）。
于是"§8 判据 ∩ unitDisk"仍是**区间交**，§7 的 1D Helly 可直接追加这条区间。

**声明**：本文件只是欧氏二次式恒等式与区间表示；不断言覆盖/弦/图事实。
-/

import Mathlib
import N11Formalization.Definitions

namespace N11Formalization

open scoped RealInnerProductSpace

/-- `‖M + τ•u‖²` 沿直线的展开（`‖u‖ = 1`）：
`= τ² + 2τ⟪M,u⟫ + ‖M‖²`。 -/
theorem norm_sq_along_line {M u : Point} {τ : ℝ} (hu1 : ‖u‖ = 1) :
    ‖M + τ • u‖ ^ 2 = τ ^ 2 + 2 * τ * (inner ℝ M u : ℝ) + ‖M‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, hu1, mul_one,
    Real.norm_eq_abs, sq_abs]
  ring

/-- 圆盘条件等价于 τ 的**二次不等式**（配方形式）。 -/
theorem unitDisk_tau_iff {M u : Point} {τ : ℝ} (hu1 : ‖u‖ = 1) :
    ‖M + τ • u‖ ≤ 1 ↔ (τ + (inner ℝ M u : ℝ)) ^ 2 ≤ 1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2 := by
  have hsq := norm_sq_along_line (M := M) (u := u) (τ := τ) hu1
  have hnn : (0 : ℝ) ≤ ‖M + τ • u‖ := norm_nonneg _
  constructor
  · intro h
    have h1 : ‖M + τ • u‖ ^ 2 ≤ 1 := by nlinarith
    rw [hsq] at h1
    nlinarith
  · intro h
    have h1 : ‖M + τ • u‖ ^ 2 ≤ 1 := by rw [hsq]; nlinarith
    nlinarith

/-- 截线区间下界。 -/
noncomputable def diskLo (M u : Point) : ℝ :=
  -(inner ℝ M u : ℝ) - Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2)

/-- 截线区间上界。 -/
noncomputable def diskHi (M u : Point) : ℝ :=
  -(inner ℝ M u : ℝ) + Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2)

/-- 判别式 `D = 1 + ⟪M,u⟫² − ‖M‖²`。 -/
noncomputable def diskD (M u : Point) : ℝ := 1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2

/-- **截线区间**（`D = 1 + ⟪M,u⟫² − ‖M‖² ≥ 0` 时）：
`X = M + τ•u ∈ unitDisk ⟺ τ ∈ [diskLo, diskHi]`。 -/
theorem unitDisk_tau_interval {M u : Point} {τ : ℝ} (hu1 : ‖u‖ = 1)
    (hD : 0 ≤ 1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2) :
    ‖M + τ • u‖ ≤ 1 ↔ diskLo M u ≤ τ ∧ τ ≤ diskHi M u := by
  rw [unitDisk_tau_iff hu1]
  have hsq : Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2) ^ 2
      = 1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2 := Real.sq_sqrt hD
  have h0 : (0 : ℝ) ≤ Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2) := Real.sqrt_nonneg _
  simp only [diskLo, diskHi]
  constructor
  · intro h
    have h1 : (τ + (inner ℝ M u : ℝ)) ^ 2
        ≤ (Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2)) ^ 2 := by
      rw [hsq]; exact h
    have h2 : |τ + (inner ℝ M u : ℝ)| ≤ Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2) := by
      have := sq_le_sq.mp h1
      rwa [abs_of_nonneg h0] at this
    have h3 := abs_le.mp h2
    constructor <;> linarith [h3.1, h3.2]
  · rintro ⟨h1, h2⟩
    have hb : -(Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2)) ≤ τ + (inner ℝ M u : ℝ)
        ∧ τ + (inner ℝ M u : ℝ) ≤ Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2) := by
      constructor <;> linarith
    have h3 : |τ + (inner ℝ M u : ℝ)| ≤ Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2) :=
      abs_le.mpr hb
    have h4 : (τ + (inner ℝ M u : ℝ)) ^ 2
        ≤ (Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2)) ^ 2 := by
      have h5 : |τ + (inner ℝ M u : ℝ)|
          ≤ |Real.sqrt (1 + (inner ℝ M u : ℝ) ^ 2 - ‖M‖ ^ 2)| := by
        rwa [abs_of_nonneg h0]
      simpa [sq_abs] using sq_le_sq.mpr h5
    rw [hsq] at h4
    exact h4

/-- **直线与单位圆盘相交 ⟺ `D ≥ 0`**（即原点到直线的距离 ≤ 1）。 -/
theorem unitDisk_tau_nonempty_iff {M u : Point} (hu1 : ‖u‖ = 1) :
    (∃ τ : ℝ, ‖M + τ • u‖ ≤ 1) ↔ 0 ≤ diskD M u := by
  constructor
  · rintro ⟨τ, hτ⟩
    have h := (unitDisk_tau_iff hu1).mp hτ
    have h2 : (0 : ℝ) ≤ (τ + (inner ℝ M u : ℝ)) ^ 2 := sq_nonneg _
    simp only [diskD]
    linarith
  · intro hD
    refine ⟨-(inner ℝ M u : ℝ), ?_⟩
    rw [unitDisk_tau_iff hu1]
    simp only [diskD] at hD
    simpa using hD

end N11Formalization
