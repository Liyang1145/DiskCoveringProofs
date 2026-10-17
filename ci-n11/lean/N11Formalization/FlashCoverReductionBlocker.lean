/-
# FlashCoverReductionBlocker — 阻断判据的 Lean 内核 + 真实 Point 范数平方恒等式消费者

作者：flash-cover-reduction。写域：`lean/N11Formalization/FlashCoverReduction*.lean`。

## 本模块要付的两件事（lead 指定的唯一义务）

**(A) 实数内核**（判据本身）：
```
∀ t c b : ℝ,  0 ≤ t  →  ( (∃ τ, |τ| ≤ t ∧ 2 * τ * b ≤ c)  ↔  0 ≤ c + 2 * t * |b| )
```
**声明**：本模块只证上述代数/内积恒等式，**不**断言任何覆盖/图/弦的事实。
-/

import Mathlib
import N11Formalization.Definitions

-- 本文件是纯代数/内积恒等式：`simp only` 中保留的候选引理清单在两条证明间共用，
-- 个别条目在某条证明里用不到；关掉该 linter 以免噪声（不影响证明内容）。
set_option linter.unusedSimpArgs false

namespace N11Formalization

/-! ## (A) 实数内核 -/

/-- **可行 τ 的存在性 ⟺ 符号式非负**（blocker 判据的内核）。

`2 τ b ≤ c` 是"A 不弱于 B"在平分线坐标下的不等式。存在 `|τ| ≤ t` 的解
当且仅当 `c + 2 t |b| ≥ 0`；**无需对 b 分类或做除法**。 -/
theorem exists_tau_mul_le_iff {t c b : ℝ} (ht : 0 ≤ t) :
    (∃ τ : ℝ, |τ| ≤ t ∧ 2 * τ * b ≤ c) ↔ 0 ≤ c + 2 * t * |b| := by
  constructor
  · rintro ⟨τ, hτ, hle⟩
    have h1 : |τ * b| ≤ t * |b| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hτ (abs_nonneg b)
    have h2 : -(t * |b|) ≤ τ * b := neg_le_of_abs_le h1
    linarith
  · intro h
    rcases lt_trichotomy b 0 with hb | hb | hb
    · refine ⟨t, ?_, ?_⟩
      · rw [abs_of_nonneg ht]
      · rw [abs_of_neg hb] at h
        linarith
    · refine ⟨0, ?_, ?_⟩
      · simpa using ht
      · rw [hb] at h
        simpa using h
    · refine ⟨-t, ?_, ?_⟩
      · rw [abs_neg, abs_of_nonneg ht]
      · rw [abs_of_pos hb] at h
        linarith

/-- 推论（"阻断"形式）：可行 τ **不存在** ⟺ `c + 2 t |b| < 0`。 -/
theorem not_exists_tau_mul_le_iff {t c b : ℝ} (ht : 0 ≤ t) :
    (¬ ∃ τ : ℝ, |τ| ≤ t ∧ 2 * τ * b ≤ c) ↔ c + 2 * t * |b| < 0 := by
  rw [← not_le, ← exists_tau_mul_le_iff ht]

/-! ## (B) 真实 Point 上的范数平方差恒等式与消费者 -/

/-- **范数平方差恒等式**：`‖x − a‖² − ‖x − b‖² = ‖a‖² − ‖b‖² + 2⟪x, b − a⟫`。 -/
theorem norm_sub_sq_sub_norm_sub_sq (x a b : Point) :
    ‖x - a‖ ^ 2 - ‖x - b‖ ^ 2 = ‖a‖ ^ 2 - ‖b‖ ^ 2 + 2 * (inner ℝ x (b - a) : ℝ) := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
  ring

/-- **消费者（平分线差式）**：设 `M = (a+c)/2`、`X = M + τ•u`，则
```
‖X − b‖² − ‖X − a‖² = (‖b − M‖² − ‖c − a‖²/4) − 2τ⟪u, b − a⟫
```
即 `c0 = ‖b − M‖² − ‖c − a‖²/4`、`b_⟂ = ⟪u, b − a⟫`，差式**恰为 `c0 − 2τb_⟂`**。
**该恒等式不需要 u 与 c−a 正交。** -/
theorem bisector_difference {a c b M u : Point} {τ : ℝ}
    (hM : M = (2 : ℝ)⁻¹ • (a + c)) :
    ‖(M + τ • u) - b‖ ^ 2 - ‖(M + τ • u) - a‖ ^ 2 =
      (‖b - M‖ ^ 2 - ‖c - a‖ ^ 2 / 4) - 2 * τ * (inner ℝ u (b - a) : ℝ) := by
  subst hM
  simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    smul_add, smul_smul, real_inner_self_eq_norm_sq, real_inner_comm, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  ring

/-- **平分线等距**：若 `u ⊥ (c − a)`，则 `X = M + τ•u` 到 `a`、`c` 等距
（这才是"平分线"性质）。 -/
theorem bisector_equidistant {a c M u : Point} {τ : ℝ}
    (hM : M = (2 : ℝ)⁻¹ • (a + c)) (hu : (inner ℝ u (c - a) : ℝ) = 0) :
    ‖(M + τ • u) - a‖ = ‖(M + τ • u) - c‖ := by
  have hu' : (inner ℝ (c - a) u : ℝ) = 0 := by rw [real_inner_comm]; exact hu
  have hzero : ‖(M + τ • u) - a‖ ^ 2 - ‖(M + τ • u) - c‖ ^ 2 = 0 := by
    subst hM
    simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      smul_add, smul_smul, real_inner_self_eq_norm_sq, real_inner_comm, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    have hcu : (inner ℝ c u : ℝ) = inner ℝ a u := by
      have h := hu'
      rw [inner_sub_left] at h
      linarith
    ring_nf
    linear_combination (2 * τ) * hcu
  have hsq : ‖(M + τ • u) - a‖ ^ 2 = ‖(M + τ • u) - c‖ ^ 2 := sub_eq_zero.mp hzero
  have h1 : (0 : ℝ) ≤ ‖(M + τ • u) - a‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖(M + τ • u) - c‖ := norm_nonneg _
  nlinarith [hsq, h1, h2, sq_nonneg (‖(M + τ • u) - a‖ - ‖(M + τ • u) - c‖)]

end N11Formalization
