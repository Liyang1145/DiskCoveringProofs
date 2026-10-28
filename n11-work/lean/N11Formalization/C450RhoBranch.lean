import Mathlib

/-!
# C450：`t → ρ` 两支合法域（V2：符号余量 + 不依赖 membership 顺序）

**本文件不含 C450 的排除结论。**

## V2 相对 `lead/c450-rhobranch-gate1.log` exit1（9 处）的分类与修复

| gate 站点 | 错误类别 | 根因 | V2 修法 |
|---|---|---|---|
| L46 | 参数类型 | `Real.sq_sqrt` 要 `0 ≤ 被开方数`，我传了 `0 ≤ √…` | 先证 `0 ≤ R² − sin²t`（由合法域 `sin² ≤ R²`），再 `Real.sq_sqrt` |
| L54/L59 | 退化分支 | `t = π/2` 时旧写法走 `cos t = 0` 分支、`linarith` 无源 | **符号余量**：`sin²t ≤ R² < 1` + `sin²+cos²=1` ⟹ `cos²t > 0`；配 `0 ≤ cos t` ⟹ `cos t > 0`（`cos_pos_of_legal`） |
| L73 | 参数顺序 | `Real.strictAntiOn_cos` 的 membership 顺序我猜错 | **不再用** `strictAntiOn/strictMonoOn`：改用已确认的 `Real.sin_le_sin_of_le_of_le_pi_div_two` 与 `Real.cos_sub_cos`（和差化积） |
| L80/102/105/128/146 | `linarith` 无源 | 上游 `cos t > 0` / `sin²` 单调缺失 | 由上面两条补齐（`cos_antitone`、`sin_sq_mono` 显式具名） |

## 结构

* `R_sq_lt_one`、`cos_pos_of_legal`：合法域 ⟹ `cos t > 0`（符号，非裸 `linarith`）；
* `cos_antitone`（和差化积 `cos t₁ − cos t₂ = 2 sin((t₁+t₂)/2) sin((t₂−t₁)/2) ≥ 0`）；
* `sin_sq_mono`（用 `Real.sin_le_sin_of_le_of_le_pi_div_two`，**无 membership 顺序问题**）；
* `rho_minus_eq_ratio`（内根比值恒等式，含严格正性）、`rho_plus_antitone`、`rho_minus_monotone`；
* `rho_plus_mem_of_t_box` / `rho_minus_mem_of_t_box`：两支各自的 `t`-盒 ⟹ `ρ`-盒。

## 不主张

* 不主张段域完整（`TMAX`、`v`、`e` 来源未接）、逐段盒界、`hper`、十边界支；数值读数不称 certified。
-/

namespace N11Formalization

section

/-- `R² < 1`（`R = 19/50`）。 -/
theorem R_sq_lt_one : ((19 : ℝ) / 50) ^ 2 < 1 := by norm_num

/-- **合法域 ⟹ `cos t > 0`**（符号余量：`sin²t ≤ R² < 1`，`sin²+cos²=1`，再用 `0 ≤ cos t`）。 -/
theorem cos_pos_of_legal {t : ℝ} (hcos : 0 ≤ Real.cos t)
    (hleg : (Real.sin t) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2) : 0 < Real.cos t := by
  have hcos2 : 1 - ((19 : ℝ) / 50) ^ 2 ≤ Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t, hleg]
  rcases eq_or_lt_of_le hcos with h | h
  · rw [← h] at hcos2
    nlinarith [R_sq_lt_one]
  · exact h

/-- **`cos` 反调**（`[0,π/2]`，和差化积）。 -/
theorem cos_antitone {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (h0 : 0 ≤ t₁) (hπ : t₂ ≤ Real.pi / 2) :
    Real.cos t₂ ≤ Real.cos t₁ := by
  have hprod : Real.cos t₁ - Real.cos t₂
      = 2 * Real.sin ((t₁ + t₂) / 2) * Real.sin ((t₂ - t₁) / 2) := by
    have h := Real.cos_sub_cos t₁ t₂
    have hneg : Real.sin ((t₁ - t₂) / 2) = -Real.sin ((t₂ - t₁) / 2) := by
      rw [← Real.sin_neg]; ring_nf
    rw [h, hneg]; ring
  have h1 : 0 ≤ Real.sin ((t₁ + t₂) / 2) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos, hπ, h0]
  have h2 : 0 ≤ Real.sin ((t₂ - t₁) / 2) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos, hπ, h0]
  nlinarith [hprod, h1, h2]

/-- **`sin²` 单调**（`[0,π/2]`；用已确认的 `Real.sin_le_sin_of_le_of_le_pi_div_two`）。 -/
theorem sin_sq_mono {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (h0 : 0 ≤ t₁) (hπ : t₂ ≤ Real.pi / 2) :
    (Real.sin t₁) ^ 2 ≤ (Real.sin t₂) ^ 2 := by
  have hle : Real.sin t₁ ≤ Real.sin t₂ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hπ ht
  have hnn : 0 ≤ Real.sin t₁ := Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [hπ]⟩
  nlinarith [hle, Real.sin_le_one t₂]

/-- **内根比值恒等式**（含严格正性）：`cos t − √(R²−sin²t) = (1−R²)/(cos t + √(R²−sin²t))`。 -/
theorem rho_minus_eq_ratio {t : ℝ} (hcos : 0 ≤ Real.cos t)
    (hleg : (Real.sin t) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2) :
    Real.cos t - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)
      = (1 - ((19 : ℝ) / 50) ^ 2)
        / (Real.cos t + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)) := by
  have hrad : 0 ≤ ((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2 := by linarith
  have hsq : (Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)) ^ 2
      = ((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2 := Real.sq_sqrt hrad
  have hcospos : 0 < Real.cos t := cos_pos_of_legal hcos hleg
  have hspos : 0 ≤ Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2) := Real.sqrt_nonneg _
  have hden : Real.cos t + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2) ≠ 0 := by
    have : 0 < Real.cos t + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2) := by linarith
    exact ne_of_gt this
  apply (eq_div_iff hden).2
  nlinarith [Real.sin_sq_add_cos_sq t, hsq]

/-- **外根（= 分母）反调**：`t₁ ≤ t₂`、`0 ≤ t₁`、`t₂ ≤ π/2`、`sin²t₂ ≤ R²` ⟹ `ρ₊(t₂) ≤ ρ₊(t₁)`。 -/
theorem rho_plus_antitone {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (h0 : 0 ≤ t₁)
    (hπ : t₂ ≤ Real.pi / 2) (hsin : (Real.sin t₂) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2) :
    Real.cos t₂ + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t₂) ^ 2)
      ≤ Real.cos t₁ + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t₁) ^ 2) := by
  have hcos_le : Real.cos t₂ ≤ Real.cos t₁ := cos_antitone ht h0 hπ
  have hsin_le : (Real.sin t₁) ^ 2 ≤ (Real.sin t₂) ^ 2 := sin_sq_mono ht h0 hπ
  have hsub : ((19 : ℝ) / 50) ^ 2 - (Real.sin t₂) ^ 2
      ≤ ((19 : ℝ) / 50) ^ 2 - (Real.sin t₁) ^ 2 := by linarith
  have hsq : Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t₂) ^ 2)
      ≤ Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t₁) ^ 2) := Real.sqrt_le_sqrt hsub
  linarith

/-- **内根单调增**（比值形式，分母反调且正）。 -/
theorem rho_minus_monotone {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (h0 : 0 ≤ t₁)
    (hπ : t₂ ≤ Real.pi / 2) (hsin : (Real.sin t₂) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2) :
    Real.cos t₁ - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t₁) ^ 2)
      ≤ Real.cos t₂ - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t₂) ^ 2) := by
  have hcos1 : 0 ≤ Real.cos t₁ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [hπ]⟩
  have hcos2 : 0 ≤ Real.cos t₂ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [hπ]⟩
  have hleg1 : (Real.sin t₁) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2 :=
    le_trans (sin_sq_mono ht h0 hπ) hsin
  have r1 := rho_minus_eq_ratio (t := t₁) hcos1 hleg1
  have r2 := rho_minus_eq_ratio (t := t₂) hcos2 hsin
  have hden_le := rho_plus_antitone ht h0 hπ hsin
  have hden2pos : 0 < Real.cos t₂ + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t₂) ^ 2) := by
    have := cos_pos_of_legal hcos2 hsin
    have := Real.sqrt_nonneg (((19 : ℝ) / 50) ^ 2 - (Real.sin t₂) ^ 2)
    linarith
  have hnum : 0 < 1 - ((19 : ℝ) / 50) ^ 2 := by linarith [R_sq_lt_one]
  rw [r1, r2]
  exact div_le_div_of_nonneg_left (le_of_lt hnum) hden2pos hden_le

/-- **外根盒**：`t ∈ [t_lo,t_hi] ⊆ [0,π/2]`、`sin²t_hi ≤ R²` ⟹ `ρ₊ ∈ [ρ₊(t_hi), ρ₊(t_lo)]`。 -/
theorem rho_plus_mem_of_t_box {t t_lo t_hi : ℝ} (ht1 : t_lo ≤ t) (ht2 : t ≤ t_hi)
    (h0 : 0 ≤ t_lo) (hπ : t_hi ≤ Real.pi / 2)
    (hsin : (Real.sin t_hi) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2) :
    Real.cos t_hi + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t_hi) ^ 2)
        ≤ Real.cos t + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)
      ∧ Real.cos t + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)
        ≤ Real.cos t_lo + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t_lo) ^ 2) := by
  have hsin_t : (Real.sin t) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2 :=
    le_trans (sin_sq_mono ht2 (by linarith) hπ) hsin
  exact ⟨rho_plus_antitone ht2 (by linarith) hπ hsin,
    rho_plus_antitone ht1 h0 (by linarith) hsin_t⟩

/-- **内根盒**：同前提。 -/
theorem rho_minus_mem_of_t_box {t t_lo t_hi : ℝ} (ht1 : t_lo ≤ t) (ht2 : t ≤ t_hi)
    (h0 : 0 ≤ t_lo) (hπ : t_hi ≤ Real.pi / 2)
    (hsin : (Real.sin t_hi) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2) :
    Real.cos t_lo - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t_lo) ^ 2)
        ≤ Real.cos t - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)
      ∧ Real.cos t - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)
        ≤ Real.cos t_hi - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t_hi) ^ 2) := by
  have hsin_t : (Real.sin t) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2 :=
    le_trans (sin_sq_mono ht2 (by linarith) hπ) hsin
  exact ⟨rho_minus_monotone ht1 h0 (by linarith) hsin_t,
    rho_minus_monotone ht2 (by linarith) hπ hsin⟩

#check @N11Formalization.rho_minus_eq_ratio
#check @N11Formalization.rho_plus_mem_of_t_box
#check @N11Formalization.rho_minus_mem_of_t_box

#print axioms N11Formalization.rho_plus_mem_of_t_box
#print axioms N11Formalization.rho_minus_mem_of_t_box

end

end N11Formalization
