import Mathlib

/-!
# C450：`ℓ²` 的**符号单调性**与 `ℓ`-盒（V2：显式具名每一步比较）

**本文件不含 C450 的排除结论。** 先修符号层，再给出正确的 `ℓ`-盒角点。

## V2 相对 `lead/c450-ellmono-gate1.log` exit1 的修复（L70/71/89/95）

gate1 全是 **`le_trans` 方向/中项推断错误**（我用了嵌套 `le_trans` 让 Lean 猜中项）。V2 按 Lead：
**每一步中间比较显式具名**，全部改用 `mul_le_mul_of_nonneg_left/right`，不再让 Lean 推断方向：
* `he0 : 0 ≤ e := le_trans helo0 helo`（此前多套了一层 `helo hehi`）；
* `hvhi0 : 0 ≤ v_hi := le_trans hvlo0 (le_trans hvlo hvhi)`（此前中项被强成 `v_hi`）；
* `hρv`/`hρvh`/`hCv`/`hDv`/`heρvlo`/`helo_ρlo`/`hvloelo` 各自具名。

## 口径修正（Lead 2026-10-01）

`ℓ²(ρ,v,e) = ρ² − 2ρve + e²`：对 `v` **反调**（`−2ρe ≤ 0`，`ρ,e ≥ 0`）；对 `e` 在 `e ≤ ρv` 段**反调**；
对 `ρ` 在 `ρ ≥ ve` 段**增**。**角点**：`ℓ_lo = ℓ(ρ_lo, v_hi, e_hi)`、`ℓ_hi = ℓ(ρ_hi, v_lo, e_lo)`。

## 不主张

* 本件**不**解除 root 几何 box 前提、**不**接 consumer 阈值；`C450GeomBox` 只作 generic bounds；
  新 consumer 若走宽盒 `b ∈ [11/20,2/3]` **不得**套旧 `3/5` 前提。
-/

namespace N11Formalization

section

/-- `ℓ²` 的等价形式（几何读数）：`(ρv−e)² + ρ²(1−v²) = ρ² − 2ρve + e²`。 -/
theorem ellsq_vform (ρ v e : ℝ) :
    (ρ * v - e) ^ 2 + ρ ^ 2 * (1 - v ^ 2) = ρ ^ 2 - 2 * ρ * v * e + e ^ 2 := by ring

/-- **对 `v` 反调**（`ρ ≥ 0`、`e ≥ 0`）。 -/
theorem ellsq_antitone_v {ρ e v₁ v₂ : ℝ} (hρ : 0 ≤ ρ) (he : 0 ≤ e) (h : v₁ ≤ v₂) :
    ρ ^ 2 - 2 * ρ * v₂ * e + e ^ 2 ≤ ρ ^ 2 - 2 * ρ * v₁ * e + e ^ 2 := by
  nlinarith [mul_nonneg (mul_nonneg hρ he) (sub_nonneg.mpr h)]

/-- **对 `e` 反调**（在 `e₂ ≤ ρv` 段）。 -/
theorem ellsq_antitone_e {ρ v e₁ e₂ : ℝ} (h₁ : e₁ ≤ e₂) (h₂ : e₂ ≤ ρ * v) :
    ρ ^ 2 - 2 * ρ * v * e₂ + e₂ ^ 2 ≤ ρ ^ 2 - 2 * ρ * v * e₁ + e₁ ^ 2 := by
  have hsum : e₁ + e₂ ≤ 2 * (ρ * v) := by linarith
  have hfac : 0 ≤ (e₂ - e₁) * (2 * (ρ * v) - (e₁ + e₂)) :=
    mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr hsum)
  nlinarith [hfac]

/-- **对 `ρ` 单调增**（在 `ρ ≥ ve` 段）。 -/
theorem ellsq_monotone_ρ {v e ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) (hve : v * e ≤ ρ₁) :
    ρ₁ ^ 2 - 2 * ρ₁ * v * e + e ^ 2 ≤ ρ₂ ^ 2 - 2 * ρ₂ * v * e + e ^ 2 := by
  have hsum : 2 * (v * e) ≤ ρ₁ + ρ₂ := by linarith
  have hfac : 0 ≤ (ρ₂ - ρ₁) * (ρ₁ + ρ₂ - 2 * (v * e)) :=
    mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hsum)
  nlinarith [hfac]

/-- **`ℓ²` 盒（修正角点，逐步具名）**。 -/
theorem ellsq_mem_of_box {ρ v e ρ_lo ρ_hi v_lo v_hi e_lo e_hi : ℝ}
    (hρlo : ρ_lo ≤ ρ) (hρhi : ρ ≤ ρ_hi) (hvlo : v_lo ≤ v) (hvhi : v ≤ v_hi)
    (helo : e_lo ≤ e) (hehi : e ≤ e_hi)
    (hρlo0 : 0 ≤ ρ_lo) (hvlo0 : 0 ≤ v_lo) (hv1 : v_lo ≤ 1) (helo0 : 0 ≤ e_lo)
    (heρv : e_hi ≤ ρ_lo * v_lo) (hvele : v_hi * e_hi ≤ ρ_lo) :
    ρ_lo ^ 2 - 2 * ρ_lo * v_hi * e_hi + e_hi ^ 2
        ≤ ρ ^ 2 - 2 * ρ * v * e + e ^ 2
      ∧ ρ ^ 2 - 2 * ρ * v * e + e ^ 2
        ≤ ρ_hi ^ 2 - 2 * ρ_hi * v_lo * e_lo + e_lo ^ 2 := by
  -- 非负（逐步具名）
  have hρ0 : 0 ≤ ρ := le_trans hρlo0 hρlo
  have he0 : 0 ≤ e := le_trans helo0 helo
  have hv0 : 0 ≤ v := le_trans hvlo0 hvlo
  have hvhi0 : 0 ≤ v_hi := le_trans hvlo0 (le_trans hvlo hvhi)
  -- 乘积比较（逐步具名，均用 mul_le_mul_of_nonneg_left/right）
  have hA1 : ρ_lo * v_lo ≤ ρ_lo * v := mul_le_mul_of_nonneg_left hvlo hρlo0
  have hA2 : ρ_lo * v ≤ ρ * v := mul_le_mul_of_nonneg_right hρlo hv0
  have hρv : ρ_lo * v_lo ≤ ρ * v := le_trans hA1 hA2
  have hB1 : ρ_lo * v_lo ≤ ρ_lo * v_hi := mul_le_mul_of_nonneg_left (le_trans hvlo hvhi) hρlo0
  have hB2 : ρ_lo * v_hi ≤ ρ * v_hi := mul_le_mul_of_nonneg_right hρlo hvhi0
  have hρvh : ρ_lo * v_lo ≤ ρ * v_hi := le_trans hB1 hB2
  have hC1 : ρ_lo * v_lo ≤ ρ * v_lo := mul_le_mul_of_nonneg_right hρlo hvlo0
  have hD0 : ρ_lo * v_lo ≤ ρ_lo * 1 := mul_le_mul_of_nonneg_left hv1 hρlo0
  have hD1 : ρ_lo * v_lo ≤ ρ_lo := by simpa using hD0
  -- 需要的三条方向性结论（各自具名）
  have heρvh : e_hi ≤ ρ * v_hi := le_trans heρv hρvh
  have heρvlo : e ≤ ρ * v_lo := le_trans hehi (le_trans heρv hC1)
  have helo_ρ : e_lo ≤ ρ := le_trans helo (le_trans hehi (le_trans heρv (le_trans hD1 hρlo)))
  have hve_lo : v_lo * e_lo ≤ ρ := by
    have h1 : v_lo * e_lo ≤ 1 * e_lo := mul_le_mul_of_nonneg_right hv1 helo0
    have h2 : (1 : ℝ) * e_lo = e_lo := one_mul e_lo
    have h3 : e_lo ≤ ρ := helo_ρ
    linarith
  constructor
  · have s1 : ρ ^ 2 - 2 * ρ * v_hi * e + e ^ 2 ≤ ρ ^ 2 - 2 * ρ * v * e + e ^ 2 :=
      ellsq_antitone_v hρ0 he0 hvhi
    have s2 : ρ ^ 2 - 2 * ρ * v_hi * e_hi + e_hi ^ 2
        ≤ ρ ^ 2 - 2 * ρ * v_hi * e + e ^ 2 :=
      ellsq_antitone_e hehi heρvh
    have s3 : ρ_lo ^ 2 - 2 * ρ_lo * v_hi * e_hi + e_hi ^ 2
        ≤ ρ ^ 2 - 2 * ρ * v_hi * e_hi + e_hi ^ 2 :=
      ellsq_monotone_ρ hρlo hvele
    linarith [s1, s2, s3]
  · have s1 : ρ ^ 2 - 2 * ρ * v * e + e ^ 2 ≤ ρ ^ 2 - 2 * ρ * v_lo * e + e ^ 2 :=
      ellsq_antitone_v hρ0 he0 hvlo
    have s2 : ρ ^ 2 - 2 * ρ * v_lo * e + e ^ 2 ≤ ρ ^ 2 - 2 * ρ * v_lo * e_lo + e_lo ^ 2 :=
      ellsq_antitone_e helo heρvlo
    have s3 : ρ ^ 2 - 2 * ρ * v_lo * e_lo + e_lo ^ 2
        ≤ ρ_hi ^ 2 - 2 * ρ_hi * v_lo * e_lo + e_lo ^ 2 :=
      ellsq_monotone_ρ hρhi hve_lo
    linarith [s1, s2, s3]

/-- **`ℓ`-盒（开方）**。 -/
theorem ell_mem_of_box {ρ v e ρ_lo ρ_hi v_lo v_hi e_lo e_hi : ℝ}
    (hρlo : ρ_lo ≤ ρ) (hρhi : ρ ≤ ρ_hi) (hvlo : v_lo ≤ v) (hvhi : v ≤ v_hi)
    (helo : e_lo ≤ e) (hehi : e ≤ e_hi)
    (hρlo0 : 0 ≤ ρ_lo) (hvlo0 : 0 ≤ v_lo) (hv1 : v_lo ≤ 1) (helo0 : 0 ≤ e_lo)
    (heρv : e_hi ≤ ρ_lo * v_lo) (hvele : v_hi * e_hi ≤ ρ_lo) :
    Real.sqrt (ρ_lo ^ 2 - 2 * ρ_lo * v_hi * e_hi + e_hi ^ 2)
        ≤ Real.sqrt (ρ ^ 2 - 2 * ρ * v * e + e ^ 2)
      ∧ Real.sqrt (ρ ^ 2 - 2 * ρ * v * e + e ^ 2)
        ≤ Real.sqrt (ρ_hi ^ 2 - 2 * ρ_hi * v_lo * e_lo + e_lo ^ 2) := by
  have h := ellsq_mem_of_box hρlo hρhi hvlo hvhi helo hehi hρlo0 hvlo0 hv1 helo0 heρv hvele
  exact ⟨Real.sqrt_le_sqrt h.1, Real.sqrt_le_sqrt h.2⟩

#check @N11Formalization.ellsq_antitone_v
#check @N11Formalization.ellsq_mem_of_box
#check @N11Formalization.ell_mem_of_box

#print axioms N11Formalization.ellsq_mem_of_box
#print axioms N11Formalization.ell_mem_of_box

end

end N11Formalization
