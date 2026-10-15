import N11Formalization.C450Identify
import N11Formalization.C450RhoBranch
import N11Formalization.C450BoxCalib
import N11Formalization.C450GeomBox

/-!
# C450：源 t-盒 → ρ-盒 → ℓ-盒 → b-盒（V2：**域 `sin² ≤ R²` 真实显式付**）

**本文件不含 C450 的排除结论。**

## V2 相对 `lead/c450-sourcechain-gate1.log` exit1 的修复

| 站点 | 错误 | 根因 | V2 修法 |
|---|---|---|---|
| L56 | `linarith` 无源 | 我用 `sin ≤ 1` 想推 `sin²t ≤ R²` ✗（推不出） | 新增 `sin_sq_le_R_sq_of_box`：**显式**用 `Real.sin_lt`（`sin x < x`，`x > 0`）+ `Real.sin_nonneg_of_mem_Icc` + `sin_sq_mono` + `(1/1250)² ≤ R²`（有理）⟹ `sin²t ≤ R²` |
| L59/L60 | unsolved goals | `Real.sin_le_one`/`sin_nonneg_of_mem_Icc` 的参数形 | 全部写成显式 `Set.Icc` 成员（`constructor <;> linarith [Real.pi_gt_three]`） |
| L65 | `rw` 找不到 `cos 0 − √…` | 我把 `rho_minus_monotone` 的参数序用错（得到 `ρ₋(t) ≤ ρ₋(1/1250)` 却当成 `ρ₋(0) ≤ ρ₋(t)`） | 两次调用**显式给序**：下界 `rho_minus_monotone ht0 (by norm_num) (by linarith [hπ]) hleg`；上界 `rho_minus_monotone ht1 ht0 hπ hleg1250` |
| L73/L91 | `linarith` 无源 | 上面两条的下游 | 由上修好 |

## 盒域 provenance（显式，不宣称整个 ten-branch）

内根 `t ∈ [0,1/1250]` ⟹ `ρ ∈ [6199/10000, 6201/10000]`（= `C450BoxCalib` 同盒）；
外根同 `t`-盒 ⟹ `ρ ∈ [3799/10000, 1381/1000]`（**另一盒**，其 `ℓ/v/e` 须另算）。
`v`、`e` 的域来源仍是**显式前提**（真实 segment 输入未付）。

## 不主张

* 不主张整个 ten-branch、逐段盒界、`hper`、十边界支；数值读数不称 certified。
-/

namespace N11Formalization

section

/-- `√(R² − (1/1250)²) ≥ 3799/10000`（两侧平方的有理比较）。 -/
theorem sqrt_radicand_ge : (3799 : ℝ) / 10000 ≤ Real.sqrt (((19 : ℝ) / 50) ^ 2 - (1 / 1250) ^ 2) := by
  have hsq : ((3799 : ℝ) / 10000) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2 - (1 / 1250) ^ 2 := by norm_num
  exact (Real.le_sqrt (by norm_num) (by linarith [hsq])).mpr hsq

/-- **域显式付**：`t ∈ [0,1/1250]` ⟹ `sin²t ≤ R²`
（`sin x < x` 于 `x > 0` + `sin ≥ 0` 于 `[0,π]` + `sin²` 单调 + `(1/1250)² ≤ R²`）。 -/
theorem sin_sq_le_R_sq_of_box {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 1250) :
    (Real.sin t) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2 := by
  have hx : (0 : ℝ) < 1 / 1250 := by norm_num
  have hlt : Real.sin (1 / 1250 : ℝ) < 1 / 1250 := Real.sin_lt hx
  have hnn : 0 ≤ Real.sin (1 / 1250 : ℝ) :=
    Real.sin_nonneg_of_mem_Icc (show (1 / 1250 : ℝ) ∈ Set.Icc 0 Real.pi by
      constructor <;> linarith [Real.pi_gt_three])
  have h1250 : (Real.sin (1 / 1250 : ℝ)) ^ 2 ≤ (1 / 1250 : ℝ) ^ 2 := by nlinarith
  have hR : (1 / 1250 : ℝ) ^ 2 ≤ ((19 : ℝ) / 50) ^ 2 := by norm_num
  have hπ : (1 : ℝ) / 1250 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hmono : (Real.sin t) ^ 2 ≤ (Real.sin (1 / 1250 : ℝ)) ^ 2 := sin_sq_mono ht1 ht0 hπ
  linarith

/-- **内根 `ρ`-盒**：`t ∈ [0,1/1250]`、`‖c‖ = ρ₋(t)` ⟹ `ρ ∈ [6199/10000, 6201/10000]`。 -/
theorem rho_inner_box {c : Point} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 1250)
    (hρ : ‖c‖ = Real.cos t - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)) :
    (6199 : ℝ) / 10000 ≤ ‖c‖ ∧ ‖c‖ ≤ (6201 : ℝ) / 10000 := by
  have hπ : (1 : ℝ) / 1250 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hleg := sin_sq_le_R_sq_of_box ht0 ht1
  have hleg1250 := sin_sq_le_R_sq_of_box (t := 1 / 1250) (by norm_num) (le_refl _)
  -- 下界：`ρ₋(0) ≤ ρ₋(t)`（参数序显式）
  have hlo : Real.cos 0 - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin 0) ^ 2)
      ≤ Real.cos t - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2) :=
    rho_minus_monotone ht0 (by norm_num) (by linarith [hπ]) hleg
  -- 上界：`ρ₋(t) ≤ ρ₋(1/1250)`
  have hhi : Real.cos t - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)
      ≤ Real.cos (1 / 1250) - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin (1 / 1250)) ^ 2) :=
    rho_minus_monotone ht1 ht0 hπ hleg1250
  have hzero : Real.cos 0 - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin 0) ^ 2)
      = 1 - (19 : ℝ) / 50 := by
    norm_num [Real.cos_zero, Real.sin_zero]
  -- 上界端点的显式估计
  have hsin1250 : (Real.sin (1 / 1250 : ℝ)) ^ 2 ≤ (1 / 1250 : ℝ) ^ 2 := by
    have hx : (0 : ℝ) < 1 / 1250 := by norm_num
    have hlt : Real.sin (1 / 1250 : ℝ) < 1 / 1250 := Real.sin_lt hx
    have hnn : 0 ≤ Real.sin (1 / 1250 : ℝ) :=
      Real.sin_nonneg_of_mem_Icc (show (1 / 1250 : ℝ) ∈ Set.Icc 0 Real.pi by
        constructor <;> linarith [Real.pi_gt_three])
    nlinarith
  have hsqmono : Real.sqrt (((19 : ℝ) / 50) ^ 2 - (1 / 1250 : ℝ) ^ 2)
      ≤ Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin (1 / 1250)) ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hupper : Real.cos (1 / 1250) - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin (1 / 1250)) ^ 2)
      ≤ (6201 : ℝ) / 10000 := by
    have h1 : Real.cos (1 / 1250) ≤ 1 := Real.cos_le_one _
    have h2 := sqrt_radicand_ge
    linarith
  rw [hρ]
  exact ⟨by linarith [hlo, hzero,
      (show (6199 : ℝ) / 10000 ≤ 1 - (19 : ℝ) / 50 from by norm_num)],
    by linarith [hhi, hupper]⟩

/-- `1 − R ≥ 6199/10000`。 -/
theorem one_sub_R_ge' : (6199 : ℝ) / 10000 ≤ 1 - (19 : ℝ) / 50 := by norm_num

/-- **外根 `ρ`-盒**：`t ∈ [0,1/1250]`、`‖c‖ = ρ₊(t)` ⟹ `ρ ∈ [3799/10000, 1381/1000]`。 -/
theorem rho_outer_box {c : Point} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 1250)
    (hρ : ‖c‖ = Real.cos t + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)) :
    (3799 : ℝ) / 10000 ≤ ‖c‖ ∧ ‖c‖ ≤ (1381 : ℝ) / 1000 := by
  have hπ : (1 : ℝ) / 1250 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hleg := sin_sq_le_R_sq_of_box ht0 ht1
  have hleg1250 := sin_sq_le_R_sq_of_box (t := 1 / 1250) (by norm_num) (le_refl _)
  -- 反调：`ρ₊(1/1250) ≤ ρ₊(t) ≤ ρ₊(0)`
  have hlo : Real.cos (1 / 1250) + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin (1 / 1250)) ^ 2)
      ≤ Real.cos t + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2) :=
    rho_plus_antitone ht1 ht0 hπ hleg1250
  have hhi : Real.cos t + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2)
      ≤ Real.cos 0 + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin 0) ^ 2) :=
    rho_plus_antitone ht0 (by norm_num) (by linarith [hπ]) hleg
  have hzero : Real.cos 0 + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin 0) ^ 2)
      = 1 + (19 : ℝ) / 50 := by
    norm_num [Real.cos_zero, Real.sin_zero]
  have hsin1250 : (Real.sin (1 / 1250 : ℝ)) ^ 2 ≤ (1 / 1250 : ℝ) ^ 2 := by
    have hx : (0 : ℝ) < 1 / 1250 := by norm_num
    have hlt : Real.sin (1 / 1250 : ℝ) < 1 / 1250 := Real.sin_lt hx
    have hnn : 0 ≤ Real.sin (1 / 1250 : ℝ) :=
      Real.sin_nonneg_of_mem_Icc (show (1 / 1250 : ℝ) ∈ Set.Icc 0 Real.pi by
        constructor <;> linarith [Real.pi_gt_three])
    nlinarith
  have hsqmono : Real.sqrt (((19 : ℝ) / 50) ^ 2 - (1 / 1250 : ℝ) ^ 2)
      ≤ Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin (1 / 1250)) ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hlow : (3799 : ℝ) / 10000
      ≤ Real.cos (1 / 1250) + Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin (1 / 1250)) ^ 2) := by
    have h1 := sqrt_radicand_ge
    have h2 : 0 ≤ Real.cos (1 / 1250) :=
      Real.cos_nonneg_of_mem_Icc (show (1 / 1250 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_gt_three])
    linarith
  rw [hρ]
  exact ⟨by linarith [hlo, hlow], by linarith [hhi, hzero]⟩

/-- **内支串联**：`t`-盒 + `ρ`-盒 + 显式 `v/e` 盒 ⟹ `ℓ`-盒（接已绿 `C450BoxCalib`）。 -/
theorem inner_chain {c : Point} {e v t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 1250)
    (hρ : ‖c‖ = Real.cos t - Real.sqrt (((19 : ℝ) / 50) ^ 2 - (Real.sin t) ^ 2))
    (hvlo : (1 : ℝ) / 4 ≤ v) (hvhi : v ≤ 1) (hv : v = c 0 / ‖c‖)
    (he0 : (0 : ℝ) ≤ e) (he1 : e ≤ 1 / 250)
    (hℓ : ‖c - !₂[e, 0]‖ = Real.sqrt (‖c‖ ^ 2 - 2 * ‖c‖ * v * e + e ^ 2)) :
    Real.sqrt ((((6199 : ℝ) / 10000) ^ 2) - 2 * ((6199 : ℝ) / 10000) * 1 * (1 / 250)
          + (1 / 250) ^ 2)
        ≤ ‖c - !₂[e, 0]‖
      ∧ ‖c - !₂[e, 0]‖
        ≤ Real.sqrt ((((6201 : ℝ) / 10000) ^ 2) - 2 * ((6201 : ℝ) / 10000) * (1 / 4) * 0
          + 0 ^ 2) := by
  obtain ⟨hρlo, hρhi⟩ := rho_inner_box ht0 ht1 hρ
  have h := ell_box_seg0 (ρ := ‖c‖) (v := v) (e := e) hρlo hρhi hvlo hvhi he0 he1
  rw [← hℓ] at h
  exact h

#check @N11Formalization.sin_sq_le_R_sq_of_box
#check @N11Formalization.rho_inner_box
#check @N11Formalization.rho_outer_box
#check @N11Formalization.inner_chain

#print axioms N11Formalization.rho_inner_box
#print axioms N11Formalization.rho_outer_box

end

end N11Formalization
