/-
n=11 全局最优性形式化 —— 「盘数据 → 弧数据」接口（kernel-checked）

`ArcRoots.lean` 的内根替换吃的是**弧数据** `(中点方向 u, 半宽 θ, 半径 r)`。本文件把这层输入
从**实际盘数据** `(c₀ : Point, r)` 算出来，从而闭掉接口环：

* `centerDir c := ‖c‖⁻¹ • c`（中点方向，`c ≠ 0` 时单位向量）；
* `capHalfWidth c r := arccos ((1 + ‖c‖² - r²) / (2‖c‖))`（cap 半宽）；
* 证 `0 ≤ capHalfWidth c r ≤ arcsin r`（**不需要**「盘与 S¹ 相交」这一额外输入，见下）；
* 证 cap 相同：`‖x‖=1` 时 `dist x c ≤ r ⟺ cos θ ≤ ⟪x, centerDir c⟫ ⟺ dist x (ρ₊ • centerDir c) ≤ r`
  （"同一实际弧"，需盘确实与 `S¹` 相交，即 `MeetsCircle` 形式）；
* 端到端：`MeetsCircle` ⇒ `ArcRoots` 全部前提成立 ⇒ 可用 `dist_innerRoot_le_of_outerRoot`。

零 `sorry`、零自定义 `axiom`。
-/
import Mathlib
import N11Formalization.Definitions
import N11Formalization.Geometry.CapArc
import N11Formalization.Geometry.InnerRoot
import N11Formalization.Geometry.ArcRoots

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace N11Formalization

noncomputable section

/-! ## 一般形式（盘心距离 `s = ⟪c₀,u⟫ > 0`） -/

/-- 盘 `B(s•u, r)` 在 `S¹` 上的 cap 由阈值 `(1+s²-r²)/(2s)` 给出（`mem_sphere_closedBall_iff` 的阈值形式）。 -/
theorem cap_iff_cos_threshold {u x : Point} (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) {s r : ℝ}
    (hs : 0 < s) (hr0 : 0 ≤ r) :
    dist x (s • u) ≤ r ↔ (1 + s ^ 2 - r ^ 2) / (2 * s) ≤ inner ℝ x u := by
  have hnorm : ‖s • u‖ ^ 2 = s ^ 2 := by rw [norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
  have hinner : inner ℝ x (s • u) = s * inner ℝ x u := by rw [real_inner_smul_right]
  rw [mem_sphere_closedBall_iff hr0 hx, hnorm, hinner, div_le_iff₀ (by linarith)]
  constructor <;> intro h <;> linarith

/-- **cap 半宽的核心代数**：阈值 `≥ √(1-r²)`（等价 `(s²-(1-r²))² ≥ 0`）——即源文 §1
「角宽 ≤ 2asin(r)」的定量核心（对任意 `s > 0`、`0 ≤ r ≤ 1` 成立，与该盘是否真的相交无关）。 -/
theorem sqrt_one_sub_sq_le_cap_threshold {s r : ℝ} (hs : 0 < s) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.sqrt (1 - r ^ 2) ≤ (1 + s ^ 2 - r ^ 2) / (2 * s) := by
  have hnum : 0 ≤ 1 + s ^ 2 - r ^ 2 := by nlinarith
  have hτ0 : 0 ≤ (1 + s ^ 2 - r ^ 2) / (2 * s) := div_nonneg hnum (by linarith)
  have hden2 : (0 : ℝ) < (2 * s) ^ 2 := by nlinarith
  have hsq : (Real.sqrt (1 - r ^ 2)) ^ 2 ≤ ((1 + s ^ 2 - r ^ 2) / (2 * s)) ^ 2 := by
    rw [Real.sq_sqrt (by nlinarith), div_pow, le_div_iff₀ hden2]
    nlinarith [sq_nonneg (s ^ 2 - (1 - r ^ 2))]
  have h2 := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hτ0] at h2

/-- cap 半宽（`arccos` 形式）不超过 `arcsin r`：`arccos ((1+s²-r²)/(2s)) ≤ arcsin r`。
（`0 ≤ r < 1` 保证阈值 `≥ -1`；阈值 `> 1` 时左边为 `0`，仍成立。） -/
theorem arccos_cap_threshold_le_arcsin {s r : ℝ} (hs : 0 < s) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.arccos ((1 + s ^ 2 - r ^ 2) / (2 * s)) ≤ Real.arcsin r := by
  set C : ℝ := (1 + s ^ 2 - r ^ 2) / (2 * s) with hC
  have hCn : -1 ≤ C := by
    rw [hC, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * s)]
    nlinarith [hs, hr0, hr1]
  have hcos_ge : Real.cos (Real.arcsin r) ≤ Real.cos (Real.arccos C) := by
    rw [Real.cos_arcsin]
    by_cases hC1 : C ≤ 1
    · rw [Real.cos_arccos hCn hC1]
      exact sqrt_one_sub_sq_le_cap_threshold hs hr0 hr1.le
    · rw [Real.arccos_of_one_le (not_le.mp hC1).le, Real.cos_zero]
      calc Real.sqrt (1 - r ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith)
        _ = 1 := Real.sqrt_one
  by_contra hcon
  rw [not_le] at hcon
  have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arcsin_nonneg.mpr hr0)
    (Real.arccos_le_pi C) hcon
  linarith

/-- 盘心距离恰是 `ArcRoots` 两条径向根所在二次方程的根：`s² - 2s·cos θ + (1-r²) = 0`。 -/
theorem diskRoot_relation {s r : ℝ} (hs : s ≠ 0) :
    s ^ 2 - 2 * s * ((1 + s ^ 2 - r ^ 2) / (2 * s)) + (1 - r ^ 2) = 0 := by
  field_simp
  ring

/-! ## 盘数据 `(c₀, r)` → 弧数据 `(u, θ)` -/

/-- 盘心方向（单位向量），由盘心 `c` 得到弧中点方向。 -/
def centerDir (c : Point) : Point := (‖c‖)⁻¹ • c

/-- cap 半宽：`θ := arccos ((1 + ‖c‖² - r²) / (2‖c‖))`。 -/
def capHalfWidth (c : Point) (r : ℝ) : ℝ := Real.arccos ((1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖))

theorem centerDir_norm {c : Point} (hc : c ≠ 0) : ‖centerDir c‖ = 1 := by
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [centerDir, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (ne_of_gt hs)]

/-- `c = ‖c‖ • centerDir c`（`c ≠ 0`）。 -/
theorem self_eq_norm_smul_centerDir {c : Point} (hc : c ≠ 0) : c = ‖c‖ • centerDir c := by
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [centerDir, smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]

theorem capHalfWidth_nonneg (c : Point) (r : ℝ) : 0 ≤ capHalfWidth c r :=
  Real.arccos_nonneg _

/-- **`θ ≤ arcsin r`**（本文件的核心）：只需 `c ≠ 0`、`0 ≤ r < 1`，
**不需要**「盘与 `S¹` 相交」这一额外输入（cap 为空时 `θ = 0`，仍然成立）。 -/
theorem capHalfWidth_le_arcsin {c : Point} {r : ℝ} (hc : c ≠ 0) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    capHalfWidth c r ≤ Real.arcsin r :=
  arccos_cap_threshold_le_arcsin (norm_pos_iff.mpr hc) hr0 hr1

/-- 若盘真的与 `S¹` 相交（`MeetsCircle` 形式），则阈值 `≤ 1`，从而 `cos θ` 恰等于该阈值。 -/
theorem cap_threshold_le_one_of_meets {c : Point} {r : ℝ} (hc : c ≠ 0) (hr0 : 0 ≤ r)
    (hmeet : ∃ y : Point, ‖y‖ = 1 ∧ dist y c ≤ r) :
    (1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖) ≤ 1 := by
  obtain ⟨y, hy, hyd⟩ := hmeet
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hu : ‖centerDir c‖ = 1 := centerDir_norm hc
  have h1 := (cap_iff_cos_threshold hu hy hs hr0).mp (by rwa [self_eq_norm_smul_centerDir hc] at hyd)
  have h2 : inner ℝ y (centerDir c) ≤ 1 := by
    calc inner ℝ y (centerDir c) ≤ ‖y‖ * ‖centerDir c‖ := real_inner_le_norm _ _
      _ = 1 := by rw [hy, hu, one_mul]
  linarith

/-- **同一实际弧（端到端形式）**：`c ≠ 0`、`0 ≤ r < 1`、盘与 `S¹` 相交时，
该盘的 cap 恰是半宽 `θ = capHalfWidth c r` 的弧：`‖x‖=1` 时
`dist x c ≤ r ⟺ cos θ ≤ ⟪x, centerDir c⟫ ⟺ dist x (ρ₊ • centerDir c) ≤ r`。 -/
theorem cap_eq_of_meets {c x : Point} {r : ℝ} (hc : c ≠ 0) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmeet : ∃ y : Point, ‖y‖ = 1 ∧ dist y c ≤ r) (hx : ‖x‖ = 1) :
    (dist x c ≤ r ↔ Real.cos (capHalfWidth c r) ≤ inner ℝ x (centerDir c)) ∧
      (dist x c ≤ r ↔ dist x (outerRoot (capHalfWidth c r) r • centerDir c) ≤ r) := by
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hu : ‖centerDir c‖ = 1 := centerDir_norm hc
  have hC1 : (1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖) ≤ 1 :=
    cap_threshold_le_one_of_meets hc hr0 hmeet
  have hCn : -1 ≤ (1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * ‖c‖)]
    nlinarith [hs, hr0, hr1]
  have hcos : Real.cos (capHalfWidth c r) = (1 + ‖c‖ ^ 2 - r ^ 2) / (2 * ‖c‖) := by
    rw [capHalfWidth]
    exact Real.cos_arccos hCn hC1
  have hθ0 : 0 ≤ capHalfWidth c r := capHalfWidth_nonneg c r
  have hθ : capHalfWidth c r ≤ Real.arcsin r := capHalfWidth_le_arcsin hc hr0 hr1
  constructor
  · conv_lhs => rw [self_eq_norm_smul_centerDir hc]
    rw [cap_iff_cos_threshold hu hx hs hr0, ← hcos]
  · conv_lhs => rw [self_eq_norm_smul_centerDir hc]
    rw [cap_iff_cos_threshold hu hx hs hr0, ← hcos]
    exact (cap_outerRoot_iff hu hx hr0 hr1 hθ0 hθ).symm

/-- **端到端内根替换**：盘与 `S¹` 相交时，`ArcRoots` 的全部前提自动满足，可直接替换径向根：
`‖x‖ ≤ 1` 且 `dist x (ρ₊ • centerDir c) ≤ r` ⇒ `dist x (ρ₋ • centerDir c) ≤ r`
（`ρ_± = innerRoot/outerRoot (capHalfWidth c r) r`）。 -/
theorem innerRoot_replacement_of_disk {c x : Point} {r : ℝ} (hc : c ≠ 0) (hr0 : 0 < r)
    (hr1 : r < 1) (hmeet : ∃ y : Point, ‖y‖ = 1 ∧ dist y c ≤ r) (hx : ‖x‖ ≤ 1)
    (h : dist x (outerRoot (capHalfWidth c r) r • centerDir c) ≤ r) :
    dist x (innerRoot (capHalfWidth c r) r • centerDir c) ≤ r :=
  dist_innerRoot_le_of_outerRoot (centerDir_norm hc) hr0 hr1 (capHalfWidth_nonneg c r)
    (capHalfWidth_le_arcsin hc hr0.le hr1) hx h

end

/-! ## 可信基础 -/

#print axioms N11Formalization.cap_iff_cos_threshold
#print axioms N11Formalization.sqrt_one_sub_sq_le_cap_threshold
#print axioms N11Formalization.arccos_cap_threshold_le_arcsin
#print axioms N11Formalization.capHalfWidth_le_arcsin
#print axioms N11Formalization.cap_threshold_le_one_of_meets
#print axioms N11Formalization.cap_eq_of_meets
#print axioms N11Formalization.innerRoot_replacement_of_disk

end N11Formalization
