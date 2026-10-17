/-
n=11 全局最优性形式化 —— 内根替换的**几何接口**：从「实际弧」到径向根 ρ_±（kernel-checked）

`UNRESTRICTED-PROOF-ASSEMBLY` §1 说：
> For each boundary disk replace its outer radial root by the inner root of the SAME actual arc and
> SAME r. If rho_- * rho_+ = 1 - r² and c = (rho_- + rho_+)/2, then ... Thus coverage and actual
> arcs are preserved.

本文件把这个「隐含前提」变成**定理**：由几何数据（弧中点方向 `u`、弧半宽 `θ`、半径 `r`）定义

  ρ_± := cos θ ± √(r² - sin²θ)      （同一实际弧、同一 r 的两个径向根）

并**证出** Lead 引理所需的全部前提，其中 `c = cos θ > 0` 来自几何（`θ ≤ arcsin r < π/2`）：

* `innerRoot_le_outerRoot` : `ρ_- ≤ ρ_+`
* `innerRoot_add_outerRoot` : `ρ_- + ρ_+ = 2 cos θ`（故 `c = cos θ`）
* `innerRoot_mul_outerRoot` : `ρ_- · ρ_+ = 1 - r²`
* `cos_pos_of_arcHalfWidth` / `innerRoot_pos` : `0 < c`、`0 < ρ_-`
* `cap_innerRoot_iff` / `cap_outerRoot_iff` : **同一条实际弧**（两个盘在 `S¹` 上的交都是 `{⟪x,u⟫ ≥ cos θ}`）
* `dist_innerRoot_le_of_outerRoot` : **组合定理**：外根盘与 `D` 的交含于内根盘（覆盖被保持）

零 `sorry`、零自定义 `axiom`。
-/
import Mathlib
import N11Formalization.Definitions
import N11Formalization.Geometry.CapArc
import N11Formalization.Geometry.InnerRoot

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace N11Formalization

noncomputable section

/-! ## 径向根的定义与代数前提 -/

/-- 内径向根 `ρ_- = cos θ - √(r² - sin²θ)`（同一实际弧、同一 `r`）。 -/
def innerRoot (θ r : ℝ) : ℝ := Real.cos θ - Real.sqrt (r ^ 2 - Real.sin θ ^ 2)

/-- 外径向根 `ρ_+ = cos θ + √(r² - sin²θ)`。 -/
def outerRoot (θ r : ℝ) : ℝ := Real.cos θ + Real.sqrt (r ^ 2 - Real.sin θ ^ 2)

/-- 弧半宽 `θ`、半径 `r ≤ 1` 时 `sin²θ ≤ r²`（因为 `θ ≤ arcsin r`）。 -/
theorem sin_sq_le_sq_of_le_arcsin {θ r : ℝ} (hr1 : r ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ Real.arcsin r) : Real.sin θ ^ 2 ≤ r ^ 2 := by
  have hr0 : 0 ≤ r := Real.arcsin_nonneg.mp (le_trans hθ0 hθ)
  have hsin : Real.sin θ ≤ r := by
    have h3 : Real.sin θ ≤ Real.sin (Real.arcsin r) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (Real.arcsin_le_pi_div_two r) hθ
    have h4 : Real.sin (Real.arcsin r) = r := Real.sin_arcsin (by linarith) hr1
    linarith
  have hθπ : θ ≤ Real.pi := by
    linarith [le_trans hθ (Real.arcsin_le_pi_div_two r), Real.pi_pos]
  have h0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  nlinarith

theorem sin_sq_le_sq_of_le_arcsin' {θ r : ℝ} (hr1 : r ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ Real.arcsin r) : 0 ≤ r ^ 2 - Real.sin θ ^ 2 :=
  sub_nonneg.mpr (sin_sq_le_sq_of_le_arcsin hr1 hθ0 hθ)

theorem innerRoot_le_outerRoot (θ r : ℝ) : innerRoot θ r ≤ outerRoot θ r := by
  simp only [innerRoot, outerRoot]
  linarith [Real.sqrt_nonneg (r ^ 2 - Real.sin θ ^ 2)]

theorem innerRoot_add_outerRoot (θ r : ℝ) : innerRoot θ r + outerRoot θ r = 2 * Real.cos θ := by
  simp only [innerRoot, outerRoot]
  ring

/-- 源文的乘积关系：`ρ_- · ρ_+ = 1 - r²`。 -/
theorem innerRoot_mul_outerRoot {θ r : ℝ} (h : 0 ≤ r ^ 2 - Real.sin θ ^ 2) :
    innerRoot θ r * outerRoot θ r = 1 - r ^ 2 := by
  have hs2 : Real.sqrt (r ^ 2 - Real.sin θ ^ 2) ^ 2 = r ^ 2 - Real.sin θ ^ 2 :=
    Real.sq_sqrt h
  simp only [innerRoot, outerRoot]
  nlinarith [hs2, Real.sin_sq θ]

/-- **`0 < c` 的几何来源**：`c = cos θ`，而 `θ ≤ arcsin r < π/2` ⟹ `cos θ ≥ √(1-r²) > 0`。 -/
theorem cos_pos_of_arcHalfWidth {θ r : ℝ} (hr1 : r < 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ Real.arcsin r) : 0 < Real.cos θ := by
  have hr0 : 0 ≤ r := Real.arcsin_nonneg.mp (le_trans hθ0 hθ)
  have hcos : Real.cos (Real.arcsin r) ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hθ0
      (by linarith [Real.arcsin_le_pi_div_two r, Real.pi_pos]) hθ
  rw [Real.cos_arcsin] at hcos
  have hpos : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  linarith

/-- 内径向根为正（`ρ_- > 0`）：`ρ_- = cos θ - √(r²-sin²θ)`、`cos θ > 0`、
`cos²θ > r² - sin²θ ⟺ 1 > r²`。 -/
theorem innerRoot_pos {θ r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ Real.arcsin r) : 0 < innerRoot θ r := by
  have hcos : 0 < Real.cos θ := cos_pos_of_arcHalfWidth hr1 hθ0 hθ
  have hs2 : Real.sqrt (r ^ 2 - Real.sin θ ^ 2) ^ 2 = r ^ 2 - Real.sin θ ^ 2 :=
    Real.sq_sqrt (sin_sq_le_sq_of_le_arcsin' hr1.le hθ0 hθ)
  have hsnn : 0 ≤ Real.sqrt (r ^ 2 - Real.sin θ ^ 2) := Real.sqrt_nonneg _
  have hkey : Real.sqrt (r ^ 2 - Real.sin θ ^ 2) < Real.cos θ := by
    by_contra hc
    rw [not_lt] at hc
    have h2 : Real.cos θ ^ 2 ≤ Real.sqrt (r ^ 2 - Real.sin θ ^ 2) ^ 2 := by
      nlinarith [hsnn, hcos.le, hc]
    rw [hs2] at h2
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq θ, hr0, hr1]
  simp only [innerRoot]
  linarith

/-! ## 同一条实际弧 -/

/-- 一般事实：`‖x‖ = 1` 时，`‖x - ρu‖ ≤ r` 等价于半平面条件 `cos θ ≤ ⟪x,u⟫`，
只要 `1 + ρ² - r² = 2ρ cos θ`（这是两个径向根共有的代数关系）。 -/
theorem cap_iff_of_root {u x : Point} (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) {θ r ρ : ℝ}
    (hr0 : 0 ≤ r) (hρ : 0 < ρ) (hkey : 1 + ρ ^ 2 - r ^ 2 = 2 * ρ * Real.cos θ) :
    dist x (ρ • u) ≤ r ↔ Real.cos θ ≤ inner ℝ x u := by
  have hnorm : ‖ρ • u‖ ^ 2 = ρ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
  have hinner : inner ℝ x (ρ • u) = ρ * inner ℝ x u := by
    rw [real_inner_smul_right]
  rw [mem_sphere_closedBall_iff hr0 hx, hnorm, hinner, hkey]
  constructor <;> intro h <;> nlinarith

/-- **同一条实际弧（外根盘）**：外根盘在 `S¹` 上的交恰是半宽 `θ` 的弧 `{⟪x,u⟫ ≥ cos θ}`。 -/
theorem cap_outerRoot_iff {u x : Point} (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) {θ r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.arcsin r) :
    dist x (outerRoot θ r • u) ≤ r ↔ Real.cos θ ≤ inner ℝ x u := by
  have hcos : 0 < Real.cos θ := cos_pos_of_arcHalfWidth hr1 hθ0 hθ
  have hs2 : Real.sqrt (r ^ 2 - Real.sin θ ^ 2) ^ 2 = r ^ 2 - Real.sin θ ^ 2 :=
    Real.sq_sqrt (sin_sq_le_sq_of_le_arcsin' hr1.le hθ0 hθ)
  refine cap_iff_of_root hu hx hr0 (by
    simp only [outerRoot]; linarith [Real.sqrt_nonneg (r ^ 2 - Real.sin θ ^ 2)]) ?_
  simp only [outerRoot]
  nlinarith [hs2, Real.sin_sq θ]

/-- **同一条实际弧（内根盘）**：内根盘在 `S¹` 上的交是**同一条**弧。 -/
theorem cap_innerRoot_iff {u x : Point} (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) {θ r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.arcsin r) :
    dist x (innerRoot θ r • u) ≤ r ↔ Real.cos θ ≤ inner ℝ x u := by
  have hρ : 0 < innerRoot θ r := innerRoot_pos hr0 hr1 hθ0 hθ
  have hs2 : Real.sqrt (r ^ 2 - Real.sin θ ^ 2) ^ 2 = r ^ 2 - Real.sin θ ^ 2 :=
    Real.sq_sqrt (sin_sq_le_sq_of_le_arcsin' hr1.le hθ0 hθ)
  refine cap_iff_of_root hu hx hr0 hρ ?_
  simp only [innerRoot]
  nlinarith [hs2, Real.sin_sq θ]

/-! ## 组合定理：覆盖被保持 -/

/-- **组合定理（对应源文 §1 的 "Thus coverage and actual arcs are preserved"）**：
外径向根盘与内根盘有同一条实际弧（半宽 `θ`、半径 `r`），且外根盘落在 `D` 内的部分含于内根盘。
几何前提唯一：`0 ≤ r < 1`、`0 ≤ θ ≤ arcsin r`（后两者说明「半宽 `θ` 的实际弧」在半径 `r` 下可实现）。 -/
theorem dist_innerRoot_le_of_outerRoot {u x : Point} (hu : ‖u‖ = 1) {θ r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.arcsin r) (hx : ‖x‖ ≤ 1)
    (h : dist x (outerRoot θ r • u) ≤ r) : dist x (innerRoot θ r • u) ≤ r :=
  dist_inner_root_le (a := innerRoot θ r) (b := outerRoot θ r) (c := Real.cos θ) hu hr0 hr1
    (innerRoot_le_outerRoot θ r) (innerRoot_add_outerRoot θ r)
    (innerRoot_mul_outerRoot (sin_sq_le_sq_of_le_arcsin' hr1.le hθ0 hθ))
    (cos_pos_of_arcHalfWidth hr1 hθ0 hθ) hx h

/-- 最优中心情形 `θ = arcsin r`：两根重合，`ρ_- = ρ_+ = √(1-r²)`（此时替换平凡，无需移动盘）。 -/
theorem innerRoot_eq_outerRoot_of_eq_arcsin {θ r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hθ : θ = Real.arcsin r) : innerRoot θ r = outerRoot θ r := by
  have hsin : Real.sin θ = r := by
    rw [hθ]
    exact Real.sin_arcsin (by linarith) hr1.le
  have h0 : r ^ 2 - Real.sin θ ^ 2 = 0 := by rw [hsin]; ring
  simp only [innerRoot, outerRoot, h0, Real.sqrt_zero, add_zero, sub_zero]

end

/-! ## 可信基础 -/

#print axioms N11Formalization.innerRoot_le_outerRoot
#print axioms N11Formalization.innerRoot_add_outerRoot
#print axioms N11Formalization.innerRoot_mul_outerRoot
#print axioms N11Formalization.cos_pos_of_arcHalfWidth
#print axioms N11Formalization.innerRoot_pos
#print axioms N11Formalization.cap_outerRoot_iff
#print axioms N11Formalization.cap_innerRoot_iff
#print axioms N11Formalization.dist_innerRoot_le_of_outerRoot

end N11Formalization
