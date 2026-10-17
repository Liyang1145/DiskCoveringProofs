/-
n=11 全局最优性形式化 —— 内根替换引理（`UNRESTRICTED-PROOF-ASSEMBLY` §1，kernel-checked）

源文原话：
> For each boundary disk replace its outer radial root by the inner root of the SAME actual arc
> and SAME r. If rho_- * rho_+ = 1 - r² and c = (rho_- + rho_+)/2, then at x=p.u <= c the inner
> distance is no larger; at x>=c, |p-rho_-u|² <= 1-2rho_-c+rho_-² = r². Thus coverage and actual
> arcs are preserved.

本文件给出精确陈述与证明，并**显式补上 Lead 陈述中缺失的前提 `0 < c`**：

* `dist_inner_root_le`：一般形式（含 `hcpos : 0 < c`）；
* `dist_inner_root_le_sqrt`：显式根形式（`a = c - √(c²-(1-r²))`, `b = c + √(c²-(1-r²))`）；
* `inner_root_lemma_false_without_pos_center`：**kernel-proved 反例**，说明 `0 < c` 不能删
  （无 `0 < c` 时 `a` 可为负，`s² - 2at + a² < 1 - 2ac + a²` 那一步的放缩方向反了，结论本身为假）。

零 `sorry`、零自定义 `axiom`。
-/
import Mathlib
import N11Formalization.Geometry.CapArc

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace N11Formalization

noncomputable section

/-! ## 一般形式 -/

/-- 前提 `0 < c` 下内根为正（`ab = 1-r² > 0` 说明两根同号，而 `a+b = 2c > 0` 说明同号为正）。 -/
theorem inner_root_pos {r a b c : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hab : a ≤ b)
    (hsum : a + b = 2 * c) (hprod : a * b = 1 - r ^ 2) (hcpos : 0 < c) : 0 < a := by
  have hpos : 0 < 1 - r ^ 2 := by nlinarith
  have ha0 : a ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hprod
    linarith
  rcases lt_trichotomy a 0 with h | h | h
  · have hb : b < 0 := by
      rcases lt_trichotomy b 0 with hb | hb | hb
      · exact hb
      · rw [hb, mul_zero] at hprod; linarith
      · nlinarith
    linarith
  · exact absurd h ha0
  · exact h

/-- **内根替换引理（一般形式）**：`a` 是内根（`a ≤ b`、`a+b = 2c`、`ab = 1-r²`、`0 < c`）时，
落在外根盘 `closedBall (b•u) r` 内的点 `x`（`‖x‖ ≤ 1`）也落在内根盘 `closedBall (a•u) r` 内。 -/
theorem dist_inner_root_le {u : Point} (hu : ‖u‖ = 1) {r a b c : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hab : a ≤ b) (hsum : a + b = 2 * c) (hprod : a * b = 1 - r ^ 2) (hcpos : 0 < c)
    {x : Point} (hx : ‖x‖ ≤ 1) (hxb : dist x (b • u) ≤ r) : dist x (a • u) ≤ r := by
  have ha_pos : 0 < a := inner_root_pos hr0 hr1 hab hsum hprod hcpos
  have hna : ‖x - a • u‖ ^ 2 = ‖x‖ ^ 2 - 2 * a * inner ℝ x u + a ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
    ring
  have hnb : ‖x - b • u‖ ^ 2 = ‖x‖ ^ 2 - 2 * b * inner ℝ x u + b ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs]
    ring
  have hxb' : ‖x - b • u‖ ≤ r := by rwa [dist_eq_norm] at hxb
  have hxb2 : ‖x - b • u‖ ^ 2 ≤ r ^ 2 := by
    nlinarith [norm_nonneg (x - b • u), hxb', hr0.le]
  by_cases ht : inner ℝ x u ≤ c
  · -- `t ≤ c`：内距离 ≤ 外距离
    have hle : ‖x - a • u‖ ^ 2 ≤ ‖x - b • u‖ ^ 2 := by
      rw [hna, hnb]
      nlinarith [ht, hab, hsum]
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x - a • u), le_trans hle hxb2, hr0.le]
  · -- `t > c`：用 `‖x‖ ≤ 1` 与 `a > 0` 直接压到 `r²`
    have ht' : c < inner ℝ x u := not_le.mp ht
    have hx1 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x, hx]
    have hstep : ‖x‖ ^ 2 - 2 * a * inner ℝ x u + a ^ 2 < 1 - 2 * a * c + a ^ 2 := by
      nlinarith [hx1, ha_pos, ht']
    have hval : 1 - 2 * a * c + a ^ 2 = r ^ 2 := by nlinarith [hsum, hprod]
    have hlt : ‖x - a • u‖ ^ 2 < r ^ 2 := by
      rw [hna]
      linarith
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x - a • u), hlt, hr0.le]

/-- **显式根形式**：`a = c - √(c²-(1-r²))`（内根）、`b = c + √(c²-(1-r²))`（外根）。 -/
theorem dist_inner_root_le_sqrt {u : Point} (hu : ‖u‖ = 1) {r c : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hcpos : 0 < c) (hdisc : 0 ≤ c ^ 2 - (1 - r ^ 2)) {x : Point} (hx : ‖x‖ ≤ 1)
    (hxb : dist x ((c + Real.sqrt (c ^ 2 - (1 - r ^ 2))) • u) ≤ r) :
    dist x ((c - Real.sqrt (c ^ 2 - (1 - r ^ 2))) • u) ≤ r := by
  have hs2 : Real.sqrt (c ^ 2 - (1 - r ^ 2)) ^ 2 = c ^ 2 - (1 - r ^ 2) := Real.sq_sqrt hdisc
  have hsnn : 0 ≤ Real.sqrt (c ^ 2 - (1 - r ^ 2)) := Real.sqrt_nonneg _
  have hab : c - Real.sqrt (c ^ 2 - (1 - r ^ 2)) ≤ c + Real.sqrt (c ^ 2 - (1 - r ^ 2)) := by
    linarith
  have hsum : c - Real.sqrt (c ^ 2 - (1 - r ^ 2)) + (c + Real.sqrt (c ^ 2 - (1 - r ^ 2)))
      = 2 * c := by ring
  have hprod : (c - Real.sqrt (c ^ 2 - (1 - r ^ 2))) * (c + Real.sqrt (c ^ 2 - (1 - r ^ 2)))
      = 1 - r ^ 2 := by nlinarith [hs2]
  exact dist_inner_root_le hu hr0 hr1 hab hsum hprod hcpos hx hxb

/-- **源文最直接的实例**：中心在单位圆周上的「边界盘」（`c₀ = u`，`‖u‖ = 1`）的径向根是
`ρ_± = 1 ± r`（故 `ρ_- · ρ_+ = 1 - r²`、`c = (ρ_-+ρ_+)/2 = 1 > 0`，**`0 < c` 自动满足**）。
于是：`D ∩ closedBall ((1+r)•u) r ⊆ closedBall ((1-r)•u) r`
（外切盘在 `D` 内的部分含于内切盘；半径 `r` 与 `S¹` 上的实际弧都不变，覆盖被保持）。 -/
theorem dist_inner_root_le_of_norm_eq_one {u : Point} (hu : ‖u‖ = 1) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) {x : Point} (hx : ‖x‖ ≤ 1) (h : dist x ((1 + r) • u) ≤ r) :
    dist x ((1 - r) • u) ≤ r :=
  dist_inner_root_le (a := 1 - r) (b := 1 + r) (c := 1) hu hr0 hr1 (by linarith) (by ring)
    (by ring) (by norm_num) hx h

/-! ## 反例：前提 `0 < c` 不能删 -/

theorem cons_norm_eq_abs (y : ℝ) : ‖(!₂[y, (0 : ℝ)] : Point)‖ = |y| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

theorem smul_cons_zero (z y : ℝ) :
    z • (!₂[y, (0 : ℝ)] : Point) = (!₂[z * y, (0 : ℝ)] : Point) := by
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp

theorem sub_cons_zero (y z : ℝ) :
    (!₂[y, (0 : ℝ)] : Point) - (!₂[z, (0 : ℝ)] : Point) = (!₂[y - z, (0 : ℝ)] : Point) := by
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;> simp

theorem dist_cons_smul_cons (y z : ℝ) :
    dist (!₂[y, (0 : ℝ)] : Point) (z • (!₂[(1 : ℝ), (0 : ℝ)] : Point)) = |y - z| := by
  rw [dist_eq_norm, smul_cons_zero, sub_cons_zero, mul_one, cons_norm_eq_abs]

/-- **反例（kernel-proved）**：去掉 `0 < c` 后内根替换引理为假。
取 `u = (1,0)`、`x = (-1/4, 0)`、`r = 1/2`、内根 `a = -1`、外根 `b = -3/4`、`c = -7/8`：
`ab = 3/4 = 1-r²`、`a+b = -7/4 = 2c`、`‖x‖ = 1/4 ≤ 1`、`dist x (b•u) = 1/2 = r`，
但 `dist x (a•u) = 3/4 > r`。故 `0 < c`（等价 `0 < a`）是必需前提。 -/
theorem inner_root_lemma_false_without_pos_center :
    ∃ (u x : Point) (r a b c : ℝ), ‖u‖ = 1 ∧ 0 < r ∧ r < 1 ∧ a ≤ b ∧ a + b = 2 * c ∧
      a * b = 1 - r ^ 2 ∧ ‖x‖ ≤ 1 ∧ dist x (b • u) ≤ r ∧ ¬ (dist x (a • u) ≤ r) := by
  refine ⟨(!₂[(1 : ℝ), (0 : ℝ)] : Point), (!₂[(-(1 : ℝ) / 4), (0 : ℝ)] : Point),
    (1 : ℝ) / 2, -1, -(3 : ℝ) / 4, -(7 : ℝ) / 8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cons_norm_eq_abs]; norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [cons_norm_eq_abs]; norm_num
  · rw [dist_cons_smul_cons]; norm_num
  · rw [dist_cons_smul_cons]; norm_num

end

/-! ## 可信基础 -/

#print axioms N11Formalization.inner_root_pos
#print axioms N11Formalization.dist_inner_root_le
#print axioms N11Formalization.dist_inner_root_le_sqrt
#print axioms N11Formalization.dist_inner_root_le_of_norm_eq_one
#print axioms N11Formalization.inner_root_lemma_false_without_pos_center

end N11Formalization
