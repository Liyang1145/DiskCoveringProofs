import Mathlib
import N11Formalization.FlashLocalChart

/-!
# FlashLocal — 120 局部叶承重链 · 第六环：**三阶向量余项** `‖U(x) − U − v + (x²/2)U‖ ≤ q³/6`

Lead（2026-09-30，读 `RELATIVE-STRESS-BASIS.md` / `ANISOTROPIC-STRESS-REMAINDER.md` 后）：
真实消费者（C920：`mu=0.0018, tau0=734, tau=1468, B=0.495, A=0.00858, G=0.015363,
Ccross=0.0358, d=0.08, rho=0.01458`）需要的**不是**二阶 `w = δ − v` 界，而是**三阶**向量余项
`‖U(x) − U − v + (x²/2)U‖ ≤ q³/6`。

本件把它做成**无条件 kernel 定理**（闭形式，无积分）：

* **归约（旋转正交性，与第一环同款）**：三阶残差的平方和只依赖位移 `x`：
  `chartThirdSq a x = (cos x − 1 + x²/2)² + (x − sin x)²`；
* **标量核心**：`g(x) := x⁶/36 − (cos x − 1 + x²/2)² − (x − sin x)² >= 0`（**全实轴**，用偶性），
  因为 `g'(x) = x² * (sin x − x + x³/6)` 而 `sin x − x + x³/6 >= 0`（x ≥ 0），
  后者由 `h'(x) = cos x − 1 + x²/2 >= 0` 给出（**同一个** `Real.one_sub_sq_div_two_le_cos`）；
* ⇒ `chartThirdSq a x <= (x³/6)²`，即 `‖R‖ <= |x|³/6`（**ρ 之前的精确常数 1/6**）。

**与二阶的关系（口径）**：二阶件给 `‖δ − v‖ <= q²/2`；本件给
`‖δ − v + (x²/2)U‖ <= q³/6`。两者**不是**同一个量（本件多减了 `(x²/2)U` 项），
故不可互相替代：真实消费者要的是本件的三阶形。

**scope**：对任意实数 `a x` 无条件；不含 `Λ`、不含响应、不含 `H0`、不含任何图/叶。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Set

/-! ## 1. 标量辅助函数 `sin x − x + x³/6 >= 0`（x ≥ 0） -/

/-- `h(x) = sin x − x + x³/6`（三阶 Taylor 的"余项符号"函数）。 -/
def thirdAux (x : ℝ) : ℝ := Real.sin x - x + x ^ 3 / 6

theorem hasDerivAt_thirdAux (x : ℝ) :
    HasDerivAt thirdAux (Real.cos x - 1 + x ^ 2 / 2) x := by
  have hsin : HasDerivAt (fun y : ℝ => Real.sin y) (Real.cos x) x := Real.hasDerivAt_sin x
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hcube : HasDerivAt (fun y : ℝ => y ^ 3 / 6) (3 * x ^ 2 / 6) x := by
    have h := (hasDerivAt_pow 3 x).div_const 6
    simpa using h
  refine ((hsin.sub hid).add hcube).congr_deriv ?_
  ring

theorem thirdAux_deriv_nonneg (x : ℝ) : 0 ≤ deriv thirdAux x := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hd : deriv thirdAux x = Real.cos x - 1 + x ^ 2 / 2 := (hasDerivAt_thirdAux x).deriv
  rw [hd]
  linarith

/-- **`0 <= sin x − x + x³/6`（x ≥ 0）**。 -/
theorem thirdAux_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ thirdAux x := by
  have hcont : ContinuousOn thirdAux (Ici 0) :=
    fun y _ => (hasDerivAt_thirdAux y).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ thirdAux (interior (Ici 0)) :=
    fun y _ => (hasDerivAt_thirdAux y).differentiableAt.differentiableWithinAt
  have hderiv : ∀ y ∈ interior (Ici 0), 0 ≤ deriv thirdAux y :=
    fun y _ => thirdAux_deriv_nonneg y
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff hderiv
  have h0 : thirdAux 0 = 0 := by unfold thirdAux; norm_num
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  rwa [h0] at this

/-! ## 2. 标量核心 `g >= 0`（三阶残差平方的补式） -/

/-- `g(x) = x⁶/36 − (cos x − 1 + x²/2)² − (x − sin x)²`。 -/
def thirdRem (x : ℝ) : ℝ :=
  x ^ 6 / 36 - (Real.cos x - 1 + x ^ 2 / 2) ^ 2 - (x - Real.sin x) ^ 2

theorem hasDerivAt_cosAux (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos y - 1 + y ^ 2 / 2) (-Real.sin x + x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.cos y - 1) (-Real.sin x) x :=
    (Real.hasDerivAt_cos x).sub_const 1
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) (2 * x / 2) x := by
    have h := (hasDerivAt_pow 2 x).div_const 2
    simpa using h
  refine (h1.add h2).congr_deriv ?_
  ring

theorem hasDerivAt_sinAux (x : ℝ) :
    HasDerivAt (fun y : ℝ => y - Real.sin y) (1 - Real.cos x) x :=
  ((hasDerivAt_id x).sub (Real.hasDerivAt_sin x)).congr_deriv (by ring)

theorem hasDerivAt_thirdRem (x : ℝ) :
    HasDerivAt thirdRem (x ^ 2 * thirdAux x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 6 / 36) (6 * x ^ 5 / 36) x := by
    have h := (hasDerivAt_pow 6 x).div_const 36
    simpa using h
  have h2 : HasDerivAt (fun y : ℝ => (Real.cos y - 1 + y ^ 2 / 2) ^ 2)
      (2 * (Real.cos x - 1 + x ^ 2 / 2) ^ 1 * (-Real.sin x + x)) x :=
    (hasDerivAt_cosAux x).pow 2
  have h3 : HasDerivAt (fun y : ℝ => (y - Real.sin y) ^ 2)
      (2 * (x - Real.sin x) ^ 1 * (1 - Real.cos x)) x :=
    (hasDerivAt_sinAux x).pow 2
  refine (((h1.sub h2).sub h3)).congr_deriv ?_
  unfold thirdAux
  ring

theorem thirdRem_deriv_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ deriv thirdRem x := by
  have hd : deriv thirdRem x = x ^ 2 * thirdAux x := (hasDerivAt_thirdRem x).deriv
  rw [hd]
  exact mul_nonneg (sq_nonneg x) (thirdAux_nonneg hx.le)

/-- `g` 是**偶函数**。 -/
theorem thirdRem_neg (x : ℝ) : thirdRem (-x) = thirdRem x := by
  unfold thirdRem
  rw [Real.sin_neg, Real.cos_neg]
  ring

/-- **`g >= 0`（全实轴）**：三阶残差平方 ≤ `x⁶/36`。 -/
theorem thirdRem_nonneg (x : ℝ) : 0 ≤ thirdRem x := by
  have aux : ∀ x : ℝ, 0 ≤ x → 0 ≤ thirdRem x := by
    intro x hx
    have hcont : ContinuousOn thirdRem (Ici 0) :=
      fun y _ => (hasDerivAt_thirdRem y).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ thirdRem (interior (Ici 0)) :=
      fun y _ => (hasDerivAt_thirdRem y).differentiableAt.differentiableWithinAt
    have hderiv : ∀ y ∈ interior (Ici 0), 0 ≤ deriv thirdRem y := by
      intro y hy
      rw [interior_Ici] at hy
      exact thirdRem_deriv_nonneg hy
    have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff hderiv
    have h0 : thirdRem 0 = 0 := by unfold thirdRem; norm_num
    have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
    rwa [h0] at this
  rcases le_total 0 x with h | h
  · exact aux x h
  · rw [← thirdRem_neg x]
    exact aux (-x) (by linarith)

/-! ## 3. 三阶残差的平方和（旋转正交性 ⇒ 只依赖 `x`） -/

/-- 单位圆图的**三阶**残差平方：`‖u(a+x) − u(a) − x u'(a) + (x²/2)u(a)‖²`。 -/
def chartThirdSq (a x : ℝ) : ℝ :=
  (Real.cos (a + x) - Real.cos a + x * Real.sin a + (x ^ 2 / 2) * Real.cos a) ^ 2 +
    (Real.sin (a + x) - Real.sin a - x * Real.cos a + (x ^ 2 / 2) * Real.sin a) ^ 2

/-- 旋转正交性：三阶残差平方只依赖位移 `x`。 -/
theorem chartThirdSq_eq (a x : ℝ) :
    chartThirdSq a x = (Real.cos x - 1 + x ^ 2 / 2) ^ 2 + (x - Real.sin x) ^ 2 := by
  have h := Real.cos_sq_add_sin_sq a
  have hexp : chartThirdSq a x =
      (Real.cos a * (Real.cos x - 1 + x ^ 2 / 2) + Real.sin a * (x - Real.sin x)) ^ 2 +
        (Real.sin a * (Real.cos x - 1 + x ^ 2 / 2) - Real.cos a * (x - Real.sin x)) ^ 2 := by
    rw [chartThirdSq, Real.cos_add, Real.sin_add]
    ring
  rw [hexp]
  linear_combination ((Real.cos x - 1 + x ^ 2 / 2) ^ 2 + (x - Real.sin x) ^ 2) * h

/-- **主定理（无条件）**：`chartThirdSq a x <= (x³/6)²`，即 `‖R‖ <= |x|³/6`。 -/
theorem chartThirdSq_le (a x : ℝ) : chartThirdSq a x ≤ (x ^ 3 / 6) ^ 2 := by
  rw [chartThirdSq_eq]
  have h := thirdRem_nonneg x
  unfold thirdRem at h
  nlinarith [h]

/-- 范数形态：`‖R‖ <= |x|³/6`。 -/
theorem chartThird_norm_le (a x : ℝ) :
    Real.sqrt (chartThirdSq a x) ≤ |x| ^ 3 / 6 := by
  have h := chartThirdSq_le a x
  have hnn : 0 ≤ |x| ^ 3 / 6 := by positivity
  calc Real.sqrt (chartThirdSq a x) ≤ Real.sqrt ((x ^ 3 / 6) ^ 2) := Real.sqrt_le_sqrt h
    _ = |x ^ 3 / 6| := Real.sqrt_sq_eq_abs _
    _ = |x| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.thirdAux_nonneg
#print axioms N11Formalization.FlashLocal.thirdRem_nonneg
#print axioms N11Formalization.FlashLocal.chartThirdSq_eq
#print axioms N11Formalization.FlashLocal.chartThirdSq_le
#print axioms N11Formalization.FlashLocal.chartThird_norm_le
