import Mathlib
import N11Formalization.Geometry.ArcCovering

/-!
# FlashLocal — 120 局部叶 (local leaves) 承重链 · 第一环：单位圆图的**精确二阶展开**

对象与口径（source，非本文件自创）：
`team-current/lead/ADAPTIVE-STRESS-FINITE-REMAINDER.md` 第 20 行（**exact integral Taylor bounds**）：
`delta_i = U_i(x) - U0_i`, `v_i = J U0_i x_i`, `w = delta - v` (x8=0)，要求
`||delta||_F <= q`, `||v||_F = q`, **`||w||_F <= q^2/2`**，显式理由是
`w_i = x_i^2 ∫_0^1 (1-s) U_i''(s x_i) ds` 且 `|U_i''| = 1`，并强调
**"This holds for either sign of x_i and is not an asymptotic Taylor truncation."**

本文件把该环做成**无条件 kernel 定理**。分两层：

## 第一层 `chartResidualSq*` —— 标量闭形式

对 `u(t) = (cos t, sin t)` 与锚点角 `a`、位移 `x`，
`||u(a+x) - u(a) - x u'(a)||^2 = 2 - 2 cos x + x^2 - 2 x sin x = chartResidualSq a x`，
且 `chartResidualSq a x <= (x^2/2)^2`，对 `x` 的**两种符号**都成立（`chartRem_neg` 是关键那一步）。

证明链条（全部初等）：
1. `chartResidualSq_eq`：用 `cos_add`/`sin_add` 与 `cos^2+sin^2=1` 把残差化为
   `(cos x - 1)^2 + (x - sin x)^2`（**旋转正交性**——不是逐分量三角不等式）。
2. `chartRem_nonneg`：`h(x) := x^4/4 - x^2 + 2x sin x + 2cos x - 2 >= 0`；
   `h(0)=0`，`h'(x) = x * (x^2 - 2(1 - cos x))`，而 `x^2 - 2(1-cos x) >= 0` 由
   `Real.one_sub_sq_div_two_le_cos` 给出 ⇒ `h'` 的符号 = `x` 的符号 ⇒ 分两半轴单调，
   再由**偶性** `chartRem_neg` 合成全轴结论。

## 第二层 `anchor*` —— **真实 `Point` / `Fin 9` 圈映射**上的 Frobenius 包

`q^2 := ∑ i, x i ^ 2`（**2-范数**，逐字对应源的 `q = ||x||`）。
- `anchorDelta_frob_le`   : `∑ i, ‖delta_i‖^2 <= q^2`（弦 ≤ 弧；`delta_i` 是 `Point`）
- `anchorLin_frob_eq`     : `∑ i, ‖v_i‖^2 = q^2`（`v_i = x_i • tangent`，等号）
- `anchorRemainder_frob_le`: `∑ i, ‖w_i‖^2 <= (q^2)^2 / 4`，即 `||w||_F <= q^2/2`

第三式的常数**必须**走 `∑ x_i^4 <= (∑ x_i^2)^2`（`sum_four_le_sq_sum`，常数 1）；
**不得**用 `∑|x_i|` 型累加换常数（那会把右端放大 `n` 倍）。

**scope（精确）**：解析引理，对**任意** `θ x : Fin 9 → ℝ` 成立；无条件、无图数据、
无 45 边/20 自由节点身份、无 `hH`、无盒数据、无 stress/权重。它是局部叶链中
`w = delta - v` 的**唯一非线性输入**。
常数 `1/2` **不可改进为 `1/4`**（`chartResidualSq_half_control`，kernel 反例，显式点带 π）。
-/

namespace N11Formalization.FlashLocal

open Set

noncomputable section

/-! ## 第一层：标量闭形式 -/

/-- 单位圆图的二阶残差平方：`||u(a+x) - u(a) - x u'(a)||^2`（`u(t)=(cos t, sin t)`）。 -/
def chartResidualSq (a x : ℝ) : ℝ :=
  (Real.cos (a + x) - Real.cos a + x * Real.sin a) ^ 2 +
    (Real.sin (a + x) - Real.sin a - x * Real.cos a) ^ 2

/-- 残差只依赖位移 `x`：旋转正交性。 -/
theorem chartResidualSq_eq (a x : ℝ) :
    chartResidualSq a x = (Real.cos x - 1) ^ 2 + (x - Real.sin x) ^ 2 := by
  have h := Real.cos_sq_add_sin_sq a
  have hexp : chartResidualSq a x =
      (Real.cos a * (Real.cos x - 1) + Real.sin a * (x - Real.sin x)) ^ 2 +
        (Real.sin a * (Real.cos x - 1) - Real.cos a * (x - Real.sin x)) ^ 2 := by
    rw [chartResidualSq, Real.cos_add, Real.sin_add]
    ring
  rw [hexp]
  linear_combination ((Real.cos x - 1) ^ 2 + (x - Real.sin x) ^ 2) * h

/-- 残差平方的闭形式：`||w||^2 = 2 - 2cos x + x^2 - 2x sin x`（全轴、两种符号）。 -/
theorem chartResidualSq_eq_closed (a x : ℝ) :
    chartResidualSq a x = 2 - 2 * Real.cos x + x ^ 2 - 2 * x * Real.sin x := by
  have h := Real.cos_sq_add_sin_sq x
  rw [chartResidualSq_eq]
  linear_combination h

/-- 解析核心函数的**组合子形态**（专为 `HasDerivAt` 组合的零 convert 装配而设）。 -/
def chartComb : ℝ → ℝ := ((fun y : ℝ => y ^ 4 / 4) - (fun y : ℝ => y ^ 2)) +
    ((fun y : ℝ => 2 * id y) * Real.sin) + (fun y : ℝ => 2 * Real.cos y)

/-- 解析核心 `h(x) = ||w||^2 - (x^2/2)^2` 的补式。 -/
def chartRem (x : ℝ) : ℝ := chartComb x - 2

/-- `chartComb` 的标量读法。 -/
theorem chartComb_eq_scalar :
    chartComb = fun y : ℝ => y ^ 4 / 4 - y ^ 2 + 2 * y * Real.sin y + 2 * Real.cos y := by
  funext y
  simp only [chartComb, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]

/-- `chartRem` 的标量读法（下游证明都走这一条）。 -/
theorem chartRem_eq_scalar (x : ℝ) :
    chartRem x = x ^ 4 / 4 - x ^ 2 + 2 * x * Real.sin x + 2 * Real.cos x - 2 := by
  rw [chartRem, chartComb_eq_scalar]

/-- `d/dx chartComb = x * (x^2 - 2(1 - cos x))`。 -/
theorem hasDerivAt_chartComb (x : ℝ) :
    HasDerivAt chartComb (x * (x ^ 2 - 2 * (1 - Real.cos x))) x := by
  have h₁ : HasDerivAt (fun y : ℝ => y ^ 4 / 4) (x ^ 3) x := by
    refine ((hasDerivAt_pow 4 x).div_const 4).congr_deriv ?_
    norm_num
  have h₂ : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    refine (hasDerivAt_pow 2 x).congr_deriv ?_
    norm_num
  have h₃ : HasDerivAt ((fun y : ℝ => 2 * id y) * Real.sin)
      (2 * Real.sin x + 2 * x * Real.cos x) x := by
    have h := ((hasDerivAt_id x).const_mul (2 : ℝ)).mul (Real.hasDerivAt_sin x)
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have h₄ : HasDerivAt (fun y : ℝ => 2 * Real.cos y) (2 * -Real.sin x) x :=
    (Real.hasDerivAt_cos x).const_mul (2 : ℝ)
  have hsum := ((h₁.sub h₂).add h₃).add h₄
  rw [chartComb]
  exact hsum.congr_deriv (by ring)

/-- `d/dx chartRem = x * (x^2 - 2(1 - cos x))`（少一个常数 `2`，导数不变）。 -/
theorem hasDerivAt_chartRem (x : ℝ) :
    HasDerivAt chartRem (x * (x ^ 2 - 2 * (1 - Real.cos x))) x :=
  (hasDerivAt_chartComb x).sub_const 2

/-- `h` 是**偶函数**（`x` 两种符号都成立的那一步，不是对称性假设）。 -/
theorem chartRem_neg (x : ℝ) : chartRem (-x) = chartRem x := by
  rw [chartRem_eq_scalar, chartRem_eq_scalar, Real.sin_neg, Real.cos_neg]
  ring

/-- `h` 的导数在正半轴非负（由 `cos x >= 1 - x^2/2`）。 -/
theorem chartRem_deriv_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ deriv chartRem x := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hd : deriv chartRem x = x * (x ^ 2 - 2 * (1 - Real.cos x)) :=
    (hasDerivAt_chartRem x).deriv
  rw [hd]
  refine mul_nonneg hx.le ?_
  linarith

/-- `h >= 0` 在非负半轴上。 -/
theorem chartRem_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ chartRem x := by
  have hcont : ContinuousOn chartRem (Ici 0) :=
    fun y _ => (hasDerivAt_chartRem y).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ chartRem (interior (Ici 0)) :=
    fun y _ => (hasDerivAt_chartRem y).differentiableAt.differentiableWithinAt
  have hderiv : ∀ y ∈ interior (Ici 0), 0 ≤ deriv chartRem y := by
    intro y hy
    rw [interior_Ici] at hy
    exact chartRem_deriv_nonneg hy
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff hderiv
  have h0 : chartRem 0 = 0 := by rw [chartRem_eq_scalar]; norm_num
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  rwa [h0] at this

/-- **`h >= 0`（全实轴）**：单位圆图二阶残差 ≤ `(x^2/2)^2` 的解析核心。 -/
theorem chartRem_nonneg (x : ℝ) : 0 ≤ chartRem x := by
  rcases le_total 0 x with h | h
  · exact chartRem_nonneg_of_nonneg h
  · rw [← chartRem_neg x]
    exact chartRem_nonneg_of_nonneg (by linarith)

/-- **主定理（无条件）**：单位圆图的二阶展开残差 ≤ `(x^2/2)^2`，两种符号都成立。 -/
theorem chartResidualSq_le (a x : ℝ) : chartResidualSq a x ≤ (x ^ 2 / 2) ^ 2 := by
  rw [chartResidualSq_eq_closed]
  have h := chartRem_nonneg x
  rw [chartRem_eq_scalar] at h
  nlinarith [h]

/-- 消费者形态：残差的欧氏范数 ≤ `x^2/2`（供 `delta`/`v`/`w` 分解直接引用）。 -/
theorem chartResidual_norm_le (a x : ℝ) :
    Real.sqrt (chartResidualSq a x) ≤ x ^ 2 / 2 := by
  have h := chartResidualSq_le a x
  calc Real.sqrt (chartResidualSq a x) ≤ Real.sqrt ((x ^ 2 / 2) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = |x ^ 2 / 2| := Real.sqrt_sq_eq_abs _
    _ = x ^ 2 / 2 := abs_of_nonneg (by positivity)

/-- 逐坐标版本（源文档写的 `|w_i| <= x_i^2/2`）：每个分量都被 `x^2/2` 控制。 -/
theorem chartResidual_coord_le (a x : ℝ) :
    |Real.cos (a + x) - Real.cos a + x * Real.sin a| ≤ x ^ 2 / 2 ∧
      |Real.sin (a + x) - Real.sin a - x * Real.cos a| ≤ x ^ 2 / 2 := by
  have hle := chartResidualSq_le a x
  have hc : 0 ≤ x ^ 2 / 2 := by positivity
  have h1 : (Real.cos (a + x) - Real.cos a + x * Real.sin a) ^ 2 ≤ (x ^ 2 / 2) ^ 2 := by
    have hsub : (Real.cos (a + x) - Real.cos a + x * Real.sin a) ^ 2 ≤ chartResidualSq a x := by
      rw [chartResidualSq]
      nlinarith [sq_nonneg (Real.sin (a + x) - Real.sin a - x * Real.cos a)]
    linarith
  have h2 : (Real.sin (a + x) - Real.sin a - x * Real.cos a) ^ 2 ≤ (x ^ 2 / 2) ^ 2 := by
    have hsub : (Real.sin (a + x) - Real.sin a - x * Real.cos a) ^ 2 ≤ chartResidualSq a x := by
      rw [chartResidualSq]
      nlinarith [sq_nonneg (Real.cos (a + x) - Real.cos a + x * Real.sin a)]
    linarith
  exact ⟨abs_le_of_sq_le_sq h1 hc, abs_le_of_sq_le_sq h2 hc⟩

/-- **判别力对照（kernel 反例）**：常数 `1/2` 不可改进为 `1/4`。
在 `a = 0, x = pi/2` 处残差平方 `= 2 - pi + pi^2/4`，而 `(x^2/4)^2 = pi^4/256`。 -/
theorem chartResidualSq_half_control :
    ¬ (chartResidualSq 0 (Real.pi / 2) ≤ ((Real.pi / 2) ^ 2 / 4) ^ 2) := by
  rw [chartResidualSq_eq_closed, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring_nf
  intro h
  have h2 : Real.pi ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have h4 : Real.pi ^ 4 < 256 := by nlinarith [h2, Real.pi_pos]
  nlinarith [h4, h, sq_nonneg (Real.pi - 2)]

/-! ## 第二层：真实 `Point` / `Fin 9` 圈映射上的 Frobenius 包 -/

/-- 单位圆切向（`u'(t) = (-sin t, cos t)`），即源的 `v_i` 方向。 -/
def circleTangent (t : ℝ) : Point := !₂[-Real.sin t, Real.cos t]

theorem circleTangent_apply_zero (t : ℝ) : (circleTangent t).ofLp 0 = -Real.sin t := by
  simp [circleTangent]

theorem circleTangent_apply_one (t : ℝ) : (circleTangent t).ofLp 1 = Real.cos t := by
  simp [circleTangent]

/-- `Point` 的 norm 平方 = 两坐标平方和（`Fin 2` 版）。 -/
theorem norm_sq_two (p : Point) : ‖p‖ ^ 2 = p.ofLp 0 ^ 2 + p.ofLp 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs]

/-- 切向就是平移 π/2 后的圈点：`u'(t) = u(t + pi/2)`。 -/
theorem circleTangent_eq_circleMap (t : ℝ) :
    circleTangent t = circleMap (t + Real.pi / 2) := by
  refine PiLp.ext (fun i => ?_)
  fin_cases i <;>
    simp [circleTangent, circleMap, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]

/-- 切向是单位向量。 -/
theorem circleTangent_norm (t : ℝ) : ‖circleTangent t‖ = 1 := by
  rw [circleTangent_eq_circleMap, circleMap_norm]

/-- **标量 ↔ `Point` 桥**：`Point` 上的残差范数平方 = 第一层的 `chartResidualSq`。 -/
theorem chartResidualSq_eq_pointNorm (a x : ℝ) :
    ‖circleMap (a + x) - circleMap a - x • circleTangent a‖ ^ 2 = chartResidualSq a x := by
  rw [norm_sq_two]
  simp only [PiLp.sub_apply, PiLp.smul_apply, circleMap_apply_zero, circleMap_apply_one,
    circleTangent_apply_zero, circleTangent_apply_one, chartResidualSq]
  ring

/-- 弦长平方的闭形式：`||circleMap (a+x) - circleMap a||^2 = 2 - 2cos x`。 -/
theorem chordSq_eq_closed (a x : ℝ) :
    ‖circleMap (a + x) - circleMap a‖ ^ 2 = 2 - 2 * Real.cos x := by
  have h := Real.cos_sq_add_sin_sq a
  have hx := Real.cos_sq_add_sin_sq x
  rw [norm_sq_two]
  simp only [PiLp.sub_apply, circleMap_apply_zero, circleMap_apply_one]
  rw [Real.cos_add, Real.sin_add]
  linear_combination (2 - 2 * Real.cos x) * h + (Real.cos a ^ 2 + Real.sin a ^ 2) * hx

/-- 弦长平方 ≤ 弧长平方：`||delta_i||^2 = 2 - 2cos x <= x^2`。 -/
theorem chordSq_le (a x : ℝ) : ‖circleMap (a + x) - circleMap a‖ ^ 2 ≤ x ^ 2 := by
  rw [chordSq_eq_closed]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  linarith

/-- **`sum x_i^4 <= (sum x_i^2)^2`**：第三式常数为 `1` 的那一步（**不是** L1 累加）。 -/
theorem sum_four_le_sq_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ∑ i, x i ^ 4 ≤ (∑ i, x i ^ 2) ^ 2 := by
  have h : ∀ i, x i ^ 4 ≤ (∑ j, x j ^ 2) * x i ^ 2 := by
    intro i
    have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    calc x i ^ 4 = x i ^ 2 * x i ^ 2 := by ring
      _ ≤ (∑ j, x j ^ 2) * x i ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  calc ∑ i, x i ^ 4 ≤ ∑ i, (∑ j, x j ^ 2) * x i ^ 2 := Finset.sum_le_sum (fun i _ => h i)
    _ = (∑ j, x j ^ 2) * ∑ i, x i ^ 2 := by rw [Finset.mul_sum]
    _ = (∑ i, x i ^ 2) ^ 2 := by ring

/-- **`||delta||_F <= q`**（`q^2 = sum x_i^2`）：真实 `Point` 上的 9 锚残差。 -/
theorem anchorDelta_frob_le (θ x : Fin 9 → ℝ) :
    ∑ i, ‖circleMap (θ i + x i) - circleMap (θ i)‖ ^ 2 ≤ ∑ i, x i ^ 2 :=
  Finset.sum_le_sum (fun i _ => chordSq_le (θ i) (x i))

/-- **`||v||_F = q`（等号）**：`v_i = x_i • tangent(θ_i)`。 -/
theorem anchorLin_frob_eq (θ x : Fin 9 → ℝ) :
    ∑ i, ‖x i • circleTangent (θ i)‖ ^ 2 = ∑ i, x i ^ 2 := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [norm_smul, circleTangent_norm, mul_one, Real.norm_eq_abs, sq_abs]

/-- **`||w||_F <= q^2/2`**（核心式）：`w_i = delta_i - v_i`。 -/
theorem anchorRemainder_frob_le (θ x : Fin 9 → ℝ) :
    ∑ i, ‖(circleMap (θ i + x i) - circleMap (θ i)) - x i • circleTangent (θ i)‖ ^ 2
      ≤ (∑ i, x i ^ 2) ^ 2 / 4 := by
  have h : ∀ i, ‖(circleMap (θ i + x i) - circleMap (θ i)) - x i • circleTangent (θ i)‖ ^ 2
      ≤ (x i ^ 2 / 2) ^ 2 := by
    intro i
    rw [chartResidualSq_eq_pointNorm]
    exact chartResidualSq_le (θ i) (x i)
  calc ∑ i, ‖(circleMap (θ i + x i) - circleMap (θ i)) - x i • circleTangent (θ i)‖ ^ 2
      ≤ ∑ i, (x i ^ 2 / 2) ^ 2 := Finset.sum_le_sum (fun i _ => h i)
    _ = ∑ i, x i ^ 4 / 4 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ = (∑ i, x i ^ 4) / 4 := by rw [Finset.sum_div]
    _ ≤ (∑ i, x i ^ 2) ^ 2 / 4 := by linarith [sum_four_le_sq_sum x]

/-- 范数形态：`||w||_F <= q^2/2`，`q = sqrt (sum x_i^2)`。 -/
theorem anchorRemainder_frob_norm_le (θ x : Fin 9 → ℝ) :
    Real.sqrt (∑ i, ‖(circleMap (θ i + x i) - circleMap (θ i)) - x i • circleTangent (θ i)‖ ^ 2)
      ≤ (∑ i, x i ^ 2) / 2 := by
  have h := anchorRemainder_frob_le θ x
  have hq : 0 ≤ (∑ i, x i ^ 2) / 2 := by positivity
  have hs : ∑ i, ‖(circleMap (θ i + x i) - circleMap (θ i))
      - x i • circleTangent (θ i)‖ ^ 2 ≤ ((∑ i, x i ^ 2) / 2) ^ 2 := by
    have : ((∑ i, x i ^ 2) / 2) ^ 2 = (∑ i, x i ^ 2) ^ 2 / 4 := by ring
    rw [this]
    exact h
  calc Real.sqrt (∑ i, ‖(circleMap (θ i + x i) - circleMap (θ i))
        - x i • circleTangent (θ i)‖ ^ 2)
      ≤ Real.sqrt (((∑ i, x i ^ 2) / 2) ^ 2) := Real.sqrt_le_sqrt hs
    _ = |(∑ i, x i ^ 2) / 2| := Real.sqrt_sq_eq_abs _
    _ = (∑ i, x i ^ 2) / 2 := abs_of_nonneg hq

end

end N11Formalization.FlashLocal

#check @N11Formalization.FlashLocal.anchorRemainder_frob_le
#check @N11Formalization.FlashLocal.chartResidualSq_le
#print axioms N11Formalization.FlashLocal.anchorRemainder_frob_le
#print axioms N11Formalization.FlashLocal.anchorDelta_frob_le
#print axioms N11Formalization.FlashLocal.anchorLin_frob_eq
#print axioms N11Formalization.FlashLocal.chartRem_nonneg
#print axioms N11Formalization.FlashLocal.chartResidualSq_half_control
