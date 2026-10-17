/-
  N11Formalization.Interval.Taylor19C
  ===================================

  **第 2 步：`sin` 的 N = 19 阶 Taylor 余项不等式（`x₀ = 0`）**

  lead 更正后的桥（关键：前提是 **`UniqueDiffOn`**，不是邻域）：
  `iteratedDerivWithin_eq_iteratedDeriv : UniqueDiffOn 𝕜 s → ContDiffAt 𝕜 (↑n) f x → x ∈ s →
      iteratedDerivWithin n f s x = iteratedDeriv n f x`
  `uniqueDiffOn_Icc : a < b → UniqueDiffOn ℝ (Set.Icc a b)`
  ⟹ 取 `s = Icc 0 1` 时**端点也合法**（上一轮我误判为"端点失效"，已在 C1008 记录并作废）。

  配方（`taylor_mean_remainder_bound`，`a = 0, b = 1, n = 19, f = Real.sin, C = 1`）：
  `hC` 用桥 + C1004 的 `iteratedDeriv20_sin` + `Real.abs_sin_le_one`；结论
  `‖Real.sin x − taylorWithinEval Real.sin 19 (Icc 0 1) 0 x‖ ≤ 1 · (x−0)^20 / 19!`
  —— 注意 mathlib 的余项分母是 **`n!`（`19!`）**，即比精确 Lagrange 形式
  `|x|^20/20!` **宽 20 倍**；`1e-27` 量级的读数因此变成 `2e-26` 量级，仍远低于阈值 `9.956e-10`。

  作用域：`0 ≤ x ≤ 1`（`x < 0` 侧需多项式奇性或 `Real.sin_neg` 归约，**本文件未做**）。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval`。
-/
import Mathlib
import N11Formalization.Interval.Taylor19

namespace N11Formalization

namespace RatInterval

/-- `Icc 0 1` 是唯一可微集（供 `${Within}` 桥在**含端点**处使用）。 -/
theorem uniqueDiffOn_Icc01 : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) :=
  uniqueDiffOn_Icc (by norm_num)

/-- **`hC` 内容（可直接复用）**：`Icc 0 1` 上 20 阶 `Within` 导数的一直界 `≤ 1`。
这一点含端点成立，正是靠前提是 `UniqueDiffOn` 而非邻域。 -/
theorem iteratedDerivWithin20_sin_le_one :
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 20 Real.sin (Set.Icc (0 : ℝ) 1) y‖ ≤ 1 := by
  intro y hy
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc01
    (Real.contDiff_sin.contDiffAt) hy]
  rw [iteratedDeriv20_sin, Real.norm_eq_abs]
  exact Real.abs_sin_le_one y

/-- **第 2 步主定理（`sin`）**：`x ∈ [0,1]` 时
`‖Real.sin x − taylorWithinEval Real.sin 19 (Icc 0 1) 0 x‖ ≤ x^20 / 19!`。
（mathlib 的口径：分母是 `n! = 19!`；比 Lagrange 精确形式宽 20 倍。） -/
theorem sin_taylor19_bound {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖Real.sin x - taylorWithinEval Real.sin 19 (Set.Icc (0 : ℝ) 1) 0 x‖
      ≤ x ^ 20 / Nat.factorial 19 := by
  have h := taylor_mean_remainder_bound (a := (0 : ℝ)) (b := (1 : ℝ)) (C := (1 : ℝ))
    (n := 19) (x := x) (by norm_num) Real.contDiff_sin.contDiffOn hx
    iteratedDerivWithin20_sin_le_one
  have h' : ‖Real.sin x - taylorWithinEval Real.sin 19 (Set.Icc (0 : ℝ) 1) 0 x‖
      ≤ 1 * (x - 0) ^ (19 + 1) / Nat.factorial 19 := h
  rw [sub_zero, one_mul] at h'
  exact h'

/-- **第 2 步的 `cos` 侧（同款机器，阶 20）**：`x ∈ [0,1]` 时
`‖Real.cos x − taylorWithinEval Real.cos 20 (Icc 0 1) 0 x‖ ≤ x^21 / 20!`。 -/
theorem iteratedDerivWithin21_cos_le_one :
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 21 Real.cos (Set.Icc (0 : ℝ) 1) y‖ ≤ 1 := by
  intro y hy
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc01
    (Real.contDiff_cos.contDiffAt) hy]
  rw [iteratedDeriv21_cos, Pi.neg_apply, Real.norm_eq_abs, abs_neg]
  exact Real.abs_sin_le_one y

theorem cos_taylor20_bound {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖Real.cos x - taylorWithinEval Real.cos 20 (Set.Icc (0 : ℝ) 1) 0 x‖
      ≤ x ^ 21 / Nat.factorial 20 := by
  have h := taylor_mean_remainder_bound (a := (0 : ℝ)) (b := (1 : ℝ)) (C := (1 : ℝ))
    (n := 20) (x := x) (by norm_num) Real.contDiff_cos.contDiffOn hx
    iteratedDerivWithin21_cos_le_one
  have h' : ‖Real.cos x - taylorWithinEval Real.cos 20 (Set.Icc (0 : ℝ) 1) 0 x‖
      ≤ 1 * (x - 0) ^ (20 + 1) / Nat.factorial 20 := h
  rw [sub_zero, one_mul] at h'
  exact h'

end RatInterval

end N11Formalization

