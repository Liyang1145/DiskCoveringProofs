/-
  N11Formalization.Interval.Taylor19
  ==================================

  **高阶 Taylor 界（N = 19 固定阶）—— 第 1 步：`iteratedDeriv` 的 4-周期循环**

  lead 收窄后的范围：只做 `N = 19` 固定阶的内核界（不做参数化通用阶、不改窗口算子）。

  本文件交付**第 1 步（唯一的新数学工作）**：
  * 三个**函数级**一阶导数等式（mathlib 只给点级）：`deriv_cos_fn`、`deriv_neg_sin_fn`、`deriv_neg_cos_fn`；
  * `iteratedDeriv_sin_cyc : ∀ m, (iteratedDeriv (4m) sin = sin) ∧ (4m+1 → cos) ∧ (4m+2 → −sin) ∧ (4m+3 → −cos)`
    —— `Nat` 归纳；归约步用探针确认的 `iteratedDeriv_succ`
    （**实测其形状是 `iteratedDeriv (n+1) f = deriv (iteratedDeriv n f)`**，即 `deriv` 在外层，
    故不能"向内搬运 deriv"，只能按 `4m+3 → 4m+4` 的顺序把导数作用到 IH 上）；
  * `iteratedDeriv20_sin : iteratedDeriv 20 Real.sin = Real.sin`（`20 = 4·5`）；
  * `abs_iteratedDeriv20_sin_le_one`：`|iteratedDeriv 20 Real.sin x| ≤ 1`（Taylor–Lagrange 余项所需）；
  * `cos` 侧同款：`iteratedDeriv_cos_cyc`、`iteratedDeriv21_cos = -Real.sin`、`abs_iteratedDeriv21_cos_le_one`。

  探针（`evidence/interval/_probe_taylor2.out.txt`）确认存在：`iteratedDeriv`、`iteratedDeriv_succ`、
  `iteratedDeriv_zero`、`iteratedDeriv_neg`、`Real.deriv_sin`（函数级）、`Real.deriv_cos`（点级）、
  `Real.abs_sin_le_one`、`Real.abs_cos_le_one`、`Real.contDiff_sin`、`Real.differentiable_sin`、
  `taylor_mean_remainder_lagrange`、`taylorWithinEval`、`iteratedDerivWithin`。
  **注意**：`deriv_neg` 在 mathlib 里是 `deriv Neg.neg x = -1`（**不是** `deriv (-f) = -deriv f`），
  故负号情形一律走 `HasDerivAt.neg` + `HasDerivAt.deriv`。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval`。
-/
import Mathlib
import N11Formalization.Interval.Trig

namespace N11Formalization

namespace RatInterval

/-! ## 1. 函数级的一阶导数等式 -/

/-- `deriv Real.cos = -Real.sin`（函数级；`Real.deriv_cos` 是点级，用 `funext` 提升）。 -/
theorem deriv_cos_fn : deriv Real.cos = -Real.sin := by
  funext x
  exact Real.deriv_cos

/-- `deriv (fun x => -Real.sin x) = fun x => -Real.cos x`。 -/
theorem deriv_neg_sin_fn : deriv (-Real.sin) = -Real.cos := by
  funext x
  exact (Real.hasDerivAt_sin x).neg.deriv

/-- `deriv (fun x => -Real.cos x) = Real.sin`。 -/
theorem deriv_neg_cos_fn : deriv (-Real.cos) = Real.sin := by
  funext x
  have h := (Real.hasDerivAt_cos x).neg.deriv
  rw [h, neg_neg]

/-! ## 2. `sin` 的 4-周期循环（`Nat` 归纳） -/

/-- **`sin` 的四态循环**：`iteratedDeriv` 沿 `sin → cos → −sin → −cos → sin` 循环。
归约步用 `iteratedDeriv (n+1) f = deriv (iteratedDeriv n f)`（`iteratedDeriv_succ` 实测形状）。 -/
theorem iteratedDeriv_sin_cyc : ∀ m : ℕ,
    iteratedDeriv (4 * m) Real.sin = Real.sin ∧
      iteratedDeriv (4 * m + 1) Real.sin = Real.cos ∧
      iteratedDeriv (4 * m + 2) Real.sin = -Real.sin ∧
      iteratedDeriv (4 * m + 3) Real.sin = -Real.cos := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [iteratedDeriv_zero]
    · rw [iteratedDeriv_succ, iteratedDeriv_zero, Real.deriv_sin]
    · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, Real.deriv_sin, deriv_cos_fn]
    · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
        Real.deriv_sin, deriv_cos_fn, deriv_neg_sin_fn]
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    have n0 : iteratedDeriv (4 * (m + 1)) Real.sin = Real.sin := by
      rw [show 4 * (m + 1) = (4 * m + 3) + 1 from by ring, iteratedDeriv_succ, h3,
        deriv_neg_cos_fn]
    have n1 : iteratedDeriv (4 * (m + 1) + 1) Real.sin = Real.cos := by
      rw [show 4 * (m + 1) + 1 = 4 * (m + 1) + 1 from rfl, iteratedDeriv_succ, n0,
        Real.deriv_sin]
    have n2 : iteratedDeriv (4 * (m + 1) + 2) Real.sin = -Real.sin := by
      rw [show 4 * (m + 1) + 2 = (4 * (m + 1) + 1) + 1 from by ring, iteratedDeriv_succ, n1,
        deriv_cos_fn]
    have n3 : iteratedDeriv (4 * (m + 1) + 3) Real.sin = -Real.cos := by
      rw [show 4 * (m + 1) + 3 = (4 * (m + 1) + 2) + 1 from by ring, iteratedDeriv_succ, n2,
        deriv_neg_sin_fn]
    exact ⟨n0, n1, n2, n3⟩

/-- **第 1 步主定理**：`iteratedDeriv 20 Real.sin = Real.sin`（`20 = 4·5`）。 -/
theorem iteratedDeriv20_sin : iteratedDeriv 20 Real.sin = Real.sin :=
  (iteratedDeriv_sin_cyc 5).1

/-- **推论（Taylor 余项所需的一致导数界）**：`|iteratedDeriv 20 Real.sin x| ≤ 1`。 -/
theorem abs_iteratedDeriv20_sin_le_one (x : ℝ) : |iteratedDeriv 20 Real.sin x| ≤ 1 := by
  rw [iteratedDeriv20_sin]
  exact Real.abs_sin_le_one x

/-! ## 3. `cos` 侧同款 -/

/-- **`cos` 的四态循环**：`cos → −sin → −cos → sin → cos`。 -/
theorem iteratedDeriv_cos_cyc : ∀ m : ℕ,
    iteratedDeriv (4 * m) Real.cos = Real.cos ∧
      iteratedDeriv (4 * m + 1) Real.cos = -Real.sin ∧
      iteratedDeriv (4 * m + 2) Real.cos = -Real.cos ∧
      iteratedDeriv (4 * m + 3) Real.cos = Real.sin := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [iteratedDeriv_zero]
    · rw [iteratedDeriv_succ, iteratedDeriv_zero, deriv_cos_fn]
    · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, deriv_cos_fn, deriv_neg_sin_fn]
    · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
        deriv_cos_fn, deriv_neg_sin_fn, deriv_neg_cos_fn]
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    have n0 : iteratedDeriv (4 * (m + 1)) Real.cos = Real.cos := by
      rw [show 4 * (m + 1) = (4 * m + 3) + 1 from by ring, iteratedDeriv_succ, h3, Real.deriv_sin]
    have n1 : iteratedDeriv (4 * (m + 1) + 1) Real.cos = -Real.sin := by
      rw [iteratedDeriv_succ, n0, deriv_cos_fn]
    have n2 : iteratedDeriv (4 * (m + 1) + 2) Real.cos = -Real.cos := by
      rw [show 4 * (m + 1) + 2 = (4 * (m + 1) + 1) + 1 from by ring, iteratedDeriv_succ, n1,
        deriv_neg_sin_fn]
    have n3 : iteratedDeriv (4 * (m + 1) + 3) Real.cos = Real.sin := by
      rw [show 4 * (m + 1) + 3 = (4 * (m + 1) + 2) + 1 from by ring, iteratedDeriv_succ, n2,
        deriv_neg_cos_fn]
    exact ⟨n0, n1, n2, n3⟩

/-- **`cos` 侧的阶 21 读数**：`iteratedDeriv 21 Real.cos = -Real.sin`（`21 = 4·5+1`）。 -/
theorem iteratedDeriv21_cos : iteratedDeriv 21 Real.cos = -Real.sin :=
  (iteratedDeriv_cos_cyc 5).2.1

/-- `cos` 侧的一致界：`|iteratedDeriv 21 Real.cos x| ≤ 1`。 -/
theorem abs_iteratedDeriv21_cos_le_one (x : ℝ) : |iteratedDeriv 21 Real.cos x| ≤ 1 := by
  rw [iteratedDeriv21_cos, Pi.neg_apply, abs_neg]
  exact Real.abs_sin_le_one x

end RatInterval

end N11Formalization

