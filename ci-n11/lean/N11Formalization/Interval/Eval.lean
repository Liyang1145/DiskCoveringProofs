/-
  N11Formalization.Interval.Eval
  ==============================

  反射/组合层：把「区间向量 → 区间向量」的映射写成表达式，并**证明它的包含性**。

  设计要点
  --------
  * `IExpr n` 是 `n` 元表达式语言：变量、有理常数、`+ - * `、取负、自然数幂、
    倒数、平方根，外加一个 **通用挂点 `app1`**：任何「区间算子 `f` + 实数函数 `g`
    + 已证的包含性 `Mem I y → Mem (f I) (g y)`」都可以作为一元节点挂进来。
    这样语言在**形式上是完备的**：将来证好 `sin/cos/atan2` 的包含性定理后，
    不需要改本文件，直接 `app1` 注册即可（见 `sqrt_as_app1` 的示范）。
  * 求值是**偏函数**：`inv` 需要分母区间不含 0，`pow` 需要 `0 ≤ lo`。
    条件不满足时返回 `none`（保守回退，不猜测）；`none` 不会被 `eval_sound` 解释成
    任何真命题——因此「回退」不可能伪造出包含性。
  * `eval_sound` 是唯一的声音性定理：区间求值成功 ⟹ 实数求值落在该区间内。

  纪律：无 `sorry`、无自定义 `axiom`、无 `native_decide`、无 `#eval` 当证明。
-/
import Mathlib
import N11Formalization.Interval.Core
import N11Formalization.Interval.Sqrt

namespace N11Formalization

/-- `n` 元区间表达式（`n = 12` 对应 TC/KKT 的变量数）。 -/
inductive IExpr (n : ℕ) : Type where
  | var (i : Fin n) : IExpr n
  | const (q : ℚ) : IExpr n
  | add (a b : IExpr n) : IExpr n
  | sub (a b : IExpr n) : IExpr n
  | mul (a b : IExpr n) : IExpr n
  | neg (a : IExpr n) : IExpr n
  | pow (a : IExpr n) (k : ℕ) : IExpr n
  | inv (a : IExpr n) : IExpr n
  | sqrt (a : IExpr n) : IExpr n
  /-- 通用一元挂点：`f` 是区间算子，`g` 是实数函数，`hsound` 是其已证的包含性。 -/
  | app1 (f : RatInterval → RatInterval) (g : ℝ → ℝ)
      (hsound : ∀ (I : RatInterval) (y : ℝ), RatInterval.Mem I y → RatInterval.Mem (f I) (g y))
      (a : IExpr n) : IExpr n

namespace IExpr

variable {n : ℕ}

/-- 区间求值（偏函数；条件不满足返回 `none`，即保守回退）。 -/
def eval (A : Fin n → RatInterval) : IExpr n → Option RatInterval
  | var i => some (A i)
  | const q => some (RatInterval.ofRat q)
  | add a b => (eval A a).bind (fun x => (eval A b).map (fun y => x.add y))
  | sub a b => (eval A a).bind (fun x => (eval A b).map (fun y => x.sub y))
  | mul a b => (eval A a).bind (fun x => (eval A b).map (fun y => x.mul y))
  | neg a => (eval A a).map RatInterval.neg
  | pow a k => (eval A a).bind (fun x => if 0 ≤ x.lo then some (x.pow k) else none)
  | inv a => (eval A a).bind (fun x => if h : x.hi < 0 ∨ 0 < x.lo then some (x.inv h) else none)
  | sqrt a => (eval A a).map RatInterval.sqrt
  | app1 f _ _ a => (eval A a).map f

/-- 实数求值（语义层）。`Real.sqrt` / `⁻¹` 在 ℝ 上不可计算，故标 `noncomputable`；
这只影响代码生成，不影响内核可检查性。 -/
noncomputable def evalR (x : Fin n → ℝ) : IExpr n → ℝ
  | var i => x i
  | const q => (q : ℝ)
  | add a b => evalR x a + evalR x b
  | sub a b => evalR x a - evalR x b
  | mul a b => evalR x a * evalR x b
  | neg a => -evalR x a
  | pow a k => (evalR x a) ^ k
  | inv a => (evalR x a)⁻¹
  | sqrt a => Real.sqrt (evalR x a)
  | app1 _ g _ a => g (evalR x a)

/-- **声音性**：若对每个变量 `A i ∋ x i`，且区间求值成功得到 `B`，
则实数求值落在 `B` 里。 -/
theorem eval_sound {A : Fin n → RatInterval} {x : Fin n → ℝ} (hx : ∀ i, RatInterval.Mem (A i) (x i)) :
    ∀ (F : IExpr n) (B : RatInterval), F.eval A = some B → RatInterval.Mem B (F.evalR x) := by
  intro F
  induction F with
  | var i =>
    intro B h
    simp only [eval, Option.some.injEq] at h
    subst h
    exact hx i
  | const q =>
    intro B h
    simp only [eval, Option.some.injEq] at h
    subst h
    exact RatInterval.ofRat_mem q
  | add a b iha ihb =>
    intro B h
    obtain ⟨Ba, hBa, hrest⟩ := Option.bind_eq_some_iff.mp (by simpa only [eval] using h)
    obtain ⟨Bb, hBb, rfl⟩ := Option.map_eq_some_iff.mp hrest
    exact RatInterval.add_mem (iha Ba hBa) (ihb Bb hBb)
  | sub a b iha ihb =>
    intro B h
    obtain ⟨Ba, hBa, hrest⟩ := Option.bind_eq_some_iff.mp (by simpa only [eval] using h)
    obtain ⟨Bb, hBb, rfl⟩ := Option.map_eq_some_iff.mp hrest
    exact RatInterval.sub_mem (iha Ba hBa) (ihb Bb hBb)
  | mul a b iha ihb =>
    intro B h
    obtain ⟨Ba, hBa, hrest⟩ := Option.bind_eq_some_iff.mp (by simpa only [eval] using h)
    obtain ⟨Bb, hBb, rfl⟩ := Option.map_eq_some_iff.mp hrest
    exact RatInterval.mul_mem (iha Ba hBa) (ihb Bb hBb)
  | neg a iha =>
    intro B h
    obtain ⟨Ba, hBa, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [eval] using h)
    exact RatInterval.neg_mem (iha Ba hBa)
  | pow a k iha =>
    intro B h
    obtain ⟨Ba, hBa, hrest⟩ := Option.bind_eq_some_iff.mp (by simpa only [eval] using h)
    by_cases hlo : 0 ≤ Ba.lo
    · rw [if_pos hlo, Option.some.injEq] at hrest
      subst hrest
      exact RatInterval.pow_mem hlo (iha Ba hBa) k
    · rw [if_neg hlo] at hrest
      exact absurd hrest (by simp)
  | inv a iha =>
    intro B h
    obtain ⟨Ba, hBa, hrest⟩ := Option.bind_eq_some_iff.mp (by simpa only [eval] using h)
    by_cases hz : Ba.hi < 0 ∨ 0 < Ba.lo
    · rw [dif_pos hz, Option.some.injEq] at hrest
      subst hrest
      exact RatInterval.inv_mem (iha Ba hBa) hz
    · rw [dif_neg hz] at hrest
      exact absurd hrest (by simp)
  | sqrt a iha =>
    intro B h
    obtain ⟨Ba, hBa, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [eval] using h)
    exact RatInterval.sqrt_mem (iha Ba hBa)
  | app1 f g hs a iha =>
    intro B h
    obtain ⟨Ba, hBa, rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [eval] using h)
    exact hs Ba (evalR x a) (iha Ba hBa)

/-- **求值成功 ⟹ 结果区间合法**：由 `eval_sound` + `valid_of_mem` 直接得到，
（对 `Valid` 保持性而言这就是全部所需；无需对 `eval` 的另一条归纳）。 -/
theorem eval_valid {A : Fin n → RatInterval} {x : Fin n → ℝ}
    (hx : ∀ i, RatInterval.Mem (A i) (x i)) (F : IExpr n) {B : RatInterval}
    (hB : F.eval A = some B) : RatInterval.Valid B :=
  RatInterval.valid_of_mem (eval_sound hx F B hB)

/-! ## 组合读数 -/

/-- 向量形式：逐分量求值成功 ⟹ 逐分量包含。 -/
theorem eval_sound_vec {m : ℕ} {A : Fin n → RatInterval} {x : Fin n → ℝ}
    (hx : ∀ i, RatInterval.Mem (A i) (x i)) (F : Fin m → IExpr n) (B : Fin m → RatInterval)
    (hB : ∀ j, (F j).eval A = some (B j)) : ∀ j, RatInterval.Mem (B j) ((F j).evalR x) :=
  fun j => eval_sound hx (F j) (B j) (hB j)

/-- `app1` 挂点示范：`sqrt` 既能作为内建节点，也能作为通用一元节点注册。 -/
theorem sqrt_as_app1 (A : Fin n → RatInterval) (a : IExpr n) :
    (app1 RatInterval.sqrt Real.sqrt
        (fun I y h => RatInterval.sqrt_mem (A := I) (x := y) h) a).eval A = (sqrt a).eval A :=
  rfl

/-- 具体环境：`Fin 0`（无变量），用来把求值走到底、暴露真实端点。 -/
def noEnv : Fin 0 → RatInterval := fun i => i.elim0

/-- 具体环境（实数侧）。 -/
def noEnvR : Fin 0 → ℝ := fun i => i.elim0

/-- 具体实例（区间求值）：表达式 `2*4 - 1` 在无变量环境下求值为 `[7,7]`。 -/
theorem read_eval_const_eval :
    (sub (mul (const 2) (const 4)) (const 1)).eval noEnv = some (RatInterval.intv 7 7) := by
  simp only [eval]
  norm_num [RatInterval.intv, RatInterval.mul, RatInterval.sub, RatInterval.ofRat]

/-- 具体实例（实数求值）：同一表达式在语义层等于 `7`。 -/
theorem read_eval_const_value :
    (sub (mul (const 2) (const 4)) (const 1)).evalR noEnvR = 7 := by
  norm_num [evalR]

/-- 具体实例（声音性端到端）：区间求值成功 ⟹ `7 ∈ [7,7]`。 -/
theorem read_eval_const_mem :
    RatInterval.Mem (RatInterval.intv 7 7)
      ((sub (mul (const 2) (const 4)) (const 1)).evalR noEnvR) :=
  eval_sound (A := noEnv) (x := noEnvR) (by intro i; exact i.elim0)
    (sub (mul (const 2) (const 4)) (const 1)) (RatInterval.intv 7 7) read_eval_const_eval

end IExpr

end N11Formalization
