/-
# `Precond` 七条非退化条件的**接口引理**（Lead，R41）

**用途**：`interval-ad` 在 C1070 里给出七条 `hnd*` 的**化归形式**——
- **标量型**（`hndRho` 9 条、`hndW`）：在证书盒上对 `g` 做**区间求值**得到 `I`，证 `0 ∉ I` ⇒ `∀ x ∈ B, g x ≠ 0`；
- **点分离型**（`hndU1/U2/U3/U8`、`hndWp`）：证两点的坐标差**有严格下界** ⇒ 两点不相等。

本文件只提供**从"区间读数"到"非零/非相等"的接口引理**（把 `interval-ad` 的数值判决转成 Lean 可用的形状），**不**证明七条中的任何一条（那需要值侧包含性 + 盒上求值，属 `fm-eval` 一侧）。

**口径**：全部为纯逻辑/序引理，`ℝ` 上的结论，不涉及任何数值表。
-/
import N11Formalization.Interval

namespace N11Formalization

open scoped Real

/-! ## 1. 标量型：区间不含 `0` ⇒ 真值非零 -/

/-- **通用形**：若 `g ∈ I` 且 `0 ∉ I`，则 `g ≠ 0`。
（`interval-ad` 的标量型化归给出的正是"`0 ∉ I`"这一条读数。） -/
theorem ne_zero_of_mem_of_not_mem_zero {I : RatInterval} {g : ℝ}
    (h : I.Mem g) (h0 : ¬ I.Mem (0 : ℝ)) : g ≠ 0 :=
  fun hg => h0 (hg ▸ h)

/-- **端点形（下）**：`0 < I.lo` ⇒ 区间内的任何 `g` 非零。
（多数实际用法给出的是端点比较，而非 `¬ Mem` 的命题形。） -/
theorem ne_zero_of_pos_lo {I : RatInterval} {g : ℝ}
    (h0 : (0 : ℝ) < (I.lo : ℝ)) (h : I.Mem g) : g ≠ 0 := by
  intro hg
  have := RatInterval.mem_lo_le h
  rw [hg] at this
  linarith

/-- **端点形（上）**：`I.hi < 0` ⇒ 区间内的任何 `g` 非零。 -/
theorem ne_zero_of_neg_hi {I : RatInterval} {g : ℝ}
    (h0 : (I.hi : ℝ) < 0) (h : I.Mem g) : g ≠ 0 := by
  intro hg
  have := RatInterval.mem_le_hi h
  rw [hg] at this
  linarith

/-! ## 2. 点分离型：坐标差有严格下界 ⇒ 两点不相等 -/

/- **（R76 已删除）** 原 `pair_ne_of_abs_sub_bounds`（"两坐标各有正下界"形）**已删**：其证据只用**第一坐标**
（`congrArg Prod.fst`），第二坐标的两个假设 `_hy`/`_hb` **从未参与证据** ⇒ 该引理**看起来比实际强**，
属**误导性接口**。**依据**：独立复核 `box-rstar`（C1128）指出、Lead 在 R76 机械复核确认（证据仅经 `Prod.fst`）；
全库**无任何消费者**（仅自身声明 1 处命中），且下文单坐标形 `pair_ne_of_abs_sub_bound`
**假设更少、结论相同** ⇒ 删除不损失任何东西。
**若将来真需要"两坐标联合"的点分离，必须新写一条让两个坐标的假设参与证据的引理** ——
不能靠这个只吃第一坐标的引理（那会给出"我证了两坐标分离"的错觉）。
**（注：这条留痕必须是普通块注释，不能用文档注释 —— 文档注释后必须紧跟声明，否则 Lean 报
"unexpected token，expected lemma"；这是 R39 记录过的坑。另：Lean 的块注释会嵌套，所以
本注释内不得再出现任何字面注释定界符，否则内层会吞掉外层。）** -/

/-- **点分离（单坐标形）**：只需一个坐标的绝对差有严格正下界。 -/
theorem pair_ne_of_abs_sub_bound {x₁ y₁ x₂ y₂ a : ℝ}
    (hx : a ≤ |x₁ - x₂|) (ha : 0 < a) : (x₁, y₁) ≠ (x₂, y₂) := by
  intro h
  have h1 : x₁ = x₂ := congrArg Prod.fst h
  have : |x₁ - x₂| = 0 := by rw [h1]; simp
  linarith [hx, this.le, ha]

end N11Formalization

