import N11Formalization.Reduction

/-!
# n=11 全局最优性 —— 最终定理类型（防对象漂移的固定点）

GUIDE §0/§2：待证命题是

> 单位闭圆盘可由 11 个半径 `R*` 的闭盘覆盖；任意 11 个等半径闭盘覆盖单位闭圆盘的半径均不小于 `R*`；
> 中心可任意位于 `ℝ²`，不限制对称性、接触图、一般位置或边界盘数。

本文件把该命题的**完整类型**固定下来（`N11MainStatement`），并把"达到 + 下界 ⇒ 主命题"
与"sInf 推论"两条管道显式证出。**这不是在假设结论**：两个接口 `∃ c, Covers c Rstar` 与
`∀ r c, 0 ≤ r → Covers c r → Rstar ≤ r` 是 `Rstar` 之外的**显式前提**，
其证明义务归属于 C891（根）/C892（达到）/C923+C921（下界），当前**未形式化**。
-/

namespace N11Formalization

/-- **最终主命题**（对给定 `R`）：`R` 是可行半径集合的最小元，且下确界就是 `R`。

展开后即："存在 11 个半径 `R` 的闭盘覆盖 `D`" ∧ "任何 11 个半径 `r` 的闭盘覆盖 `D` 都有 `R ≤ r`"，
再加上 `sInf` 口径。所有量词都覆盖任意中心、任意位置、允许退化。

**注意（stmt-audit 对抗审计发现）**：第二个合取项 `sInf feasibleRadii = R` 在已证
`非空 + 下有界 + 达到`（`Attainment.lean`）的前提下**由 `.1` 可推**，不是独立内容；
下游不得把 `.2` 单独当作"达到性"。承重形式是**两条标量不等式**，见
`Sharpening.lean` 的 `n11MainStatement_iff_two_bounds`：
`sInf feasibleRadii ≤ R`（达到侧，C892）∧ `R ≤ sInf feasibleRadii`（下界侧，C923+C921+C922）。 -/
def N11MainStatement (R : ℝ) : Prop :=
  IsLeast feasibleRadii R ∧ sInf feasibleRadii = R

/-- 达到侧（GUIDE §2 强接口第一支）。 -/
theorem n11_attainment {R : ℝ} (h : StrongInterface R) :
    ∃ c : Fin 11 → Point, Covers c R :=
  h.attains

/-- 最优性侧（GUIDE §2 强接口第二支），量词形状与源命题一致。 -/
theorem n11_optimality {R : ℝ} (h : StrongInterface R) (r : ℝ) (c : Fin 11 → Point)
    (hr : 0 ≤ r) (hc : Covers c r) : R ≤ r :=
  h.bounds r c hr hc

/-- **主定理（由强接口）**：全无条件地（除显式前提外）给出 `IsLeast` 与 `sInf = R`。 -/
theorem n11_main_of_strongInterface {R : ℝ} (h : StrongInterface R) : N11MainStatement R :=
  ⟨(isLeast_iff_strongInterface R).mpr h, sInf_feasibleRadii_eq ((isLeast_iff_strongInterface R).mpr h)⟩

/-- 主命题 ⇒ 强接口（等价性，防止只证一边的弱化）。 -/
theorem strongInterface_of_n11_main {R : ℝ} (h : N11MainStatement R) : StrongInterface R :=
  (isLeast_iff_strongInterface R).mp h.1

/-- 主命题的可执行读数："不存在任何更小的等半径覆盖"。 -/
theorem n11_no_smaller {R : ℝ} (h : StrongInterface R) {r : ℝ} (hr : r < R) :
    ¬ ∃ c : Fin 11 → Point, Covers c r :=
  no_cover_below h hr

end N11Formalization
