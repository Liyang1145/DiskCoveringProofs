import Mathlib
import N11Formalization.FlashLocalChart

/-!
# FlashLocal — 120 局部叶承重链 · **pinned consumer**（真实 `hL` 槽位）

Lead（2026-09-30）更正：`FlashLocalMix` 里的 `localLeaf_lower_bound` /
`localLeaf_hundred_thousandth` 对**整个 `Fin 9` 球**陈述且 `mu > 0`，**不可实例化**——
**整体旋转方向能量不变**（所有锚点转同一角是刚体旋转，`V2` 不变），
故对常数方向 `x ≡ ω` 有 `V2 = R^2` 而 `sum_i x_i^2 = 9 ω^2 > 0`，
与 `R^2 + (mu/4) sum_i x_i^2 <= V2` 矛盾。**必须**把量词限制到源的真实 pinned 图表
（源 `ADAPTIVE-STRESS-FINITE-REMAINDER.md` 第 3 行：`x` 是 raw **theta8-pinned** angular
displacement，即 **`x 8 = 0`**）。

本件（**独立于 Mix**，不修改 Mix）：

1. `pinned_no_constant_direction` —— **pinning 为什么必要**的 kernel 事实：
   `x 8 = 0` 且所有坐标相等的方向只能是零方向（即整体旋转被排除）。
2. `sum_snoc_sq` —— `Fin 8` 注入 `Fin 9`（`Fin.snoc y 0`）后 `sum` 不变。
3. `localLeaf_lower_bound_fin8` —— **真实 pinned 消费者**：量词在 `Fin 8` 上
   （等价于 `x 8 = 0` 的 `Fin 9` 球，但和式只走 `Fin 8`，不产生 `x_8` 记账）。
4. `localLeaf_hundred_thousandth_fin8` —— `mu = 1/600` ⇒ `V2 >= R^2 + ||y||^2/100000`。

**scope**：本件的结论才是 `ResumeGlobalLeafSem.hL` 的 `qL^2/100000` 槽位形状。
`FlashLocalMix` 的 generic 版本**保持为条件陈述**，但**不再声称**它已付清真实 `hL` 槽
（其量词未 pin）。本件不含 `H0`、不含 stress、不含图语义。
-/

namespace N11Formalization.FlashLocal

noncomputable section

open Finset

/-- **pinning 的必要性（kernel 事实）**：在 `x 8 = 0` 的图表里，
"所有坐标相等"的方向只能是零方向。即整体旋转方向 `x ≡ ω ≠ 0` **不在** pinned 图表内
（否则它与 `V2` 的旋转不变性矛盾）。 -/
theorem pinned_no_constant_direction (x : Fin 9 → ℝ) (h8 : x 8 = 0)
    (hconst : ∀ i, x i = x 0) : ∀ i, x i = 0 := by
  intro i
  have h0 : x 0 = 0 := by
    have h := hconst 8
    rw [h8] at h
    exact h.symm
  rw [hconst i, h0]

/- 注：注入向量 `Fin.snoc y 0 : Fin 9 → ℝ` 在末位 `8` 处取 `0`（这就是本工程用的
`x 8 = 0` 图表）；本件不需要该字面量计算，故不登记为引理。真正承重的 pinning 事实是
上面的 `pinned_no_constant_direction`（整体旋转被排除）。 -/

/-- **真实 pinned 消费者（`Fin 8` 注入形式）**。

`hEV` = 弱对偶 `E <= V2`（沿 pinned 图表；由根内 `dirichlet_le_oracle` /
`cosine_energy_le_oracle` 实例化）；
`hE` = 能量沿图的二次增长（下一件付清，**同样只在 pinned 图表上**）；
`hc` = 常数条件。结论 = `V2 >= R^2 + (mu/4) ||y||^2`（`mu/4` **推出**，非假设）。 -/
theorem localLeaf_lower_bound_fin8 {V2 E : (Fin 9 → Point) → ℝ} {R mu c rho : ℝ}
    {θ : Fin 9 → ℝ}
    (hrho : 0 ≤ rho) (hc0 : 0 ≤ c)
    (hEV : ∀ y : Fin 8 → ℝ, (∑ j, y j ^ 2) ≤ rho ^ 2 →
        E (fun i => circleMap (θ i + Fin.snoc (α := fun _ : Fin 9 => ℝ) y 0 i))
          ≤ V2 (fun i => circleMap (θ i + Fin.snoc (α := fun _ : Fin 9 => ℝ) y 0 i)))
    (hE : ∀ y : Fin 8 → ℝ, (∑ j, y j ^ 2) ≤ rho ^ 2 →
        R ^ 2 + (mu / 2 - c * Real.sqrt (∑ j, y j ^ 2)) * (∑ j, y j ^ 2)
          ≤ E (fun i => circleMap (θ i + Fin.snoc (α := fun _ : Fin 9 => ℝ) y 0 i)))
    (hc : c * rho ≤ mu / 4) :
    ∀ y : Fin 8 → ℝ, (∑ j, y j ^ 2) ≤ rho ^ 2 →
      R ^ 2 + (mu / 4) * (∑ j, y j ^ 2)
        ≤ V2 (fun i => circleMap (θ i + Fin.snoc (α := fun _ : Fin 9 => ℝ) y 0 i)) := by
  intro y hy
  have hsnn : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (y j))
  have hrs : Real.sqrt (∑ j, y j ^ 2) ≤ rho := by
    calc Real.sqrt (∑ j, y j ^ 2) ≤ Real.sqrt (rho ^ 2) := Real.sqrt_le_sqrt hy
      _ = |rho| := Real.sqrt_sq_eq_abs _
      _ = rho := abs_of_nonneg hrho
  have hcr : c * Real.sqrt (∑ j, y j ^ 2) ≤ mu / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hrs hc0) hc
  have hquad : (mu / 4) * (∑ j, y j ^ 2)
      ≤ (mu / 2 - c * Real.sqrt (∑ j, y j ^ 2)) * (∑ j, y j ^ 2) := by
    nlinarith [hcr, hsnn]
  calc R ^ 2 + (mu / 4) * (∑ j, y j ^ 2)
      ≤ R ^ 2 + (mu / 2 - c * Real.sqrt (∑ j, y j ^ 2)) * (∑ j, y j ^ 2) := by linarith
    _ ≤ E (fun i => circleMap (θ i + Fin.snoc (α := fun _ : Fin 9 => ℝ) y 0 i)) := hE y hy
    _ ≤ V2 (fun i => circleMap (θ i + Fin.snoc (α := fun _ : Fin 9 => ℝ) y 0 i)) := hEV y hy

/-- **真实 pinned 数值消费者（源常数）**：`mu = 1/600`、`c * rho <= 1/2400` ⇒
`V2 >= R^2 + ||y||^2/100000`（`ResumeGlobalLeafSem.hL` 的槽位形状，且量词已 pin）。 -/
theorem localLeaf_hundred_thousandth_fin8 {V2 E : (Fin 9 → Point) → ℝ} {R c rho : ℝ}
    {θ : Fin 9 → ℝ}
    (hrho : 0 ≤ rho) (hc0 : 0 ≤ c)
    (hEV : ∀ y : Fin 8 → ℝ, (∑ j, y j ^ 2) ≤ rho ^ 2 →
        E (fun i => circleMap (θ i + Fin.snoc (α := fun _ : Fin 9 => ℝ) y 0 i))
          ≤ V2 (fun i => circleMap (θ i + Fin.snoc (α := fun _ : Fin 9 => ℝ) y 0 i)))
    (hE : ∀ y : Fin 8 → ℝ, (∑ j, y j ^ 2) ≤ rho ^ 2 →
        R ^ 2 + ((1 : ℝ) / 600 / 2 - c * Real.sqrt (∑ j, y j ^ 2)) * (∑ j, y j ^ 2)
          ≤ E (fun i => circleMap (θ i + Fin.snoc (α := fun _ : Fin 9 => ℝ) y 0 i)))
    (hc : c * rho ≤ (1 : ℝ) / 600 / 4) :
    ∀ y : Fin 8 → ℝ, (∑ j, y j ^ 2) ≤ rho ^ 2 →
      R ^ 2 + (∑ j, y j ^ 2) / 100000
        ≤ V2 (fun i => circleMap (θ i + Fin.snoc (α := fun _ : Fin 9 => ℝ) y 0 i)) := by
  intro y hy
  have hsnn : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg (y j))
  have hgen := localLeaf_lower_bound_fin8 (V2 := V2) (E := E) (R := R) (mu := 1 / 600)
    (c := c) (rho := rho) (θ := θ) hrho hc0 hEV hE hc y hy
  have hsplit : (1 : ℝ) / 600 / 4 = 1 / 2400 := by norm_num
  rw [hsplit] at hgen
  have : (∑ j, y j ^ 2) / 100000 ≤ (1 / 2400 : ℝ) * (∑ j, y j ^ 2) := by nlinarith [hsnn]
  linarith

end

end N11Formalization.FlashLocal

#print axioms N11Formalization.FlashLocal.pinned_no_constant_direction
#print axioms N11Formalization.FlashLocal.localLeaf_lower_bound_fin8
#print axioms N11Formalization.FlashLocal.localLeaf_hundred_thousandth_fin8
