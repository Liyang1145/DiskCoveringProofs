import N11Formalization.Transport
import N11Formalization.Assembly.G1Interval

/-!
# G1 的最终形态：**单套非退化条件** + **区间数据** ⇒ 源系统唯一根

把 `Transport.differentiableAt_TCSystem_of_conditions`（义务 (2) 的单条件收口）
与 `Assembly/G1Interval.TCSystem_unique_root_of_interval_data`（义务 (1) 的区间对象化）拼起来，
得到本项目对 G1 的**最紧陈述**：

```
非退化条件（盒内非零 / 两点不重合，区间侧给它们的箱内有理下界）
        │  Transport.differentiableAt_TCSystem_of_conditions
        ▼
DifferentiableAt ℝ TCSystem x            （= 义务 (2)，已付清）
        ─┐
区间矩阵包络 (J, henc) + 行和界 K<1 + 残差界 η+Kρ<ρ   （= 义务 (1)，数值）
        ─┤  Assembly/G1Interval.TCSystem_unique_root_of_interval_data
        ▼
∃! x ∈ B(c,ρ), TCSystem x = 0
```

**真实等级**：kernel-proved，无条件（除显式非退化条件与显式区间数据），零 sorry、零自定义 axiom。
本定理把 G1 的**全部剩余内容**压成两组显式前提，**没有隐藏的可微性/可积性义务**。
-/

namespace N11Formalization

open Metric

/-- **G1 最终形态**：单套非退化条件 + 区间数据 ⇒ `TCSystem` 在球内唯一根。 -/
theorem TCSystem_unique_root_of_final_data {c : Fin 12 → ℝ} {ρ K : ℝ}
    (Y : (Fin 12 → ℝ) →L[ℝ] (Fin 12 → ℝ)) (hY : Function.Injective Y)
    (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hndRho : ∀ x ∈ closedBall c ρ, ∀ j : Fin 9,
      (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hndW : ∀ x ∈ closedBall c ρ, (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hndU1 : ∀ x ∈ closedBall c ρ, Uvec x 1 ≠ hub1 x)
    (hndU2 : ∀ x ∈ closedBall c ρ, Uvec x 2 ≠ hub0 x)
    (hndU3 : ∀ x ∈ closedBall c ρ, Uvec x 3 ≠ hub0 x)
    (hndU8 : ∀ x ∈ closedBall c ρ, Uvec x 8 ≠ hub1 x)
    (hndWp : ∀ x ∈ closedBall c ρ, wPoint x ≠ ringCenter x 6)
    (J : Fin 12 → Fin 12 → RatInterval)
    (henc : ∀ x ∈ closedBall c ρ, ∀ i j : Fin 12,
      (J i j).Mem ((ContinuousLinearMap.id ℝ (Fin 12 → ℝ) - Y.comp (fderiv ℝ TCSystem x))
        (Pi.single j 1) i))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12, max |((J i j).lo : ℝ)| |((J i j).hi : ℝ)| ≤ K)
    (hres : dist c (c - Y (TCSystem c)) + K * ρ < ρ) :
    ∃! x : Fin 12 → ℝ, x ∈ closedBall c ρ ∧ TCSystem x = 0 :=
  TCSystem_unique_root_of_interval_data Y hY hρ hK0 hK1
    (fun x hx => differentiableAt_TCSystem_of_conditions x (hndRho x hx) (hndW x hx)
      (hndU1 x hx) (hndU2 x hx) (hndU3 x hx) (hndU8 x hx) (hndWp x hx))
    J henc hsum hres

end N11Formalization
