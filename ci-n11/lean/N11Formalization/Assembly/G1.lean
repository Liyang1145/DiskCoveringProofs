import N11Formalization.KrawczykDeriv
import N11Formalization.OpNorm
import N11Formalization.TCSystem

/-!
# G1 的完全组装：**区间侧的逐元素包络 ⇒ 源的唯一根**

本文件把三块拼起来，使 G1 的前提**全部落在区间侧可算的量**上：

```
区间侧给出：  ∀ x ∈ B(c,ρ), ∀ i j,  lo i j ≤ (I − Y·(∂F/∂x)(x))_{ij} ≤ hi i j     （逐元素包络）
              ∀ i, Σ_j max |lo i j| |hi i j| ≤ K  < 1                            （行和界）
              ‖Y (F c)‖ + K·ρ < ρ                                              （残差界）
                     ↓  opNorm_le_of_entry_bounds（行和 ⇒ ∞-算子范数）
              ∀ x ∈ B(c,ρ), ‖I − Y·(∂F/∂x)(x)‖ ≤ K
                     ↓  lipschitzOn_ball_of_deriv_bound（中值不等式）
              g = id − Y·F 在 B(c,ρ) 上 K-Lipschitz
                     ↓  krawczyk_banach（Banach 收缩 + 包含性内部推出）
              ∃! x ∈ B(c,ρ), F x = 0
```

**真实等级**：kernel-proved，无条件（除显式前提），零 sorry、零自定义 axiom。
剩余义务只有：包络 `lo/hi` 与 `K`、`η` 的**精确有理界**（区间内核负责）
以及 `hdiff`（`TCSystem` 在盒上可微，含欧氏范数 `dist`）。
-/

namespace N11Formalization

open Metric

/-- **G1 的完全组装箱**（任意有限维，Pi 范数 = sup 范数）：
逐元素包络 + 行和界 + 残差界 ⇒ 球内唯一根。 -/
theorem krawczyk_unique_root_of_entry_bounds {n : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (Y : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hY : Function.Injective Y) (c : Fin n → ℝ) (ρ K : ℝ)
    (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hdiff : ∀ x ∈ closedBall c ρ, DifferentiableAt ℝ F x)
    (lo hi : Fin n → Fin n → ℝ)
    (henc : ∀ x ∈ closedBall c ρ, ∀ i j : Fin n,
      lo i j ≤ (ContinuousLinearMap.id ℝ (Fin n → ℝ) - Y.comp (fderiv ℝ F x)) (Pi.single j 1) i ∧
        (ContinuousLinearMap.id ℝ (Fin n → ℝ) - Y.comp (fderiv ℝ F x)) (Pi.single j 1) i ≤ hi i j)
    (hsum : ∀ i : Fin n, ∑ j : Fin n, max |lo i j| |hi i j| ≤ K)
    (hres : dist c (c - Y (F c)) + K * ρ < ρ) :
    ∃! x : Fin n → ℝ, x ∈ closedBall c ρ ∧ F x = 0 :=
  krawczyk_banach_of_deriv_bound F Y hY c ρ K hρ hK0 hK1 hdiff
    (fun x hx => opNorm_le_of_entry_bounds _ hK0 lo hi (fun i j => henc x hx i j) hsum) hres

/-- **源系统 `TCSystem` 的实例**：C891 的 `exists_unique` 字段，
前提全在区间侧可算的量上。 -/
theorem TCSystem_unique_root_of_entry_bounds {c : Fin 12 → ℝ} {ρ K : ℝ}
    (Y : (Fin 12 → ℝ) →L[ℝ] (Fin 12 → ℝ)) (hY : Function.Injective Y)
    (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hdiff : ∀ x ∈ closedBall c ρ, DifferentiableAt ℝ TCSystem x)
    (lo hi : Fin 12 → Fin 12 → ℝ)
    (henc : ∀ x ∈ closedBall c ρ, ∀ i j : Fin 12,
      lo i j ≤ (ContinuousLinearMap.id ℝ (Fin 12 → ℝ) - Y.comp (fderiv ℝ TCSystem x))
        (Pi.single j 1) i ∧
        (ContinuousLinearMap.id ℝ (Fin 12 → ℝ) - Y.comp (fderiv ℝ TCSystem x))
          (Pi.single j 1) i ≤ hi i j)
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12, max |lo i j| |hi i j| ≤ K)
    (hres : dist c (c - Y (TCSystem c)) + K * ρ < ρ) :
    ∃! x : Fin 12 → ℝ, x ∈ closedBall c ρ ∧ TCSystem x = 0 :=
  krawczyk_unique_root_of_entry_bounds TCSystem Y hY c ρ K hρ hK0 hK1 hdiff lo hi henc hsum hres

end N11Formalization
