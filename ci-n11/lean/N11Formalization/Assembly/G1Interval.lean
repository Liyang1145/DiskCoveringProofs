import N11Formalization.OpNorm
import N11Formalization.Assembly.G1
import N11Formalization.Interval.Vector

/-!
# G1 前提的**区间内核对象化**：把 `hbound`/`hres` 写成区间侧可直接产出的形式

`Interval/Vector.lean`（interval-core 交付）提供 `RatInterval`（ℝ 侧语义 `RatInterval.Mem`）、
`dot`、`supNorm`、`BoxIncl`。本文件把 `Assembly/G1.lean` 的解析链前提翻译成**区间对象**：

* `opNorm_le_of_interval_matrix`：**逐元素区间矩阵** `J : Fin n → Fin n → RatInterval` 包住
  `A (single j 1) i` + 行和界 `≤ Q` ⇒ `‖A‖ ≤ Q`；
* `TCSystem_unique_root_of_interval_data`：把 `Assembly/G1` 的前提全部换成
  「区间矩阵包络 + 行和界 + 残差界」——即区间内核（`Interval/*`）能直接产出的形状。

**真实等级**：kernel-proved，无条件（除显式前提），零 sorry、零自定义 axiom。
-/

namespace N11Formalization

open Metric

/-- **逐元素区间矩阵 ⇒ ∞-算子范数界**（对 `OpNorm.opNorm_le_of_entry_bounds` 的区间对象适配）。 -/
theorem opNorm_le_of_interval_matrix {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {Q : ℝ}
    (hQ : 0 ≤ Q) (J : Fin n → Fin n → RatInterval)
    (henc : ∀ i j : Fin n, (J i j).Mem (A (Pi.single j 1) i))
    (hsum : ∀ i : Fin n, ∑ j : Fin n, max |((J i j).lo : ℝ)| |((J i j).hi : ℝ)| ≤ Q) :
    ‖A‖ ≤ Q :=
  opNorm_le_of_entry_bounds A hQ (fun i j => ((J i j).lo : ℝ)) (fun i j => ((J i j).hi : ℝ))
    (fun i j => ⟨RatInterval.mem_lo_le (henc i j), RatInterval.mem_le_hi (henc i j)⟩) hsum

/-- **G1：区间数据 ⇒ 源系统唯一根**。

前提全部是区间侧可直接产出的形状：

* `hdiff`：`TCSystem` 在球上可微（G1 剩余义务之一）；
* `J` + `henc`：`I − Y·(∂F/∂x)` 的**逐元素区间包络**（区间内核的 `dot`/`supNorm` 产出）；
* `hsum`：行和界 `≤ K`（`K < 1`）；
* `hres`：残差界 `η + K·ρ < ρ`（区间内核的 `krawczykAffine_mem` 一类读数产出）。

结论即 C891 的 `exists_unique` 字段（球口径）。 -/
theorem TCSystem_unique_root_of_interval_data {c : Fin 12 → ℝ} {ρ K : ℝ}
    (Y : (Fin 12 → ℝ) →L[ℝ] (Fin 12 → ℝ)) (hY : Function.Injective Y)
    (hρ : 0 < ρ) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hdiff : ∀ x ∈ closedBall c ρ, DifferentiableAt ℝ TCSystem x)
    (J : Fin 12 → Fin 12 → RatInterval)
    (henc : ∀ x ∈ closedBall c ρ, ∀ i j : Fin 12,
      (J i j).Mem ((ContinuousLinearMap.id ℝ (Fin 12 → ℝ) - Y.comp (fderiv ℝ TCSystem x))
        (Pi.single j 1) i))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12, max |((J i j).lo : ℝ)| |((J i j).hi : ℝ)| ≤ K)
    (hres : dist c (c - Y (TCSystem c)) + K * ρ < ρ) :
    ∃! x : Fin 12 → ℝ, x ∈ closedBall c ρ ∧ TCSystem x = 0 :=
  krawczyk_unique_root_of_entry_bounds TCSystem Y hY c ρ K hρ hK0 hK1 hdiff
    (fun i j => ((J i j).lo : ℝ)) (fun i j => ((J i j).hi : ℝ))
    (fun x hx i j => ⟨RatInterval.mem_lo_le (henc x hx i j),
      RatInterval.mem_le_hi (henc x hx i j)⟩) hsum hres

end N11Formalization
