/-
# FlashCoverReductionWitness — 最近点见证引理（独立见证索引 κ 版）

作者：flash-cover-reduction。写域：`lean/N11Formalization/FlashCoverReduction*.lean`。

## 数学内容（源：DUAL-DISK-INTERFACE-AUDIT §9/§15、CLIPPED-DUAL-STRAIGHT-EMBEDDING §18）

设站点索引类型 `ι`，`c : ι → Point` 是覆盖单位闭盘 `D` 的半径 `r` 闭盘中心。
设**独立**的见证索引类型 `κ`（`κ` 与 `ι` 可以不同），`W : κ → Point` 是落在 `D` 内的
见证点族，`σ : κ → Finset ι` 关联站点，且满足**最近性**

  `hnearest : ∀ k j, j ∈ σ k → ∀ i, dist (W k) (c j) ≤ dist (W k) (c i)`

（即 `σ k` 中每个站点都是 `W k` 的最近站点；**不是**直接假设距离 ≤ r）。则

  `∀ k j, j ∈ σ k → dist (W k) (c j) ≤ r`

**证明**：`W k ∈ D` ⇒ 覆盖给出某 `q` 使 `dist (W k) (c q) ≤ r`；
最近性给出 `dist (W k) (c j) ≤ dist (W k) (c q) ≤ r`。

**这是把"覆盖"变成"见证"的唯一解析步骤**，也是 51 条约束（环-开关 18 + 面顶点 33）
之所以是**必要条件**的来源。它不是枚举陈述，也不依赖任何图类型假设。

## 量词

任意站点类型 `ι`、**独立**见证类型 `κ`、任意 `r`、任意 `c`、`W`、`σ`。
`σ` 取任意 `Finset`，故同时覆盖"面顶点三元组"与"边界开关的两站点对"。

## 与主目标的关系（防对象漂移）

- 本模块**不**声称 enumerated graph classification。
- 站点/见证索引**可以不同**（`κ` 独立于 `ι`）：`σ` 的行数可多于站点数。
- 复用 `Definitions.lean` 的 `Point` / `unitDisk`；`Definitions` 不 import 本模块，无环。

-/

import Mathlib
import N11Formalization.Definitions

namespace N11Formalization

variable {ι κ : Type*}

/-- **最近点见证引理**（独立见证索引 `κ`）。

若 `c` 以半径 `r` 覆盖单位闭盘，见证点 `W k` 在 `D` 内，且 `σ k` 中每个站点都是
`W k` 的最近站点，则 `σ k` 中每个站点到 `W k` 的距离 ≤ r。 -/
theorem nearest_witness_le_radius {c : ι → Point} {r : ℝ}
    (hcov : ∀ x : Point, x ∈ unitDisk → ∃ i, dist x (c i) ≤ r)
    {W : κ → Point} {σ : κ → Finset ι} (hW : ∀ k, W k ∈ unitDisk)
    (hnearest : ∀ k j, j ∈ σ k → ∀ i, dist (W k) (c j) ≤ dist (W k) (c i)) :
    ∀ k j, j ∈ σ k → dist (W k) (c j) ≤ r := by
  intro k j hj
  obtain ⟨q, hq⟩ := hcov (W k) (hW k)
  exact le_trans (hnearest k j hj q) hq

/-- **任意盘内点的最近站点在 r 内**（见证引理的单元形式）。 -/
theorem nearest_site_le_radius {c : ι → Point} {r : ℝ}
    (hcov : ∀ x : Point, x ∈ unitDisk → ∃ i, dist x (c i) ≤ r)
    {x : Point} (hx : x ∈ unitDisk) {k : ι} (hmin : ∀ i, dist x (c k) ≤ dist x (c i)) :
    dist x (c k) ≤ r := by
  obtain ⟨q, hq⟩ := hcov x hx
  exact le_trans (hmin q) hq

/-- **见证族同时满足**：覆盖给出"存在站点在 r 内"，最近性把界传给每个关联站点。 -/
theorem witness_family_le_radius {c : ι → Point} {r : ℝ}
    (hcov : ∀ x : Point, x ∈ unitDisk → ∃ i, dist x (c i) ≤ r)
    {W : κ → Point} {σ : κ → Finset ι} (hW : ∀ k, W k ∈ unitDisk)
    (hnearest : ∀ k j, j ∈ σ k → ∀ i, dist (W k) (c j) ≤ dist (W k) (c i)) :
    (∀ k, ∃ i, dist (W k) (c i) ≤ r) ∧
      (∀ k j, j ∈ σ k → dist (W k) (c j) ≤ r) :=
  ⟨fun k => hcov (W k) (hW k), nearest_witness_le_radius hcov hW hnearest⟩

end N11Formalization
