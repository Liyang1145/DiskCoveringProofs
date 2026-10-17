/-
# FlashCoverReductionFaceMap — 泛型 face-map 见证接口与 weighted energy ≤ r²

作者：flash-cover-reduction。写域：`lean/N11Formalization/FlashCoverReduction*.lean`。

## 内容

1. **泛型见证结构（独立站点/见证索引）**：站点索引 `S`、**独立**见证索引 `J`、
   关联 `σ : J → Finset S`。若封面 + 见证点在 `D` 内 + 最近性，则所有关联对距离 ≤ r。

2. **泛型 face-map weighted energy ≤ r²**（不复制完整 Dirichlet 结构）：
   任意见证点族 `F : J → Point` 与任意点族 `X : J → Point`，若存在 `L ≥ 0`
   使逐见证点 `‖X j − F j‖ ≤ L`，则对任意非负权重 `w`（`∑ w = 1`）有
   `∑ j, w j * ‖X j − F j‖² ≤ L²`。取 `L = r` 即 energy ≤ r²。
   该陈述不引用任何具体图，故对任意 face map（任意图）成立。

3. **canonical 51 约束的实例化**：9 环 + 2 hub；见证集 =
   9 个环-开关见证（各关联 2 环）+ 11 个面见证（各关联 3 站点）；合计 51 对。

本模块只给**必要条件**与**由必要条件推出的能量上界**，不含图分类/枚举陈述。

依赖：`FlashCoverReductionWitness`（最近点见证引理，独立见证索引 `κ`）与
`Definitions`（`Point` / `unitDisk`）。本模块**不再内联**该引理，
`faceMap_witness_le_radius` 直接调用 `nearest_witness_le_radius`。
后续 `FlashCoverReductionBridge` 把这里的 canonical 表接到 `ResumeNetwork.Feasible/V2`。
-/

import Mathlib
import N11Formalization.Definitions
import N11Formalization.FlashCoverReductionWitness

namespace N11Formalization

open scoped BigOperators

variable {S J : Type*}

/-- 泛型见证接口：站点集 `S`、**独立**见证集 `J`、关联 `σ`。 -/
structure FaceMap (S J : Type*) where
  /-- 每个见证点关联的站点集合（面顶点 / 开关的两环）。 -/
  sigma : J → Finset S

/-- **泛型见证引理**（独立站点/见证索引）：封面 + 盘内见证 + 最近性 ⇒ 关联对距离 ≤ r。
直接复用 `FlashCoverReductionWitness.nearest_witness_le_radius`。 -/
theorem faceMap_witness_le_radius {c : S → Point} {r : ℝ}
    (hcov : ∀ x : Point, x ∈ unitDisk → ∃ i, dist x (c i) ≤ r)
    (M : FaceMap S J) {W : J → Point} (hW : ∀ j, W j ∈ unitDisk)
    (hnearest : ∀ j i, i ∈ M.sigma j → ∀ k, dist (W j) (c i) ≤ dist (W j) (c k)) :
    ∀ j i, i ∈ M.sigma j → dist (W j) (c i) ≤ r := by
  intro j i hi
  exact nearest_witness_le_radius hcov hW (fun j i hi k => hnearest j i hi k) j i hi

/-- **泛型 weighted energy 上界**（任意 face map，不引用图结构）。

`w` 非负且和为 1；若逐点 `‖X j − F j‖ ≤ L`，则 `∑ w j * ‖X j − F j‖² ≤ L²`。 -/
theorem weighted_energy_le_sq {J : Type*} [Fintype J] {w : J → ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    {X F : J → Point} {L : ℝ} (hL : ∀ j, ‖X j - F j‖ ≤ L) :
    ∑ j, w j * ‖X j - F j‖ ^ 2 ≤ L ^ 2 := by
  have hterm : ∀ j, w j * ‖X j - F j‖ ^ 2 ≤ w j * L ^ 2 := by
    intro j
    have hb : ‖X j - F j‖ ^ 2 ≤ L ^ 2 := by
      have h0 : 0 ≤ ‖X j - F j‖ := norm_nonneg _
      nlinarith [hL j, h0, sq_nonneg (L - ‖X j - F j‖)]
    exact mul_le_mul_of_nonneg_left hb (hw0 j)
  calc ∑ j, w j * ‖X j - F j‖ ^ 2
      ≤ ∑ j, w j * L ^ 2 := Finset.sum_le_sum fun j _ => hterm j
    _ = (∑ j, w j) * L ^ 2 := by rw [Finset.sum_mul]
    _ = L ^ 2 := by rw [hw1, one_mul]

/-- weighted energy 的半径形式：逐点位移 ≤ r ⇒ energy ≤ r²。 -/
theorem weighted_energy_le_radius_sq {J : Type*} [Fintype J] {w : J → ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    {X F : J → Point} {r : ℝ} (hL : ∀ j, ‖X j - F j‖ ≤ r) :
    ∑ j, w j * ‖X j - F j‖ ^ 2 ≤ r ^ 2 :=
  weighted_energy_le_sq hw0 hw1 hL

/-! ## canonical 51 约束的实例化（9 环 + 2 hub） -/

/-- 站点：`ring i`（i : Fin 9）或 `hub h`（h : Fin 2）。 -/
inductive CanonSite : Type
  | ring : Fin 9 → CanonSite
  | hub : Fin 2 → CanonSite
  deriving DecidableEq, Fintype

/-- 见证：`switch i`（环 i 与环 i+1 之间的边界开关）或 `face p`（11 个三角面）。 -/
inductive CanonWitness : Type
  | switch : Fin 9 → CanonWitness
  | face : Fin 11 → CanonWitness
  deriving DecidableEq, Fintype

/-- 环 i+1（模 9）。 -/
def nextRing (i : Fin 9) : Fin 9 := ⟨(i.val + 1) % 9, Nat.mod_lt _ (by omega)⟩

/-- 开关见证的关联站点：环 i 与环 i+1。 -/
def switchAssoc (i : Fin 9) : Finset CanonSite :=
  {CanonSite.ring i, CanonSite.ring (nextRing i)}

/-- 面见证的关联站点（index map 版）：
p<4 → hub0 与环 p,p+1；4≤p<9 → hub1 与环 p,(p+1)%9；p=9 → hub0,hub1,环0；p=10 → hub0,hub1,环4。 -/
def faceTri (p : Fin 11) : Finset CanonSite :=
  if h1 : p.val < 4 then
    {CanonSite.hub 0, CanonSite.ring ⟨p.val, by omega⟩, CanonSite.ring ⟨p.val + 1, by omega⟩}
  else if h2 : p.val < 9 then
    {CanonSite.hub 1, CanonSite.ring ⟨p.val, by omega⟩,
      CanonSite.ring ⟨(p.val + 1) % 9, Nat.mod_lt _ (by omega)⟩}
  else if p.val = 9 then
    {CanonSite.hub 0, CanonSite.hub 1, CanonSite.ring 0}
  else
    {CanonSite.hub 0, CanonSite.hub 1, CanonSite.ring 4}

/-- canonical face-map 关联。 -/
def canonSigma : CanonWitness → Finset CanonSite
  | CanonWitness.switch i => switchAssoc i
  | CanonWitness.face p => faceTri p

/-- 开关见证的关联大小 = 2。 -/
theorem card_switchAssoc (i : Fin 9) : (switchAssoc i).card = 2 := by
  have hne : CanonSite.ring i ≠ CanonSite.ring (nextRing i) := by
    intro h
    have h2 : i = nextRing i := CanonSite.ring.inj h
    have h3 : i.val = (i.val + 1) % 9 := congrArg Fin.val h2
    have hlt : i.val < 9 := i.isLt
    omega
  rw [switchAssoc, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- 面见证的关联大小 = 3。 -/
theorem card_faceTri (p : Fin 11) : (faceTri p).card = 3 := by
  fin_cases p <;> decide

/-- **canonical 51 计数**：9×2 + 11×3 = 51 对关联（经各自的 card 引理）。 -/
theorem canonical_pair_count :
    (∑ i : Fin 9, (switchAssoc i).card) + (∑ p : Fin 11, (faceTri p).card) = 51 := by
  simp [card_switchAssoc, card_faceTri, Finset.sum_const, Fintype.card_fin]

/-- **canonical 51 实例的必要性**：把见证引理实例化到 9+2 站点集。 -/
theorem canonical_51_constraints {c : CanonSite → Point} {r : ℝ}
    (hcov : ∀ x : Point, x ∈ unitDisk → ∃ i, dist x (c i) ≤ r)
    {W : CanonWitness → Point} (hW : ∀ j, W j ∈ unitDisk)
    (hnearest : ∀ j i, i ∈ canonSigma j →
      ∀ k, dist (W j) (c i) ≤ dist (W j) (c k)) :
    (∀ i : Fin 9, ∀ s ∈ switchAssoc i, dist (W (CanonWitness.switch i)) (c s) ≤ r) ∧
      (∀ p : Fin 11, ∀ s ∈ faceTri p, dist (W (CanonWitness.face p)) (c s) ≤ r) := by
  constructor
  · intro i s hs
    exact nearest_witness_le_radius hcov hW (fun j i hi k => hnearest j i hi k)
      (CanonWitness.switch i) s hs
  · intro p s hs
    exact nearest_witness_le_radius hcov hW (fun j i hi k => hnearest j i hi k)
      (CanonWitness.face p) s hs

end N11Formalization
