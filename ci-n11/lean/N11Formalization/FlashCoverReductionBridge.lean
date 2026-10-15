/-
# FlashCoverReductionBridge — CanonSite/CanonWitness ↔ ResumeNetwork 的显式桥

作者：flash-cover-reduction。写域：`lean/N11Formalization/FlashCoverReduction*.lean`。

## 目的（"消费 C911"的那一步）

把 canonical 站点/见证表接到**真实对象** `ResumeNetwork`（Feasible / V2）：

1. `canonSiteEquiv : CanonSite ≃ Fin 11`（ring i ↦ i、hub 0 ↦ 9、hub 1 ↦ 10）；
2. `faceTri f` 映射后**逐项等于** `ResumeNetwork.face f` 的三个顶点；
3. 由最近点见证引理得到**真实** `ResumeNetwork.Feasible U C Z r`，
   再由 `oracle_le_feasible` 得 **`V2 U ≤ r²`**。

本模块复用 `Definitions.Point/unitDisk` 与 `ResumeNetwork.Feasible/V2`，不自造 oracle。
-/

import Mathlib
import N11Formalization.ResumeNetwork
import N11Formalization.FlashCoverReductionWitness

namespace N11Formalization

open scoped BigOperators

/-! ## 0. canonical 站点 / 见证表 -/

inductive CanonSite : Type
  | ring : Fin 9 → CanonSite
  | hub : Fin 2 → CanonSite
  deriving DecidableEq, Fintype

inductive CanonWitness : Type
  | switch : Fin 9 → CanonWitness
  | face : Fin 11 → CanonWitness
  deriving DecidableEq, Fintype

/-- 环 i+1（模 9）。 -/
def nextRing (i : Fin 9) : Fin 9 := ⟨(i.val + 1) % 9, Nat.mod_lt _ (by omega)⟩

/-- 开关见证关联的环站点：环 i 与环 i+1。 -/
def switchAssoc (i : Fin 9) : Finset CanonSite :=
  {CanonSite.ring i, CanonSite.ring (nextRing i)}

/-- 面见证关联的三个站点（与 `ResumeNetwork.face` 同表，逐值定义）。 -/
def faceTri (p : Fin 11) : Finset CanonSite :=
  match p with
  | 0 => {CanonSite.hub 0, CanonSite.ring 0, CanonSite.ring 1}
  | 1 => {CanonSite.hub 0, CanonSite.ring 1, CanonSite.ring 2}
  | 2 => {CanonSite.hub 0, CanonSite.ring 2, CanonSite.ring 3}
  | 3 => {CanonSite.hub 0, CanonSite.ring 3, CanonSite.ring 4}
  | 4 => {CanonSite.hub 1, CanonSite.ring 4, CanonSite.ring 5}
  | 5 => {CanonSite.hub 1, CanonSite.ring 5, CanonSite.ring 6}
  | 6 => {CanonSite.hub 1, CanonSite.ring 6, CanonSite.ring 7}
  | 7 => {CanonSite.hub 1, CanonSite.ring 7, CanonSite.ring 8}
  | 8 => {CanonSite.hub 1, CanonSite.ring 8, CanonSite.ring 0}
  | 9 => {CanonSite.hub 0, CanonSite.hub 1, CanonSite.ring 0}
  | _ => {CanonSite.hub 0, CanonSite.hub 1, CanonSite.ring 4}

/-- canonical 关联表。 -/
def canonSigma : CanonWitness → Finset CanonSite
  | CanonWitness.switch i => switchAssoc i
  | CanonWitness.face p => faceTri p

/-! ## 1. 站点等价 -/

/-- 环站点 i 的 `Fin 11` 索引。 -/
def ringToFin (i : Fin 9) : Fin 11 := ⟨i.val, by omega⟩

def canonSiteToFin : CanonSite → Fin 11
  | .ring i => ringToFin i
  | .hub h => if h = 0 then 9 else 10

def finToCanonSite (k : Fin 11) : CanonSite :=
  if h : k.val < 9 then .ring ⟨k.val, h⟩ else if k.val = 9 then .hub 0 else .hub 1

theorem canonSite_leftInverse : ∀ s : CanonSite, finToCanonSite (canonSiteToFin s) = s := by
  intro s
  cases s with
  | ring i =>
      have hi : (ringToFin i).val < 9 := i.isLt
      show (if h : (ringToFin i).val < 9 then CanonSite.ring ⟨(ringToFin i).val, h⟩
        else if (ringToFin i).val = 9 then CanonSite.hub 0 else CanonSite.hub 1) = CanonSite.ring i
      rw [dif_pos hi]
      rfl
  | hub h => fin_cases h <;> simp [canonSiteToFin, finToCanonSite]

theorem canonSite_rightInverse : ∀ k : Fin 11, canonSiteToFin (finToCanonSite k) = k := by
  intro k
  by_cases h9 : k.val < 9
  · have hk : finToCanonSite k = CanonSite.ring ⟨k.val, h9⟩ := by
      show (if h : k.val < 9 then CanonSite.ring ⟨k.val, h⟩
        else if k.val = 9 then CanonSite.hub 0 else CanonSite.hub 1) = _
      rw [dif_pos h9]
    rw [hk]
    show ringToFin ⟨k.val, h9⟩ = k
    exact Fin.ext rfl
  · have hk10 : k.val = 10 ∨ k.val = 9 := by have := k.isLt; omega
    rcases hk10 with h10 | h10
    · have hk : finToCanonSite k = CanonSite.hub 1 := by
        show (if h : k.val < 9 then CanonSite.ring ⟨k.val, h⟩
          else if k.val = 9 then CanonSite.hub 0 else CanonSite.hub 1) = _
        rw [dif_neg h9, if_neg (by omega : ¬ k.val = 9)]
      rw [hk]
      -- 需要 `(canonSiteToFin (CanonSite.hub 1)).val = 10`
      have hv : (CanonSite.hub (1 : Fin 2) : CanonSite) ≠ CanonSite.hub 0 := by decide
      have hval : (if h : (1 : Fin 2) = 0 then (9 : Fin 11) else (10 : Fin 11)) = (10 : Fin 11) :=
        dif_neg (by decide : ¬ (1 : Fin 2) = 0)
      rw [show CanonSite.hub 1 = (CanonSite.hub (1 : Fin 2) : CanonSite) from rfl]
      simp only [canonSiteToFin]
      exact Fin.ext (by simpa using h10.symm)
    · have hk : finToCanonSite k = CanonSite.hub 0 := by
        show (if h : k.val < 9 then CanonSite.ring ⟨k.val, h⟩
          else if k.val = 9 then CanonSite.hub 0 else CanonSite.hub 1) = _
        rw [dif_neg h9, if_pos h10]
      rw [hk]
      have hval : (if h : (0 : Fin 2) = 0 then (9 : Fin 11) else (10 : Fin 11)) = (9 : Fin 11) :=
        dif_pos rfl
      rw [show CanonSite.hub 0 = (CanonSite.hub (0 : Fin 2) : CanonSite) from rfl]
      simp only [canonSiteToFin]
      exact Fin.ext (by simpa using h10.symm)

/-- `CanonSite ≃ Fin 11`。 -/
def canonSiteEquiv : CanonSite ≃ Fin 11 where
  toFun := canonSiteToFin
  invFun := finToCanonSite
  left_inv := canonSite_leftInverse
  right_inv := canonSite_rightInverse

/-! ## 2. 表的一致性 -/

/-- 站点编号（与 `canonSiteToFin` 取值一致，作为 `Fin 11`）。 -/
def siteNum : CanonSite → Fin 11
  | .ring i => ringToFin i
  | .hub h => if h = 0 then 9 else 10

theorem siteNum_eq (s : CanonSite) : siteNum s = canonSiteToFin s := by
  cases s <;> rfl

/-- `faceTri p` 经 `siteNum` 的像恰是 `ResumeNetwork.face p` 的三个顶点。 -/
theorem faceTri_num (p : Fin 11) :
    (faceTri p).image siteNum =
      ({(ResumeNetwork.face p 0), (ResumeNetwork.face p 1), (ResumeNetwork.face p 2)} :
        Finset (Fin 11)) := by
  fin_cases p <;> decide

/-- `faceTri p` 经 `canonSiteEquiv` 的像恰是 `ResumeNetwork.face p` 的三个顶点。 -/
theorem faceTri_maps (p : Fin 11) :
    (faceTri p).map canonSiteEquiv.toEmbedding =
      ({ResumeNetwork.face p 0, ResumeNetwork.face p 1, ResumeNetwork.face p 2} :
        Finset (Fin 11)) := by
  rw [← faceTri_num p]
  ext k
  simp only [Finset.mem_image, Finset.mem_map]
  constructor
  · rintro ⟨s, hs, hsk⟩
    refine ⟨s, hs, ?_⟩
    exact hsk
  · rintro ⟨s, hs, hsk⟩
    refine ⟨s, hs, ?_⟩
    exact hsk

/-- `face f v` 的原像落在 `faceTri f` 中。 -/
theorem finToCanonSite_mem_faceTri (f : Fin 11) (v : Fin 3) :
    finToCanonSite (ResumeNetwork.face f v) ∈ faceTri f := by
  have h := faceTri_maps f
  have hmem : ResumeNetwork.face f v ∈ (faceTri f).map canonSiteEquiv.toEmbedding := by
    rw [h]
    fin_cases v <;> simp
  obtain ⟨s, hs, hsv⟩ := Finset.mem_map.mp hmem
  have hkey : finToCanonSite (ResumeNetwork.face f v) = s := by
    rw [← hsv]
    exact canonSite_leftInverse s
  rw [hkey]
  exact hs

/-- `ring i` 的原像。 -/
theorem finToCanonSite_ring (i : Fin 9) : finToCanonSite (ringToFin i) = CanonSite.ring i := by
  have hi : (ringToFin i).val < 9 := i.isLt
  show (if h : (ringToFin i).val < 9 then CanonSite.ring ⟨(ringToFin i).val, h⟩
    else if (ringToFin i).val = 9 then CanonSite.hub 0 else CanonSite.hub 1) = CanonSite.ring i
  rw [dif_pos hi]
  rfl

/-- 开关 i 关联环 i。 -/
theorem ring_mem_switchAssoc_self (i : Fin 9) : CanonSite.ring i ∈ switchAssoc i := by
  simp [switchAssoc]

/-- 开关 `i-1` 关联环 i。 -/
theorem ring_mem_switchAssoc_pred (i : Fin 9) :
    CanonSite.ring i ∈ switchAssoc (i - 1) := by
  have h : nextRing (i - 1) = i := by
    ext
    simp only [nextRing]
    omega
  simp [switchAssoc, h]

/-! ## 3. 见证 ⇒ Feasible ⇒ V2 -/

/-- 见证点指派：switch i ↦ `U i`，face f ↦ `Z f`。 -/
def witnessPoint (U : Fin 9 → Point) (Z : Fin 11 → Point) : CanonWitness → Point
  | .switch i => U i
  | .face f => Z f

/-- 51 条距离界（由最近点见证引理，站点函数取 `C ∘ canonSiteEquiv`）。 -/
theorem edgeLength_le_of_witness
    {C : Fin 11 → Point} {r : ℝ}
    (hcov : ∀ x : Point, x ∈ unitDisk →
      ∃ i, dist x (C (canonSiteEquiv i)) ≤ r)
    {U : Fin 9 → Point} {Z : Fin 11 → Point}
    (hW : ∀ w : CanonWitness, witnessPoint U Z w ∈ unitDisk)
    (hnearest : ∀ w i, i ∈ canonSigma w →
      ∀ k, dist (witnessPoint U Z w) (C (canonSiteEquiv i)) ≤
        dist (witnessPoint U Z w) (C (canonSiteEquiv k))) :
    ∀ w i, i ∈ canonSigma w →
      dist (witnessPoint U Z w) (C (canonSiteEquiv i)) ≤ r :=
  nearest_witness_le_radius hcov hW hnearest

/-- `canonSiteEquiv` 在环站点上的取值。 -/
theorem canonSiteEquiv_ring (i : Fin 9) : canonSiteEquiv (CanonSite.ring i) = ringToFin i := rfl

/-- `canonSiteEquiv` 在开关见证上的取值（`toEmbedding` 即 `canonSiteToFin`）。 -/
theorem canonSiteEquiv_face (f : Fin 11) (v : Fin 3) :
    canonSiteEquiv (finToCanonSite (ResumeNetwork.face f v)) = ResumeNetwork.face f v :=
  canonSite_rightInverse _

/-- **桥主定理（Feasible）**：见证点都在 `D` 内且关联站点都是最近站点 ⇒
`ResumeNetwork.Feasible U C Z r`。 -/
theorem feasible_of_witness
    {C : Fin 11 → Point} {r : ℝ} (hr : 0 ≤ r)
    (hcov : ∀ x : Point, x ∈ unitDisk →
      ∃ i, dist x (C (canonSiteEquiv i)) ≤ r)
    {U : Fin 9 → Point} {Z : Fin 11 → Point}
    (hW : ∀ w : CanonWitness, witnessPoint U Z w ∈ unitDisk)
    (hnearest : ∀ w i, i ∈ canonSigma w →
      ∀ k, dist (witnessPoint U Z w) (C (canonSiteEquiv i)) ≤
        dist (witnessPoint U Z w) (C (canonSiteEquiv k))) :
    ResumeNetwork.Feasible U C Z r := by
  have h51 := edgeLength_le_of_witness hcov hW hnearest
  refine ⟨hr, ?_⟩
  intro e
  rcases e with ⟨i, side⟩ | ⟨f, v⟩
  · fin_cases side
    · have hm : CanonSite.ring i ∈ canonSigma (CanonWitness.switch (i - 1)) := by
        simpa [canonSigma] using ring_mem_switchAssoc_pred i
      have hk := h51 (CanonWitness.switch (i - 1)) (CanonSite.ring i) hm
      rw [canonSiteEquiv_ring] at hk
      simpa [ResumeNetwork.edgeLength, ResumeNetwork.anchorIndex, witnessPoint,
        ringToFin, dist_comm] using hk
    · have hm : CanonSite.ring i ∈ canonSigma (CanonWitness.switch i) := by
        simpa [canonSigma] using ring_mem_switchAssoc_self i
      have hk := h51 (CanonWitness.switch i) (CanonSite.ring i) hm
      rw [canonSiteEquiv_ring] at hk
      simpa [ResumeNetwork.edgeLength, ResumeNetwork.anchorIndex, witnessPoint,
        ringToFin, dist_comm] using hk
  · have hm : finToCanonSite (ResumeNetwork.face f v) ∈ canonSigma (CanonWitness.face f) := by
      simpa [canonSigma] using finToCanonSite_mem_faceTri f v
    have hk := h51 (CanonWitness.face f) (finToCanonSite (ResumeNetwork.face f v)) hm
    rw [canonSiteEquiv_face] at hk
    simpa [ResumeNetwork.edgeLength, witnessPoint, dist_comm] using hk

/-- **桥主定理（oracle 上界）**：`V2 U ≤ r²`（消费 C911 的接口）。 -/
theorem V2_le_sq_of_witness
    {C : Fin 11 → Point} {r : ℝ} (hr : 0 ≤ r)
    (hcov : ∀ x : Point, x ∈ unitDisk →
      ∃ i, dist x (C (canonSiteEquiv i)) ≤ r)
    {U : Fin 9 → Point} {Z : Fin 11 → Point}
    (hW : ∀ w : CanonWitness, witnessPoint U Z w ∈ unitDisk)
    (hnearest : ∀ w i, i ∈ canonSigma w →
      ∀ k, dist (witnessPoint U Z w) (C (canonSiteEquiv i)) ≤
        dist (witnessPoint U Z w) (C (canonSiteEquiv k))) :
    ResumeNetwork.V2 U ≤ r ^ 2 :=
  ResumeNetwork.oracle_le_feasible (feasible_of_witness hr hcov hW hnearest)

end N11Formalization
