/-
n11-formalization —— **generic diagonal flip（线段共点）**，供 tiling 的 central 消费。

写域：`lean/N11Formalization/FlashBoundaryCapsFlip.lean` + `evidence/flash-caps/`。
（其它 flash-caps 文件均已冻结；本文件是**另一个**文件。）

## 0. 目标（lead 转述 tiling 的 central consumer）

设公共点 `q` 同时在两条线段上：`q ∈ [h₀,h₁]` 与 `q ∈ [A,B]`（`A = C₂`、`B = C₆`、`h₀,h₁` 两 hub）。
则“以 `[h₀,h₁]` 为对角线的两块”被“以 `[A,B]` 为对角线的两块”覆盖：

```
conv(h₀,A,B) ∪ conv(h₁,A,B) ⊆ conv(A,h₀,h₁) ∪ conv(B,h₀,h₁)
```

证明只用**边劈**（triangle edge split）与凸性，不需要全 stellar split：

1. `q ∈ [A,B] ⇒ [A,B] ⊆ [A,q] ∪ [q,B]`（1D split）；
2. 星分解：`p ∈ conv{P,A,B} ⇒ ∃ y ∈ [A,B], p ∈ [P,y]`（`convexHull_insert` + `mem_convexJoin`）；
3. 边劈：`conv(P,A,B) ⊆ conv(P,A,q) ∪ conv(P,q,B)`（星分解 + 1D split + 凸性）；
4. `q ∈ [h₀,h₁] ⇒ q ∈ conv(A,h₀,h₁)`、`q ∈ conv(B,h₀,h₁)`（凸性 + `segment ⊆ convexHull`），
   `convexHull_min` 收口。

## 1. 口径与坑

* `Point = EuclideanSpace ℝ (Fin 2)`；`segment`/`convexHull` 取 `ℝ` 上结构。
* `q` 只须落在**闭**线段上（不要求内点）；三点可退化（共线/重合）结论仍成立。
* **坑（已踩）**：`•` 的优先级**高于** `/`，`t / u • X` 会被解析成 `t / (u • X)` ✗；必须写 `(t / u) • X`。
* **坑（已踩）**：`segment_eq_image` 给出的是 `(fun θ => …) t` 形式，`rw [show …]` 匹配不上
  （`rw` 不做 beta 归约）；须先 `change`（走 defeq）再 `rw`。
* 无浮点、无 `sorry`、无自定义 axiom。
-/

import Mathlib
import N11Formalization.Definitions

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section

namespace N11Formalization.FlashBoundaryCapsFlip

open N11Formalization

/-! ## §1 线段上一点劈开线段（1D split） -/

/-- **1D split**：`q ∈ [A,B] ⇒ [A,B] ⊆ [A,q] ∪ [q,B]`。

证明走 `segment_eq_image`（`[A,B] = {(1-t)•A + t•B | t ∈ [0,1]}`）：
给定 `t, u ∈ [0,1]` 为 `y, q` 的参数，若 `t ≤ u` 则 `y = (1 - t/u)•A + (t/u)•q`（`u > 0`），
故 `y ∈ [A,q]`；若 `t ≥ u` 则对 `[q,B]` 同理（`u = 0`/`u = 1` 的退化情形直接归约）。 -/
theorem segment_subset_union_segment {A B q : Point} (hq : q ∈ segment ℝ A B) :
    segment ℝ A B ⊆ segment ℝ A q ∪ segment ℝ q B := by
  intro y hy
  rw [segment_eq_image ℝ A B] at hy hq
  obtain ⟨t, ht, rfl⟩ := hy
  obtain ⟨u, hu, hqu⟩ := hq
  obtain ⟨ht0, ht1⟩ := Set.mem_Icc.mp ht
  obtain ⟨hu0, hu1⟩ := Set.mem_Icc.mp hu
  rcases le_total t u with htu | hut
  · by_cases hu_eq : u = 0
    · have hqA : q = A := by rw [← hqu, hu_eq]; simp
      refine Or.inr ?_
      rw [hqA, segment_eq_image ℝ A B]
      exact ⟨t, ht, rfl⟩
    · have hu_pos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu_eq)
      refine Or.inl ?_
      rw [segment_eq_image ℝ A q]
      refine ⟨t / u, ⟨div_nonneg ht0 hu_pos.le, (div_le_one hu_pos).mpr htu⟩, ?_⟩
      change (1 - t / u) • A + (t / u) • q = (1 - t) • A + t • B
      have hq' : q = (1 - u) • A + u • B := hqu.symm
      rw [hq']
      rw [show (1 - t / u) • A + (t / u) • ((1 - u) • A + u • B)
          = ((1 - t / u) + t / u * (1 - u)) • A + (t / u * u) • B by module]
      have hA : (1 - t / u) + t / u * (1 - u) = 1 - t := by
        field_simp [ne_of_gt hu_pos]; ring
      have hB : t / u * u = t := by field_simp [ne_of_gt hu_pos]
      rw [hA, hB]
  · by_cases hu_eq : u = 1
    · have hqB : q = B := by rw [← hqu, hu_eq]; simp
      refine Or.inl ?_
      rw [hqB, segment_eq_image ℝ A B]
      exact ⟨t, ht, rfl⟩
    · have hu_lt : u < 1 := lt_of_le_of_ne hu1 hu_eq
      have h1u : 0 < 1 - u := by linarith
      refine Or.inr ?_
      rw [segment_eq_image ℝ q B]
      refine ⟨(t - u) / (1 - u), ⟨div_nonneg (by linarith) h1u.le,
        (div_le_one h1u).mpr (by linarith)⟩, ?_⟩
      change (1 - (t - u) / (1 - u)) • q + ((t - u) / (1 - u)) • B = (1 - t) • A + t • B
      have hq' : q = (1 - u) • A + u • B := hqu.symm
      rw [hq']
      rw [show (1 - (t - u) / (1 - u)) • ((1 - u) • A + u • B) + ((t - u) / (1 - u)) • B
          = ((1 - (t - u) / (1 - u)) * (1 - u)) • A
            + ((1 - (t - u) / (1 - u)) * u + (t - u) / (1 - u)) • B by module]
      have hA : (1 - (t - u) / (1 - u)) * (1 - u) = 1 - t := by
        field_simp [ne_of_gt h1u]; ring
      have hB : (1 - (t - u) / (1 - u)) * u + (t - u) / (1 - u) = t := by
        field_simp [ne_of_gt h1u]; ring
      rw [hA, hB]

/-! ## §2 星分解与边劈（triangle edge split） -/

/-- **星分解**：三角形内每点落在「顶点 `P` 到对边 `[A,B]` 上某点」的线段上。 -/
theorem exists_segment_of_mem_convexHull_three {P A B p : Point}
    (hp : p ∈ convexHull ℝ ({P,A,B} : Set Point)) :
    ∃ y ∈ segment ℝ A B, p ∈ segment ℝ P y := by
  have hins : ({P,A,B} : Set Point) = insert P ({A,B} : Set Point) := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hne : (({A,B} : Set Point)).Nonempty := ⟨A, by simp⟩
  rw [hins] at hp
  rw [convexHull_insert (𝕜 := ℝ) (x := P) hne] at hp
  rw [mem_convexJoin] at hp
  obtain ⟨a, ha, b, hb, hab⟩ := hp
  have ha' : a = P := by simpa using ha
  subst ha'
  refine ⟨b, ?_, hab⟩
  rwa [convexHull_pair A B] at hb

/-- `convexHull_min` 的三点包装：三顶点都在凸集 `t` 里 ⇒ 三角形 ⊆ `t`。 -/
theorem convexHull_subset_of_three {X Y Z : Point} {t : Set Point} (ht : Convex ℝ t)
    (hX : X ∈ t) (hY : Y ∈ t) (hZ : Z ∈ t) :
    convexHull ℝ ({X,Y,Z} : Set Point) ⊆ t :=
  convexHull_min (by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hX
    · exact hY
    · exact hZ) ht

/-- **边劈**：`q ∈ [A,B] ⇒ conv{P,A,B} ⊆ conv{P,A,q} ∪ conv{P,q,B}`。 -/
theorem convexHull_triangle_subset_union {P A B q : Point} (hq : q ∈ segment ℝ A B) :
    convexHull ℝ ({P,A,B} : Set Point) ⊆
      convexHull ℝ ({P,A,q} : Set Point) ∪ convexHull ℝ ({P,q,B} : Set Point) := by
  intro p hp
  obtain ⟨y, hyAB, hpy⟩ := exists_segment_of_mem_convexHull_three hp
  rcases segment_subset_union_segment hq hyAB with hy | hy
  · left
    have hA : A ∈ convexHull ℝ ({P,A,q} : Set Point) := subset_convexHull ℝ _ (by simp)
    have hQ : q ∈ convexHull ℝ ({P,A,q} : Set Point) := subset_convexHull ℝ _ (by simp)
    have hy' : y ∈ convexHull ℝ ({P,A,q} : Set Point) :=
      (convex_convexHull ℝ _).segment_subset hA hQ hy
    have hP : P ∈ convexHull ℝ ({P,A,q} : Set Point) := subset_convexHull ℝ _ (by simp)
    exact (convex_convexHull ℝ _).segment_subset hP hy' hpy
  · right
    have hQ : q ∈ convexHull ℝ ({P,q,B} : Set Point) := subset_convexHull ℝ _ (by simp)
    have hB : B ∈ convexHull ℝ ({P,q,B} : Set Point) := subset_convexHull ℝ _ (by simp)
    have hy' : y ∈ convexHull ℝ ({P,q,B} : Set Point) :=
      (convex_convexHull ℝ _).segment_subset hQ hB hy
    have hP : P ∈ convexHull ℝ ({P,q,B} : Set Point) := subset_convexHull ℝ _ (by simp)
    exact (convex_convexHull ℝ _).segment_subset hP hy' hpy

/-! ## §3 **diagonal flip**（lead 转述的 tiling central consumer） -/

theorem diagonal_flip {A B k0 k1 q : Point}
    (hqAB : q ∈ segment ℝ A B) (hqkk : q ∈ segment ℝ k0 k1) :
    convexHull ℝ ({k0,A,B} : Set Point) ∪ convexHull ℝ ({k1,A,B} : Set Point) ⊆
      convexHull ℝ ({A,k0,k1} : Set Point) ∪ convexHull ℝ ({B,k0,k1} : Set Point) := by
  intro p hp
  have hc1 : Convex ℝ (convexHull ℝ ({A,k0,k1} : Set Point)) := convex_convexHull ℝ _
  have hc2 : Convex ℝ (convexHull ℝ ({B,k0,k1} : Set Point)) := convex_convexHull ℝ _
  have hA : A ∈ convexHull ℝ ({A,k0,k1} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hk0 : k0 ∈ convexHull ℝ ({A,k0,k1} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hk1 : k1 ∈ convexHull ℝ ({A,k0,k1} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hqA : q ∈ convexHull ℝ ({A,k0,k1} : Set Point) := hc1.segment_subset hk0 hk1 hqkk
  have hB : B ∈ convexHull ℝ ({B,k0,k1} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hk0' : k0 ∈ convexHull ℝ ({B,k0,k1} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hk1' : k1 ∈ convexHull ℝ ({B,k0,k1} : Set Point) := subset_convexHull ℝ _ (by simp)
  have hqB : q ∈ convexHull ℝ ({B,k0,k1} : Set Point) := hc2.segment_subset hk0' hk1' hqkk
  rcases hp with hp | hp
  · rcases convexHull_triangle_subset_union (P := k0) (A := A) (B := B) hqAB hp with h | h
    · exact Or.inl (convexHull_subset_of_three hc1 hk0 hA hqA h)
    · exact Or.inr (convexHull_subset_of_three hc2 hk0' hqB hB h)
  · rcases convexHull_triangle_subset_union (P := k1) (A := A) (B := B) hqAB hp with h | h
    · exact Or.inl (convexHull_subset_of_three hc1 hk1 hA hqA h)
    · exact Or.inr (convexHull_subset_of_three hc2 hk1' hqB hB h)

end N11Formalization.FlashBoundaryCapsFlip

#print axioms N11Formalization.FlashBoundaryCapsFlip.segment_subset_union_segment
#print axioms N11Formalization.FlashBoundaryCapsFlip.exists_segment_of_mem_convexHull_three
#print axioms N11Formalization.FlashBoundaryCapsFlip.convexHull_subset_of_three
#print axioms N11Formalization.FlashBoundaryCapsFlip.convexHull_triangle_subset_union
#print axioms N11Formalization.FlashBoundaryCapsFlip.diagonal_flip
