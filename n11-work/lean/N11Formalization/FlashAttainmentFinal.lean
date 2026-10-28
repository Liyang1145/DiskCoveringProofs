/-
n11-formalization —— **最终装配（tiling 的 11 面 ⟹ 原 root 达到）**。

写域：本文件 + `evidence/flash-caps/`。

## 0. 链条（lead R-FBC-10 的路线）

```
（我）qcross_exists      ：∃ q, q ∈ [C₂,C₆] ∧ q ∈ [hub0,hub1]        ← 由中点实例给出（本文件 §2）
（我）hflip              ：FlashBoundaryCapsFlip.diagonal_flip        ← 冻结件（已入根）
（tiling）hcv/hh0/hh1/hchordA/hchordB → FlashTiling.hcover_barycentric
                        ：11 面剖分的 barycentric 形式（索引 faceI1/2/3）
（slack）hF0            ：面 0 的 FaceCoverable（固定有理 O0）
（我）hcover_of_tiling   ：上面 ⟹ Root 形状的 hcover（§3，本文件）
（slack）FlashSlackRoot.covers_of_root / exists_root_covers ⟹ Covers (centersOfRoot S.root) (Rstar S)
```

**本文件不证明** tiling 的几何不等式（`hcv`/`hh0`/`hh1`/`hchordA`/`hchordB`，即 lead 说的 “C signs”）
与 slack 的 `hF0`；它们作为**显式前提**传入。本文件负责：索引一致性（`fv1/2/3 ↔ faceI1/2/3`、
`centers11 ↔ centersOfRoot`）、`qcross`、`hflip` 的对接，以及把 Root 形状 `hcover` 交出去。

## 1. 口径

* 中心用 **raw TC 顺序**：`centersOfRoot u`（环 0..8、hub0 = 9、hub1 = 10）；
  tiling 的 `centers11 (ringCenter u) (hub0 u) (hub1 u)` 与之**逐位相同**（§1 证明）。
* 半径/坐标一律原 root；`q` 只需闭线段（退化也成立）。
* 无浮点、无 `sorry`、无自定义 axiom。
-/

import Mathlib
import N11Formalization.FlashBoundaryCapsMidpoint
import N11Formalization.FlashBoundaryCapsFaces
import N11Formalization.FlashTilingHull
import N11Formalization.FlashSlackRoot

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section

namespace N11Formalization.FlashAttainmentFinal

open N11Formalization

/-! ## §1 索引一致性（tiling 的 raw 表 ↔ `centersOfRoot` 的 raw TC 表） -/

/-- `centers11 (ringCenter u) (hub0 u) (hub1 u) = centersOfRoot u`（逐位）。 -/
theorem centers11_eq (u : Fin 12 → ℝ) (f : Fin 11) :
    FlashTiling.centers11 (ringCenter u) (hub0 u) (hub1 u) f = centersOfRoot u f := by
  fin_cases f <;> simp [FlashTiling.centers11, centersOfRoot]

/-- 第 1 顶点：`fv1 (ringCenter u) f = centersOfRoot u (faceI1 f)`。 -/
theorem fv1_eq (u : Fin 12 → ℝ) (f : Fin 11) :
    FlashTiling.fv1 (ringCenter u) f = centersOfRoot u (FlashBoundaryCapsFaces.faceI1 f) := by
  fin_cases f <;>
    simp [FlashTiling.fv1, FlashBoundaryCapsFaces.faceI1, centersOfRoot]

/-- 第 2 顶点：`fv2 (ringCenter u) (hub0 u) f = centersOfRoot u (faceI2 f)`。 -/
theorem fv2_eq (u : Fin 12 → ℝ) (f : Fin 11) :
    FlashTiling.fv2 (ringCenter u) (hub0 u) f = centersOfRoot u (FlashBoundaryCapsFaces.faceI2 f) := by
  fin_cases f <;>
    simp [FlashTiling.fv2, FlashBoundaryCapsFaces.faceI2, centersOfRoot]

/-- 第 3 顶点：`fv3 (ringCenter u) (hub0 u) (hub1 u) f = centersOfRoot u (faceI3 f)`。 -/
theorem fv3_eq (u : Fin 12 → ℝ) (f : Fin 11) :
    FlashTiling.fv3 (ringCenter u) (hub0 u) (hub1 u) f
      = centersOfRoot u (FlashBoundaryCapsFaces.faceI3 f) := by
  fin_cases f <;>
    simp [FlashTiling.fv3, FlashBoundaryCapsFaces.faceI3, centersOfRoot]

/-! ## §2 `qcross`（原 root；由中点实例给出） -/

/-- **公共点 `qcross`**：`∃ q, q ∈ [C₂,C₆] ∧ q ∈ [hub0,hub1]`（原 root，`InCertBox u`）。 -/
theorem qcross_exists (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) :
    ∃ q : Point, q ∈ segment ℝ (ringCenter u 2) (ringCenter u 6) ∧
      q ∈ segment ℝ (hub0 u) (hub1 u) :=
  ⟨FlashBoundaryCapsMidpoint.qinst u, FlashBoundaryCapsMidpoint.qinst_mem_AB u,
    FlashBoundaryCapsMidpoint.qinst_mem_hubs u hu⟩

/-! ## §3 把 tiling 的 11 面结论转成 Root 形状的 `hcover` -/

/-- **Root 形状的 `hcover`**（= `FlashSlackRoot.covers_of_root` 要的形状）：
tiling 的几何前提（`hcv`/`hh0`/`hh1`/`hchordA`/`hchordB`）+ `InCertBox u` ⟹ 11 面 barycentric 表示。 -/
theorem hcover_of_tiling (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u)
    (hcv : FlashTiling.RingConvex (ringCenter u) FlashTiling.succ9)
    (hh0 : ∀ i : Fin 9, 0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 i (hub0 u))
    (hh1 : ∀ i : Fin 9, 0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 i (hub1 u))
    (hchordA : ∀ j : Fin 9, (j = 3 ∨ j = 4 ∨ j = 5) →
      0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 2) (ringCenter u j))
    (hchordB : ∀ j : Fin 9, (j = 7 ∨ j = 8 ∨ j = 0 ∨ j = 1) →
      0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 6) (ringCenter u j)) :
    ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot u)) →
      ∃ n : Fin 11, ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
        p = la • centersOfRoot u (FlashBoundaryCapsFaces.faceI1 n)
              + lb • centersOfRoot u (FlashBoundaryCapsFaces.faceI2 n)
              + lc • centersOfRoot u (FlashBoundaryCapsFaces.faceI3 n) := by
  intro p hp
  have hrange : Set.range (FlashTiling.centers11 (ringCenter u) (hub0 u) (hub1 u))
      = Set.range (centersOfRoot u) := by
    ext z
    simp only [Set.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f, (centers11_eq u f).symm⟩
    · rintro ⟨f, rfl⟩
      exact ⟨f, centers11_eq u f⟩
  have hp' : p ∈ convexHull ℝ (Set.range (FlashTiling.centers11 (ringCenter u) (hub0 u) (hub1 u))) := by
    rwa [hrange]
  obtain ⟨f, hf⟩ := FlashTiling.hull_cover_11 (ringCenter u) (hub0 u) (hub1 u) hcv hh0 hh1
    hchordA hchordB (qcross_exists u hu)
    (fun A B H0 H1 q h1 h2 => FlashBoundaryCapsFlip.diagonal_flip h1 h2) p hp'
  obtain ⟨la, lb, lc, hla, hlb, hlc, hsum, hrep⟩ := FlashTiling.mem_convexHull_three hf
  refine ⟨f, la, lb, lc, hla, hlb, hlc, hsum, ?_⟩
  rw [hrep, ← fv1_eq u f, ← fv2_eq u f, ← fv3_eq u f]

/-! ## §4 端到端（原 root 达到；**只剩 tiling 的 C signs**，无 slack/hF0 前提） -/

/-- `InCertBox S.root` **由 S 的字段导出**（不新增前提）：
`root_mem` 给盒内 + `hlo`/`hhi` 把盒改写成证书盒。 -/
theorem inCertBox_root (S : C891RootSpec) (hlo : S.boxLo = boxLoCert) (hhi : S.boxHi = boxHiCert) :
    RootRangeBoxFull.InCertBox S.root := by
  intro i
  have h := S.root_mem.1 i
  rw [hlo, hhi] at h
  exact h

/-- **原 root 达到（装配件）**：给 tiling 的几何前提（对**每个** `S`），
则 `nd_box_final` 的根被 11 个半径 `Rstar S` 的盘覆盖。

**前提表（照实际源，非记忆）**：`FlashSlackRoot.exists_root_covers` 的完整 type 只吃
`hcover`（形如 `∀ S, sys → boxLo → boxHi → radiusIndex → 11 面 barycentric`），
其结论即 `∃ S, sys ∧ boxLo ∧ boxHi ∧ radiusIndex = 6 ∧ Rstar S < 19/50 ∧ Covers …`；
`covers_of_root` 亦只吃 `hsys/hlo/hhi/hidx/hcover`（**无 hF0**）。
本定理把 `hcover` 由 §3（tiling 的 C signs）供给后**直接委派**给 `exists_root_covers`。 -/
theorem exists_root_covers_of_tiling
    (hcv : ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 → FlashTiling.RingConvex (ringCenter S.root) FlashTiling.succ9)
    (hh0 : ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 →
      ∀ i : Fin 9, 0 ≤ FlashTiling.phi (ringCenter S.root) FlashTiling.succ9 i (hub0 S.root))
    (hh1 : ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 →
      ∀ i : Fin 9, 0 ≤ FlashTiling.phi (ringCenter S.root) FlashTiling.succ9 i (hub1 S.root))
    (hchordA : ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 →
      ∀ j : Fin 9, (j = 3 ∨ j = 4 ∨ j = 5) →
        0 < FlashTiling.orient (ringCenter S.root 6) (ringCenter S.root 2) (ringCenter S.root j))
    (hchordB : ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 →
      ∀ j : Fin 9, (j = 7 ∨ j = 8 ∨ j = 0 ∨ j = 1) →
        0 < FlashTiling.orient (ringCenter S.root 2) (ringCenter S.root 6) (ringCenter S.root j)) :
    ∃ S : C891RootSpec, S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧
      S.radiusIndex = 6 ∧ Rstar S < 19 / 50 ∧ Covers (centersOfRoot S.root) (Rstar S) :=
  FlashSlackRoot.exists_root_covers (fun S hs hlo hhi hidx =>
    hcover_of_tiling S.root (inCertBox_root S hlo hhi) (hcv S hs hlo hhi hidx)
      (hh0 S hs hlo hhi hidx) (hh1 S hs hlo hhi hidx) (hchordA S hs hlo hhi hidx)
      (hchordB S hs hlo hhi hidx))

/-! ## §5 actual Signs 打包消费者（把终结论前提压成一条） -/

/-- **actual signs**：tiling 的 11 面装配所需的**五组**几何/符号条件（对配置 `u` 打包）。
（`RingConvex`＝环严格凸 CCW；`phi ≥ 0`＝两 hub 在环凸包内；`orient` 两式＝弦 `[C₂,C₆]` 两侧号。） -/
structure ActualSigns (u : Fin 12 → ℝ) : Prop where
  /-- 环严格凸 CCW（63 条定向不等式）。 -/
  hcv : FlashTiling.RingConvex (ringCenter u) FlashTiling.succ9
  /-- `hub0` 在环凸包内（18 条）。 -/
  hh0 : ∀ i : Fin 9, 0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 i (hub0 u)
  /-- `hub1` 在环凸包内（18 条）。 -/
  hh1 : ∀ i : Fin 9, 0 ≤ FlashTiling.phi (ringCenter u) FlashTiling.succ9 i (hub1 u)
  /-- 弦 `[C₂,C₆]` 的 `A` 侧号（`j = 3,4,5`）。 -/
  hchordA : ∀ j : Fin 9, (j = 3 ∨ j = 4 ∨ j = 5) →
    0 < FlashTiling.orient (ringCenter u 6) (ringCenter u 2) (ringCenter u j)
  /-- 弦 `[C₂,C₆]` 的 `B` 侧号（`j = 7,8,0,1`）。 -/
  hchordB : ∀ j : Fin 9, (j = 7 ∨ j = 8 ∨ j = 0 ∨ j = 1) →
    0 < FlashTiling.orient (ringCenter u 2) (ringCenter u 6) (ringCenter u j)

/-- **`hcover` 的 signs 版**：`InCertBox u` + `ActualSigns u` ⟹ Root 形状 `hcover`。 -/
theorem hcover_of_signs (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u)
    (hs : ActualSigns u) :
    ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot u)) →
      ∃ n : Fin 11, ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
        p = la • centersOfRoot u (FlashBoundaryCapsFaces.faceI1 n)
              + lb • centersOfRoot u (FlashBoundaryCapsFaces.faceI2 n)
              + lc • centersOfRoot u (FlashBoundaryCapsFaces.faceI3 n) :=
  hcover_of_tiling u hu hs.hcv hs.hh0 hs.hh1 hs.hchordA hs.hchordB

/-- **终结论（signs 版，前提压成一条）**：只需「每个 S 满足 `ActualSigns S.root`」，
即得原 root 达到（11 个 `Rstar S` 盘覆盖）。 -/
theorem exists_root_covers_of_signs
    (hs : ∀ (S : C891RootSpec), S.sys = TCSystem → S.boxLo = boxLoCert → S.boxHi = boxHiCert →
      S.radiusIndex = 6 → ActualSigns S.root) :
    ∃ S : C891RootSpec, S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧
      S.radiusIndex = 6 ∧ Rstar S < 19 / 50 ∧ Covers (centersOfRoot S.root) (Rstar S) :=
  exists_root_covers_of_tiling (fun S a b c d => (hs S a b c d).hcv)
    (fun S a b c d => (hs S a b c d).hh0) (fun S a b c d => (hs S a b c d).hh1)
    (fun S a b c d => (hs S a b c d).hchordA) (fun S a b c d => (hs S a b c d).hchordB)

end N11Formalization.FlashAttainmentFinal

#print axioms N11Formalization.FlashAttainmentFinal.centers11_eq
#print axioms N11Formalization.FlashAttainmentFinal.fv1_eq
#print axioms N11Formalization.FlashAttainmentFinal.fv2_eq
#print axioms N11Formalization.FlashAttainmentFinal.fv3_eq
#print axioms N11Formalization.FlashAttainmentFinal.qcross_exists
#print axioms N11Formalization.FlashAttainmentFinal.hcover_of_tiling
#print axioms N11Formalization.FlashAttainmentFinal.inCertBox_root
#print axioms N11Formalization.FlashAttainmentFinal.exists_root_covers_of_tiling
#print axioms N11Formalization.FlashAttainmentFinal.hcover_of_signs
#print axioms N11Formalization.FlashAttainmentFinal.exists_root_covers_of_signs
