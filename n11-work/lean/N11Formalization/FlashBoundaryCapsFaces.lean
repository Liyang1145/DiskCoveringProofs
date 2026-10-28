/-
n11-formalization —— **真实面的 `hO` 数据装配（原 root `u`，raw TC 索引）**

写域：`lean/N11Formalization/FlashBoundaryCapsFaces.lean` + `evidence/flash-caps/`。
（`FlashBoundaryCaps.lean` 已冻结并已入根：SHA256 `F6C7F3AB…E371`，`caps-9.log`，
lead 的 `root-caps-stress-build.log` exit 0 / 8895 jobs；本文件是**另一个**文件。）

## 0. 本文件做什么

`FlashBoundaryCaps.hull_covered_of_triangles` 需要**每面**的 `hO` 数据：面 = 三顶点
（`Fin 11` 的 **raw TC 索引**：环 `0..8` = `ringCenter u k`，`9` = `hub0`，`10` = `hub1`，
**不做任何 canonical/重排**）+ 公共点 `O`，三顶点到 `O` 距离都 ≤ `u 6`。

本文件把**已证活跃面**的 `hO` 数据逐面钉出（不碰 tiling 的 `hcover`，不重做三角覆盖）：

| 面 | 三顶点（raw TC） | `O` | hub 距离来源 |
|---|---|---|---|
| F1 | (1, 2, 10) | `Uvec u 1` | `residual u 0 = 0`（`dist_U1_hub1`） |
| F2 | (2, 3, 9) | `Uvec u 2` | `residual u 1 = 0`（`dist_U2_hub0`） |
| F3 | (3, 4, 9) | `Uvec u 3` | `residual u 2 = 0`（`dist_U3_hub0`） |
| F8 | (8, 0, 10) | `Uvec u 8` | `residual u 3 = 0`（`dist_U8_hub1`） |
| F6 | (6, 7, 10) | `refl (Uvec u 1)` | 镜像（`rc7`/`rc6`/`hub_mirror1`）+ residual 0 |
| F5 | (5, 6, 9) | `refl (Uvec u 2)` | 镜像 + residual 1 |
| F4 | (4, 5, 9) | `refl (Uvec u 3)` | 镜像 + residual 2 |

环顶点距离全部用**一般 `u`** 的已证共点引理 `dist_Uvec_ringCenter_self/succ`
（只需 `RootRange.hsin/hR`），**不含**数值余量。

**未证面**不冒称完成：本文件只给 **`FaceCoverable`**（= `∃O` 使三顶点距离 ≤ `u 6`，
恰是 `hO` 的逐面形状）与**adapter** `hull_covered_of_faceOK`，
把“每面 `FaceCoverable`”变成 `hull_covered_of_triangles` 需要的 `hO`。
承重的两个未付前提：**面 0**（`hF0 : FaceCoverable u ⟨0,_⟩ ⟨1,_⟩ 10`，归 flash-slack 的固定有理 `O0`）
与 **`hcover`**（11 面剖分，归 flash-tiling）；**面 7** 已由面 0 镜像消掉（`faceOK_F7_of_F0`）。

## 1. 口径

* 半径 = **原 root 坐标 `u 6`**（无 `qR`/`uCert` 替换）；中心 = `centersOfRoot u`（raw TC 索引）。
* 全部是 kernel 结论；无浮点、无 `sorry`、无自定义 axiom。
-/

import Mathlib
import N11Formalization.TCSystem
import N11Formalization.Assembly.G2Unified
import N11Formalization.ResumeAttainmentAnnulusFace
import N11Formalization.ResumeAttainmentMirror
import N11Formalization.ResumeAttainmentCentral2
import N11Formalization.RootRangeBoxFull
import N11Formalization.FlashBoundaryCaps

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section

namespace N11Formalization.FlashBoundaryCapsFaces

open N11Formalization
open N11Formalization.ResumeAttainment (refl dist_mirror rc_mirror rc7 rc6 rc5 rc4 rc2_of_6
  hub_mirror0 hub_mirror1 dist_U1_hub1 dist_U2_hub0 dist_U3_hub0 dist_U8_hub1 dist_W_C6
  dist_W_hub0 dist_W_hub1 hW_of_box)

/-! ## §1 环顶点距离的两种搬运（一般 `u`，只用 `RootRange`） -/

theorem dist_ring_self_le (u : Fin 12 → ℝ) (H : RootRange u) (k : Fin 9) :
    dist (ringCenter u k) (Uvec u k) ≤ u 6 :=
  le_of_eq (by rw [dist_comm]; exact dist_Uvec_ringCenter_self u H.hsin H.hR k)

theorem dist_ring_succ_le (u : Fin 12 → ℝ) (H : RootRange u) (k : Fin 9) :
    dist (ringCenter u (k + 1)) (Uvec u k) ≤ u 6 :=
  le_of_eq (by rw [dist_comm]; exact dist_Uvec_ringCenter_succ u H.hsin H.hR k)

/-- 反射搬运：`x` 是 `x'` 的反射（y ↦ −y），则 `x` 到 `refl O` 的距离 = `x'` 到 `O` 的距离。 -/
theorem dist_refl_le {x x' O : Point} {R : ℝ} (h0 : x.ofLp 0 = x'.ofLp 0)
    (h1 : x.ofLp 1 = -(x'.ofLp 1)) (h : dist x' O ≤ R) : dist x (refl O) ≤ R := by
  rw [dist_mirror h0 h1]; exact h

/-! ## §2 四个活跃 U 面（`residual u = 0` 精确供给 hub 距离） -/

/-- 面 F1 = (C_1, C_2, H1)，`O = Uvec u 1`。 -/
theorem hO_F1 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    dist (centersOfRoot u ⟨1, by omega⟩) (Uvec u 1) ≤ u 6 ∧
    dist (centersOfRoot u ⟨2, by omega⟩) (Uvec u 1) ≤ u 6 ∧
    dist (centersOfRoot u 10) (Uvec u 1) ≤ u 6 := by
  have h1 : centersOfRoot u ⟨1, by omega⟩ = ringCenter u 1 := centersOfRoot_ring u 1
  have h2 : centersOfRoot u ⟨2, by omega⟩ = ringCenter u 2 := centersOfRoot_ring u 2
  have h3 : centersOfRoot u 10 = hub1 u := centersOfRoot_ten u
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact dist_ring_self_le u H 1
  · rw [h2]; exact dist_ring_succ_le u H 1
  · rw [h3]; exact le_of_eq (dist_comm (hub1 u) (Uvec u 1) ▸ dist_U1_hub1 u hres)

/-- 面 F2 = (C_2, C_3, H0)，`O = Uvec u 2`。 -/
theorem hO_F2 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    dist (centersOfRoot u ⟨2, by omega⟩) (Uvec u 2) ≤ u 6 ∧
    dist (centersOfRoot u ⟨3, by omega⟩) (Uvec u 2) ≤ u 6 ∧
    dist (centersOfRoot u 9) (Uvec u 2) ≤ u 6 := by
  have h1 : centersOfRoot u ⟨2, by omega⟩ = ringCenter u 2 := centersOfRoot_ring u 2
  have h2 : centersOfRoot u ⟨3, by omega⟩ = ringCenter u 3 := centersOfRoot_ring u 3
  have h3 : centersOfRoot u 9 = hub0 u := centersOfRoot_nine u
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact dist_ring_self_le u H 2
  · rw [h2]; exact dist_ring_succ_le u H 2
  · rw [h3]; exact le_of_eq (dist_comm (hub0 u) (Uvec u 2) ▸ dist_U2_hub0 u hres)

/-- 面 F3 = (C_3, C_4, H0)，`O = Uvec u 3`。 -/
theorem hO_F3 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    dist (centersOfRoot u ⟨3, by omega⟩) (Uvec u 3) ≤ u 6 ∧
    dist (centersOfRoot u ⟨4, by omega⟩) (Uvec u 3) ≤ u 6 ∧
    dist (centersOfRoot u 9) (Uvec u 3) ≤ u 6 := by
  have h1 : centersOfRoot u ⟨3, by omega⟩ = ringCenter u 3 := centersOfRoot_ring u 3
  have h2 : centersOfRoot u ⟨4, by omega⟩ = ringCenter u 4 := centersOfRoot_ring u 4
  have h3 : centersOfRoot u 9 = hub0 u := centersOfRoot_nine u
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact dist_ring_self_le u H 3
  · rw [h2]; exact dist_ring_succ_le u H 3
  · rw [h3]; exact le_of_eq (dist_comm (hub0 u) (Uvec u 3) ▸ dist_U3_hub0 u hres)

/-- 面 F8 = (C_8, C_0, H1)，`O = Uvec u 8`。 -/
theorem hO_F8 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    dist (centersOfRoot u ⟨8, by omega⟩) (Uvec u 8) ≤ u 6 ∧
    dist (centersOfRoot u ⟨0, by omega⟩) (Uvec u 8) ≤ u 6 ∧
    dist (centersOfRoot u 10) (Uvec u 8) ≤ u 6 := by
  have h1 : centersOfRoot u ⟨8, by omega⟩ = ringCenter u 8 := centersOfRoot_ring u 8
  have h2 : centersOfRoot u ⟨0, by omega⟩ = ringCenter u 0 := centersOfRoot_ring u 0
  have h3 : centersOfRoot u 10 = hub1 u := centersOfRoot_ten u
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact dist_ring_self_le u H 8
  · rw [h2]; exact dist_ring_succ_le u H 8
  · rw [h3]; exact le_of_eq (dist_comm (hub1 u) (Uvec u 8) ▸ dist_U8_hub1 u hres)

/-! ## §3 三个镜像 U 面（`O` = `refl U_k`） -/

/-- 面 F6 = (C_6, C_7, H1)，`O = refl (Uvec u 1)`。 -/
theorem hO_F6 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    dist (centersOfRoot u ⟨6, by omega⟩) (refl (Uvec u 1)) ≤ u 6 ∧
    dist (centersOfRoot u ⟨7, by omega⟩) (refl (Uvec u 1)) ≤ u 6 ∧
    dist (centersOfRoot u 10) (refl (Uvec u 1)) ≤ u 6 := by
  have h1 : centersOfRoot u ⟨6, by omega⟩ = ringCenter u 6 := centersOfRoot_ring u 6
  have h2 : centersOfRoot u ⟨7, by omega⟩ = ringCenter u 7 := centersOfRoot_ring u 7
  have h3 : centersOfRoot u 10 = hub1 u := centersOfRoot_ten u
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact dist_refl_le (rc6 u).1 (rc6 u).2 (dist_ring_succ_le u H 1)
  · rw [h2]; exact dist_refl_le (rc7 u).1 (rc7 u).2 (dist_ring_self_le u H 1)
  · rw [h3]
    exact dist_refl_le (hub_mirror1 u).1 (hub_mirror1 u).2
      (le_of_eq (dist_comm (hub1 u) (Uvec u 1) ▸ dist_U1_hub1 u hres))

/-- 面 F5 = (C_5, C_6, H0)，`O = refl (Uvec u 2)`。 -/
theorem hO_F5 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    dist (centersOfRoot u ⟨5, by omega⟩) (refl (Uvec u 2)) ≤ u 6 ∧
    dist (centersOfRoot u ⟨6, by omega⟩) (refl (Uvec u 2)) ≤ u 6 ∧
    dist (centersOfRoot u 9) (refl (Uvec u 2)) ≤ u 6 := by
  have h1 : centersOfRoot u ⟨5, by omega⟩ = ringCenter u 5 := centersOfRoot_ring u 5
  have h2 : centersOfRoot u ⟨6, by omega⟩ = ringCenter u 6 := centersOfRoot_ring u 6
  have h3 : centersOfRoot u 9 = hub0 u := centersOfRoot_nine u
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact dist_refl_le (rc5 u).1 (rc5 u).2 (dist_ring_succ_le u H 2)
  · rw [h2]; exact dist_refl_le (rc6 u).1 (rc6 u).2 (dist_ring_self_le u H 2)
  · rw [h3]
    exact dist_refl_le (hub_mirror0 u).1 (hub_mirror0 u).2
      (le_of_eq (dist_comm (hub0 u) (Uvec u 2) ▸ dist_U2_hub0 u hres))

/-- 面 F4 = (C_4, C_5, H0)，`O = refl (Uvec u 3)`。 -/
theorem hO_F4 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    dist (centersOfRoot u ⟨4, by omega⟩) (refl (Uvec u 3)) ≤ u 6 ∧
    dist (centersOfRoot u ⟨5, by omega⟩) (refl (Uvec u 3)) ≤ u 6 ∧
    dist (centersOfRoot u 9) (refl (Uvec u 3)) ≤ u 6 := by
  have h1 : centersOfRoot u ⟨4, by omega⟩ = ringCenter u 4 := centersOfRoot_ring u 4
  have h2 : centersOfRoot u ⟨5, by omega⟩ = ringCenter u 5 := centersOfRoot_ring u 5
  have h3 : centersOfRoot u 9 = hub0 u := centersOfRoot_nine u
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; exact dist_refl_le (rc4 u).1 (rc4 u).2 (dist_ring_succ_le u H 3)
  · rw [h2]; exact dist_refl_le (rc5 u).1 (rc5 u).2 (dist_ring_self_le u H 3)
  · rw [h3]
    exact dist_refl_le (hub_mirror0 u).1 (hub_mirror0 u).2
      (le_of_eq (dist_comm (hub0 u) (Uvec u 3) ▸ dist_U3_hub0 u hres))

/-! ## §4 逐面 `hO` 形状与 adapter（把“每面可覆盖”变成 `hO`） -/

/-- **逐面 `hO` 形状**：三顶点（raw TC 索引）有一个公共点 `O`，到三顶点距离都 ≤ `u 6`。

这正是 `hull_covered_of_triangles` 的 `hO` 在单面上的内容；
**未证面**只需以此形状作为显式小前提（不冒称完成）。 -/
def FaceCoverable (u : Fin 12 → ℝ) (i1 i2 i3 : Fin 11) : Prop :=
  ∃ O : Point, dist (centersOfRoot u i1) O ≤ u 6 ∧ dist (centersOfRoot u i2) O ≤ u 6 ∧
    dist (centersOfRoot u i3) O ≤ u 6

/-- **adapter**：若三角化的每面都 `FaceCoverable`，则 `hull_covered_of_triangles` 的 `hO` 成立。 -/
theorem hO_of_faceOK (u : Fin 12 → ℝ) (N : ℕ) (i1 i2 i3 : Fin N → Fin 11)
    (hOK : ∀ n : Fin N, FaceCoverable u (i1 n) (i2 n) (i3 n)) :
    ∃ O : Fin N → Point, ∀ n : Fin N, dist (centersOfRoot u (i1 n)) (O n) ≤ u 6 ∧
      dist (centersOfRoot u (i2 n)) (O n) ≤ u 6 ∧
      dist (centersOfRoot u (i3 n)) (O n) ≤ u 6 :=
  ⟨fun n => Classical.choose (hOK n), fun n => Classical.choose_spec (hOK n)⟩

/-- **端到端（三角化版，`FaceCoverable` 形式）**：`RootRange u` + 有限三角化数据
（每面 `FaceCoverable` + 凸包表示）⟹ `Covers (centersOfRoot u) (u 6)`。 -/
theorem covers_of_faceOK (u : Fin 12 → ℝ) (H : RootRange u) (N : ℕ)
    (i1 i2 i3 : Fin N → Fin 11)
    (hOK : ∀ n : Fin N, FaceCoverable u (i1 n) (i2 n) (i3 n))
    (hcover : ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot u)) →
      ∃ n : Fin N, ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
        p = la • centersOfRoot u (i1 n) + lb • centersOfRoot u (i2 n)
              + lc • centersOfRoot u (i3 n)) :
    Covers (centersOfRoot u) (u 6) := by
  obtain ⟨O, hO⟩ := hO_of_faceOK u N i1 i2 i3 hOK
  exact FlashBoundaryCaps.covers_of_triangulation u H N i1 i2 i3 O hO hcover

/-- **7 个已知面的 `FaceCoverable`（raw TC 索引清单）**：
F1=(1,2,10)、F2=(2,3,9)、F3=(3,4,9)、F8=(8,0,10)、F6=(6,7,10)、F5=(5,6,9)、F4=(4,5,9)。
（`residual u = 0` + `RootRange u`。） -/
theorem faceOK_F1 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    FaceCoverable u ⟨1, by omega⟩ ⟨2, by omega⟩ 10 :=
  ⟨Uvec u 1, hO_F1 u H hres⟩

theorem faceOK_F2 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    FaceCoverable u ⟨2, by omega⟩ ⟨3, by omega⟩ 9 :=
  ⟨Uvec u 2, hO_F2 u H hres⟩

theorem faceOK_F3 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    FaceCoverable u ⟨3, by omega⟩ ⟨4, by omega⟩ 9 :=
  ⟨Uvec u 3, hO_F3 u H hres⟩

theorem faceOK_F8 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    FaceCoverable u ⟨8, by omega⟩ ⟨0, by omega⟩ 10 :=
  ⟨Uvec u 8, hO_F8 u H hres⟩

theorem faceOK_F6 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    FaceCoverable u ⟨6, by omega⟩ ⟨7, by omega⟩ 10 :=
  ⟨refl (Uvec u 1), hO_F6 u H hres⟩

theorem faceOK_F5 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    FaceCoverable u ⟨5, by omega⟩ ⟨6, by omega⟩ 9 :=
  ⟨refl (Uvec u 2), hO_F5 u H hres⟩

theorem faceOK_F4 (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    FaceCoverable u ⟨4, by omega⟩ ⟨5, by omega⟩ 9 :=
  ⟨refl (Uvec u 3), hO_F4 u H hres⟩

/-! ## §5 两个未证面：**旧**（被 §5bis 取代，**不承重**）

未证的环边是 `{0,1}` 与 `{7,8}`（raw TC）。本节一度把两面归约到 `dist (hub1 u) (Uvec u 0) ≤ u 6`；
**该接口已被 lead 否决**（slack 的 O 是固定有理点 `O0`，与 `Uvec u 0` 不等价；L287–289 记录符号纠错）。
**当前承重接口 = §5bis 的 `hF0 : FaceCoverable u 0 1 10`**，`faceOK_table` 只消费它。
本节余下的 `faceOK_F0_H1`/`faceOK_F0_H0`/`faceOK_F7_H1` 保留为历史留痕与 H0 备件。 -/

/-- 环 8 ~ 环 0 的镜像恒等式（`θ_8 = −θ_0`、`a_8 = a_0`；用 `ArcCover` 的 `thetaOf_eight`/`thetaOf_zero`）。 -/
theorem rc8 (u : Fin 12 → ℝ) :
    (ringCenter u 8).ofLp 0 = (ringCenter u 0).ofLp 0 ∧
    (ringCenter u 8).ofLp 1 = -((ringCenter u 0).ofLp 1) := by
  refine rc_mirror u 0 8 ?_ ?_
  · exact angleVec_eight_eq_zero u
  · rw [thetaOf_eight, thetaOf_zero]; ring

/-! ## §5bis **面 7 = 面 0 的镜像**（对**任意** `O`，无需 Uvec 0）

lead 指定：slack 的 O 是固定有理点（`O0 = (-385882560178,-295977251136)/1e12`），
只保证 `(C_0, C_1, H1)` 三顶点距 `O0` ≤ `u 6`（= `FaceCoverable u 0 1 10`）。
**这与 `Uvec u 0` 无关**（旧 `hslack : dist (hub1 u) (Uvec u 0) ≤ u 6` 作历史保留、**不承重**）。

由回文镜像 `rc7`（`C_7 = refl C_1`）、`rc8`（`C_8 = refl C_0`，本文件新增）、`hub_mirror1`（`H1` 在 x 轴）：
面 0 的任意见证 `O` 直接给出面 7 的见证 `refl O`。 -/

/-- **面 7 由面 0 的任意见证镜像得到**：`FaceCoverable u 0 1 10 → FaceCoverable u 7 8 10`。 -/
theorem faceOK_F7_of_F0 (u : Fin 12 → ℝ)
    (hF0 : FaceCoverable u ⟨0, by omega⟩ ⟨1, by omega⟩ 10) :
    FaceCoverable u ⟨7, by omega⟩ ⟨8, by omega⟩ 10 := by
  obtain ⟨O, h0, h1, h2⟩ := hF0
  have e0 : centersOfRoot u ⟨0, by omega⟩ = ringCenter u 0 := centersOfRoot_ring u 0
  have e1 : centersOfRoot u ⟨1, by omega⟩ = ringCenter u 1 := centersOfRoot_ring u 1
  have e10 : centersOfRoot u 10 = hub1 u := centersOfRoot_ten u
  rw [e0] at h0
  rw [e1] at h1
  rw [e10] at h2
  have f7 : centersOfRoot u ⟨7, by omega⟩ = ringCenter u 7 := centersOfRoot_ring u 7
  have f8 : centersOfRoot u ⟨8, by omega⟩ = ringCenter u 8 := centersOfRoot_ring u 8
  have f10 : centersOfRoot u 10 = hub1 u := centersOfRoot_ten u
  exact ⟨refl O, by rw [f7]; exact dist_refl_le (rc7 u).1 (rc7 u).2 h1,
    by rw [f8]; exact dist_refl_le (rc8 u).1 (rc8 u).2 h0,
    by rw [f10]; exact dist_refl_le (hub_mirror1 u).1 (hub_mirror1 u).2 h2⟩

/-! ## §5ter 历史（**不承重**）：基于 `Uvec u 0` 的 slack 版本

以下三条把面 0/7 归约到 `dist (hub1 u) (Uvec u 0) ≤ u 6`。lead 已指示**不用**该前提
（slack 的 O 是固定有理点 `O0 = (-385882560178,-295977251136)/1e12`，与 `Uvec u 0` 不等价）。
**符号记录（lead 复跑后更正）**：`STATUS.md` L12（STATUS9）原记「U0/U7 作外心在盒心处数值距离
**超** R 约 0.00284」；lead 已实跑 `evidence/flash-caps/EXP-11-*` 并确认该符号**写反**——
实为 `R − dist = +2.838987e−03`（U0 在 R **内侧**），STATUS/DEAD 已更正并追下游。
**保留仅作历史留痕与 H0 备件；`faceOK_table` 不再消费它们。** -/

/-- 未证面 (C_0,C_1,H1)：**只需** `dist (hub1 u) (Uvec u 0) ≤ u 6`（**历史，不承重**）。 -/
theorem faceOK_F0_H1 (u : Fin 12 → ℝ) (H : RootRange u)
    (h : dist (hub1 u) (Uvec u 0) ≤ u 6) :
    FaceCoverable u ⟨0, by omega⟩ ⟨1, by omega⟩ 10 := by
  have h1 : centersOfRoot u ⟨0, by omega⟩ = ringCenter u 0 := centersOfRoot_ring u 0
  have h2 : centersOfRoot u ⟨1, by omega⟩ = ringCenter u 1 := centersOfRoot_ring u 1
  have h3 : centersOfRoot u 10 = hub1 u := centersOfRoot_ten u
  exact ⟨Uvec u 0, by rw [h1]; exact dist_ring_self_le u H 0,
    by rw [h2]; exact dist_ring_succ_le u H 0, by rw [h3]; exact h⟩

/-- 未证面 (C_0,C_1,H0)：`dist (hub0 u) (Uvec u 0) ≤ u 6` 的备选三角 `(0,1,9)`
（**不属于 lead 的 11 面表**；历史备件，勿混用）。 -/
theorem faceOK_F0_H0 (u : Fin 12 → ℝ) (H : RootRange u)
    (h : dist (hub0 u) (Uvec u 0) ≤ u 6) :
    FaceCoverable u ⟨0, by omega⟩ ⟨1, by omega⟩ 9 := by
  have h1 : centersOfRoot u ⟨0, by omega⟩ = ringCenter u 0 := centersOfRoot_ring u 0
  have h2 : centersOfRoot u ⟨1, by omega⟩ = ringCenter u 1 := centersOfRoot_ring u 1
  have h3 : centersOfRoot u 9 = hub0 u := centersOfRoot_nine u
  exact ⟨Uvec u 0, by rw [h1]; exact dist_ring_self_le u H 0,
    by rw [h2]; exact dist_ring_succ_le u H 0, by rw [h3]; exact h⟩

/-- 未证面 (C_7,C_8,H1)：**同一条** `dist (hub1 u) (Uvec u 0) ≤ u 6`（**历史，不承重**）。 -/
theorem faceOK_F7_H1 (u : Fin 12 → ℝ) (H : RootRange u)
    (h : dist (hub1 u) (Uvec u 0) ≤ u 6) :
    FaceCoverable u ⟨7, by omega⟩ ⟨8, by omega⟩ 10 := by
  have h1 : centersOfRoot u ⟨7, by omega⟩ = ringCenter u 7 := centersOfRoot_ring u 7
  have h2 : centersOfRoot u ⟨8, by omega⟩ = ringCenter u 8 := centersOfRoot_ring u 8
  have h3 : centersOfRoot u 10 = hub1 u := centersOfRoot_ten u
  exact ⟨refl (Uvec u 0),
    by rw [h1]; exact dist_refl_le (rc7 u).1 (rc7 u).2 (dist_ring_succ_le u H 0),
    by rw [h2]; exact dist_refl_le (rc8 u).1 (rc8 u).2 (dist_ring_self_le u H 0),
    by rw [h3]; exact dist_refl_le (hub_mirror1 u).1 (hub_mirror1 u).2 h⟩

/-! ## §6 两个中心面（`(2,9,10)` 与 `(6,9,10)`，raw TC；lead 给定的 11 面表后两项）

* `(6,9,10)` = W 面，`O = wPoint u`（`ResumeAttainmentFace2.W_face_cover` 的同一组距离：
  `dist_W_C6`（residual 4 = 0）、`dist_W_hub0`/`dist_W_hub1`（需 `hR` 与 `hW`））；
* `(2,9,10)` = 其镜像面，`O = refl (wPoint u)`（`rc2_of_6` = `rc6` 的反向）。

盒版用 `InCertBox` 供给 `hR = (ha_hapi_of_box u hu).1` 与 `hW = hW_of_box u hu`（Face3 已证）。 -/

/-- 中心面 (C_6, H0, H1)，`O = wPoint u`。 -/
theorem faceOK_C6 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) (hres : residual u = 0) :
    FaceCoverable u ⟨6, by omega⟩ 9 10 := by
  have hR : 0 ≤ u 6 := (RootRangeBoxFull.ha_hapi_of_box u hu).1
  have hW : ((u 5 - u 4) / 2) ^ 2 ≤ (u 6) ^ 2 := hW_of_box u hu
  have h1 : centersOfRoot u ⟨6, by omega⟩ = ringCenter u 6 := centersOfRoot_ring u 6
  have h2 : centersOfRoot u 9 = hub0 u := centersOfRoot_nine u
  have h3 : centersOfRoot u 10 = hub1 u := centersOfRoot_ten u
  exact ⟨wPoint u,
    by rw [h1]; exact le_of_eq (by rw [dist_comm]; exact dist_W_C6 u hres),
    by rw [h2]; exact le_of_eq (by rw [dist_comm]; exact dist_W_hub0 u hR hW),
    by rw [h3]; exact le_of_eq (by rw [dist_comm]; exact dist_W_hub1 u hR hW)⟩

/-- 中心面 (C_2, H0, H1)，`O = refl (wPoint u)`。 -/
theorem faceOK_C2 (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u) (hres : residual u = 0) :
    FaceCoverable u ⟨2, by omega⟩ 9 10 := by
  have hR : 0 ≤ u 6 := (RootRangeBoxFull.ha_hapi_of_box u hu).1
  have hW : ((u 5 - u 4) / 2) ^ 2 ≤ (u 6) ^ 2 := hW_of_box u hu
  have h1 : centersOfRoot u ⟨2, by omega⟩ = ringCenter u 2 := centersOfRoot_ring u 2
  have h2 : centersOfRoot u 9 = hub0 u := centersOfRoot_nine u
  have h3 : centersOfRoot u 10 = hub1 u := centersOfRoot_ten u
  refine ⟨refl (wPoint u), ?_, ?_, ?_⟩
  · rw [h1]
    exact dist_refl_le (rc2_of_6 u).1 (rc2_of_6 u).2
      (by rw [dist_comm]; exact le_of_eq (dist_W_C6 u hres))
  · rw [h2]
    exact dist_refl_le (hub_mirror0 u).1 (hub_mirror0 u).2
      (by rw [dist_comm]; exact le_of_eq (dist_W_hub0 u hR hW))
  · rw [h3]
    exact dist_refl_le (hub_mirror1 u).1 (hub_mirror1 u).2
      (by rw [dist_comm]; exact le_of_eq (dist_W_hub1 u hR hW))

/-! ## §7 真实 raw TC **11 面表**（lead 给定）与表级 `FaceCoverable`

表（每行 = 一个面的三顶点，raw TC 索引）：
```
0:(0,1,10) 1:(1,2,10) 2:(2,3,9) 3:(3,4,9) 4:(4,5,9) 5:(5,6,9)
6:(6,7,10) 7:(7,8,10) 8:(8,0,10) 9:(2,9,10) 10:(6,9,10)
```
其中 1–6、8–10 共 **9 面**在本文件被实际证出（7 环面 + 2 中心面）；
**面 0** 由前提 `hF0 : FaceCoverable u ⟨0,_⟩ ⟨1,_⟩ 10` 供给（slack 的固定有理点 `O0`），
**面 7** 由面 0 的**任意见证镜像**得到（`faceOK_F7_of_F0`，`O ↦ refl O`）——不再依赖任何 slack 不等式。 -/

/-- 第 n 面的第一顶点（raw TC）。 -/
def faceI1 : Fin 11 → Fin 11 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 2, 6]
/-- 第 n 面的第二顶点（raw TC）。 -/
def faceI2 : Fin 11 → Fin 11 := ![1, 2, 3, 4, 5, 6, 7, 8, 0, 9, 9]
/-- 第 n 面的第三顶点（raw TC）。 -/
def faceI3 : Fin 11 → Fin 11 := ![10, 10, 9, 9, 9, 9, 10, 10, 10, 10, 10]

/-- **表级 `FaceCoverable`**：`InCertBox u` + `residual u = 0` + **面 0 的 `FaceCoverable`**
（slack 的固定有理点 `O0` 直接供给）⟹ 11 面全部 `FaceCoverable`。

面 7 由面 0 的**任意见证镜像**得到（`faceOK_F7_of_F0`，无需 `Uvec u 0`）；
其余 9 面（1–6、8、9、10）由 §2–§6 的实际定理供给。 -/
theorem faceOK_table (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u)
    (hres : residual u = 0)
    (hF0 : FaceCoverable u ⟨0, by omega⟩ ⟨1, by omega⟩ 10) :
    ∀ n : Fin 11, FaceCoverable u (faceI1 n) (faceI2 n) (faceI3 n) := by
  have H : RootRange u := RootRangeBoxFull.rootRange_of_box u hu
  intro n
  fin_cases n
  · exact hF0
  · exact faceOK_F1 u H hres
  · exact faceOK_F2 u H hres
  · exact faceOK_F3 u H hres
  · exact faceOK_F4 u H hres
  · exact faceOK_F5 u H hres
  · exact faceOK_F6 u H hres
  · exact faceOK_F7_of_F0 u hF0
  · exact faceOK_F8 u H hres
  · exact faceOK_C2 u hu hres
  · exact faceOK_C6 u hu hres

/-- **端到端（盒版；剩余前提 = `hF0`（面 0）与 `hcover`（tiling 的 11 面剖分））**：
`InCertBox u` + `residual u = 0` + 面 0 的 `FaceCoverable`（slack 的固定有理 `O0`）
+ **按 `faceI1/2/3` 同一索引顺序**的 11 面凸包表示
⟹ `Covers (centersOfRoot u) (u 6)`。

这把 flash-tiling 的 `hcover` 与 10 个实际面定理（9 面 + 面 7 的镜像）+ 面 0 的 slack 直接接起来。 -/
theorem covers_of_box_of_faces (u : Fin 12 → ℝ) (hu : RootRangeBoxFull.InCertBox u)
    (hres : residual u = 0)
    (hF0 : FaceCoverable u ⟨0, by omega⟩ ⟨1, by omega⟩ 10)
    (hcover : ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot u)) →
      ∃ n : Fin 11, ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
        p = la • centersOfRoot u (faceI1 n) + lb • centersOfRoot u (faceI2 n)
              + lc • centersOfRoot u (faceI3 n)) :
    Covers (centersOfRoot u) (u 6) :=
  covers_of_faceOK u (RootRangeBoxFull.rootRange_of_box u hu) 11 faceI1 faceI2 faceI3
    (faceOK_table u hu hres hF0) hcover

/-- **表值自检**（`decide`，内核级）：11 面的 raw TC 索引与 lead 给定表**逐位**一致。
这是接口自检（表错一位则后续 `hcover` 的索引对接全错），不是装饰。 -/example :
    (faceI1 0, faceI2 0, faceI3 0) = (0, 1, 10) ∧
    (faceI1 1, faceI2 1, faceI3 1) = (1, 2, 10) ∧
    (faceI1 2, faceI2 2, faceI3 2) = (2, 3, 9) ∧
    (faceI1 3, faceI2 3, faceI3 3) = (3, 4, 9) ∧
    (faceI1 4, faceI2 4, faceI3 4) = (4, 5, 9) ∧
    (faceI1 5, faceI2 5, faceI3 5) = (5, 6, 9) ∧
    (faceI1 6, faceI2 6, faceI3 6) = (6, 7, 10) ∧
    (faceI1 7, faceI2 7, faceI3 7) = (7, 8, 10) ∧
    (faceI1 8, faceI2 8, faceI3 8) = (8, 0, 10) ∧
    (faceI1 9, faceI2 9, faceI3 9) = (2, 9, 10) ∧
    (faceI1 10, faceI2 10, faceI3 10) = (6, 9, 10) := by decide

end N11Formalization.FlashBoundaryCapsFaces

#print axioms N11Formalization.FlashBoundaryCapsFaces.dist_ring_self_le
#print axioms N11Formalization.FlashBoundaryCapsFaces.dist_refl_le
#print axioms N11Formalization.FlashBoundaryCapsFaces.hO_F1
#print axioms N11Formalization.FlashBoundaryCapsFaces.hO_F2
#print axioms N11Formalization.FlashBoundaryCapsFaces.hO_F3
#print axioms N11Formalization.FlashBoundaryCapsFaces.hO_F8
#print axioms N11Formalization.FlashBoundaryCapsFaces.hO_F6
#print axioms N11Formalization.FlashBoundaryCapsFaces.hO_F5
#print axioms N11Formalization.FlashBoundaryCapsFaces.hO_F4
#print axioms N11Formalization.FlashBoundaryCapsFaces.hO_of_faceOK
#print axioms N11Formalization.FlashBoundaryCapsFaces.covers_of_faceOK
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_F1
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_F2
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_F3
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_F8
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_F6
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_F5
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_F4
#print axioms N11Formalization.FlashBoundaryCapsFaces.rc8
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_F7_of_F0
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_F0_H1
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_F7_H1
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_C6
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_C2
#print axioms N11Formalization.FlashBoundaryCapsFaces.faceOK_table
#print axioms N11Formalization.FlashBoundaryCapsFaces.covers_of_box_of_faces
