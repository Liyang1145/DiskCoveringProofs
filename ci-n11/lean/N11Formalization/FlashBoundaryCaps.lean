/-
n11-formalization —— **凸包-射线覆盖 consumer（原 root `u`，非 uCert/qR）**

写域：`lean/N11Formalization/FlashBoundaryCaps.lean` + `evidence/flash-caps/`。

## 0. 结构（取代此前作废的“逐个 cap 铺满”路线）

对**任意**中心族 `c` 与半径 `r`：

```
(∀ q, ‖q‖ = 1 → ∃ i, dist q (c i) ≤ r)          -- 边界层（本工程已证：circle_covered_of_range）
(∀ p ∈ convexHull ℝ (range c), ∃ i, dist p (c i) ≤ r)  -- 凸包层（hHull，由三角面覆盖承担）
⟹ Covers c r
```

证明（射线 + 单调性，不需要 cap 铺满、不需要把 `u 6` 换成舍入常数）：

* 若 `x ∈ hull` ⇒ 凸包层。
* 若 `‖x‖ = 1` ⇒ 边界层。
* 若 `‖x‖ < 1` 且 `x ∉ hull` ⇒ 由**严格分离**（`ResumeOutsideHull.exists_outward_nonneg`，
  lead 件）取 `v ≠ 0` 且 `∀i, 0 ≤ ⟪v, x − cᵢ⟫`；
  沿射线 `x + t•v` 每个中心距离**单调不减**（引理 A）；
  射线必与单位球面相交（引理 B，显式二次根，不用 IVT）；
  对交点 `q` 用边界层得某 `c_k`，再用引理 A 传回 `x`。

**口径**：`Point = EuclideanSpace ℝ (Fin 2)`；闭盘；长度以单位圆半径 1 为单位；`r = u 6` 原样传参。
本文件不含浮点、不含 `native_decide`、不含 `sorry`/自定义 axiom。

## 1. 已作废（留痕，见 evidence/flash-caps/EXP-8 与 team-message）

早前版本写了 `disk_of_inner_ge : ‖x‖ ≤ 1 → 1/4 ≤ ⟪x,c⟫ → ‖c‖ ≤ 9/10 → dist x c ≤ qR`，
**该命题为假**（反例 `x=(1,0), c=(1/4,0)`：`dist=3/4 > qR`），且“9 个环盘覆盖整个闭单位盘”也假
（原点距各环心 > 0.6）。已删除，不再使用任何 `qR` 替换。
-/

import Mathlib
import N11Formalization.Definitions
import N11Formalization.TCSystem
import N11Formalization.Assembly.G2Unified
import N11Formalization.ResumeOutsideHull
import N11Formalization.RootRangeBoxFull
import N11Formalization.ResumeAttainmentAnnulusFace

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section

namespace N11Formalization.FlashBoundaryCaps

open N11Formalization

/-! ## §1 引理 A：分离方向上的射线，到每个中心的距离单调不减 -/

/-- **距离沿严格分离方向单调不减**：若 `⟪v, x − c⟫ ≥ 0`，则对任意 `t ≥ 0`，`x + t•v` 到 `c`
的距离不小于 `x` 到 `c` 的距离。

（`‖(x+t v)−c‖² = ‖x−c‖² + 2t⟪v,x−c⟫ + t²‖v‖² ≥ ‖x−c‖²`。） -/
theorem dist_le_dist_add_smul {x c v : Point} {t : ℝ} (ht : 0 ≤ t)
    (hsep : 0 ≤ inner ℝ v (x - c)) : dist x c ≤ dist (x + t • v) c := by
  have h2 : (0 : ℝ) ≤ 2 * t * inner ℝ v (x - c) := by
    have h2t : (0 : ℝ) ≤ 2 * t := by linarith
    exact mul_nonneg h2t hsep
  have hkey : dist (x + t • v) c ^ 2
      = dist x c ^ 2 + (2 * t * inner ℝ v (x - c) + t ^ 2 * ‖v‖ ^ 2) := by
    rw [dist_eq_norm, dist_eq_norm]
    have e : (x + t • v) - c = (x - c) + (t • v) := by abel
    rw [e, norm_add_sq_real, real_inner_smul_right, real_inner_comm v (x - c)]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hle : dist x c ^ 2 ≤ dist (x + t • v) c ^ 2 := by
    rw [hkey]
    nlinarith [h2, sq_nonneg t, sq_nonneg (‖v‖ : ℝ)]
  have h := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (show (0 : ℝ) ≤ dist x c from dist_nonneg),
    Real.sqrt_sq (show (0 : ℝ) ≤ dist (x + t • v) c from dist_nonneg)] at h

/-! ## §2 引理 B：从内点沿非零方向必与单位球面相交（显式二次根） -/

/-- **射线与单位球面相交**：`v ≠ 0`、`‖x‖ < 1` ⟹ 存在 `t ≥ 0` 使 `‖x + t•v‖ = 1`。

显式解：`C = ‖v‖² > 0`、`B = ⟪x,v⟫`、`s = √(B² + C(1−‖x‖²))`、`t = (s−B)/C`；
由 `Ct² + 2Bt + (‖x‖²−1) = 0` 得 `‖x + t•v‖² = 1`。 -/
theorem exists_norm_eq_one_of_lt {x v : Point} (hv : v ≠ 0) (hx : ‖x‖ < 1) :
    ∃ t : ℝ, 0 ≤ t ∧ ‖x + t • v‖ = 1 := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hC : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  have hA : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x, hx]
  have hA0 : (0 : ℝ) ≤ 1 - ‖x‖ ^ 2 := by linarith
  set B := inner ℝ x v with hB
  set s := Real.sqrt (B ^ 2 + ‖v‖ ^ 2 * (1 - ‖x‖ ^ 2)) with hs
  have hrad : 0 ≤ B ^ 2 + ‖v‖ ^ 2 * (1 - ‖x‖ ^ 2) :=
    add_nonneg (sq_nonneg B) (mul_nonneg hC.le hA0)
  have hs2 : s ^ 2 = B ^ 2 + ‖v‖ ^ 2 * (1 - ‖x‖ ^ 2) := Real.sq_sqrt hrad
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hBs : B ≤ s := by
    have h1 : B ^ 2 ≤ s ^ 2 := by rw [hs2]; nlinarith [mul_nonneg hC.le hA0]
    have h2 : |B| ≤ |s| := sq_le_sq.mp h1
    rw [abs_of_nonneg hs0] at h2
    exact (abs_le.mp h2).2
  refine ⟨(s - B) / ‖v‖ ^ 2, by positivity, ?_⟩
  have hkey : ‖x + ((s - B) / ‖v‖ ^ 2) • v‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, real_inner_smul_right, ← hB]
    have hnv : ‖((s - B) / ‖v‖ ^ 2) • v‖ ^ 2 = ((s - B) / ‖v‖ ^ 2) ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hnv]
    field_simp
    nlinarith [hs2]
  have hnn : (0 : ℝ) ≤ ‖x + ((s - B) / ‖v‖ ^ 2) • v‖ := norm_nonneg _
  calc ‖x + ((s - B) / ‖v‖ ^ 2) • v‖
      = Real.sqrt (‖x + ((s - B) / ‖v‖ ^ 2) • v‖ ^ 2) := (Real.sqrt_sq hnn).symm
    _ = Real.sqrt 1 := by rw [hkey]
    _ = 1 := Real.sqrt_one

/-! ## §3 最终 consumer（原 root `u`；只留 `hHull`） -/

/-- **凸包 + 边界层 ⟹ 全覆盖**（任意 `Fin 11` 中心族）。

本定理的 `centersOfRoot u` 特化即 `§4`。 -/
theorem covers_of_sphere_and_hull (c : Fin 11 → Point) (r : ℝ)
    (hSphere : ∀ q : Point, ‖q‖ = 1 → ∃ i : Fin 11, dist q (c i) ≤ r)
    (hHull : ∀ p : Point, p ∈ convexHull ℝ (Set.range c) → ∃ i : Fin 11, dist p (c i) ≤ r) :
    Covers c r := by
  intro x hx
  rw [mem_unitDisk] at hx
  by_cases hmem : x ∈ convexHull ℝ (Set.range c)
  · exact hHull x hmem
  · by_cases h1 : ‖x‖ = 1
    · exact hSphere x h1
    · have hlt : ‖x‖ < 1 := lt_of_le_of_ne hx h1
      obtain ⟨v, hv, hsep⟩ :=
        ResumeOutsideHull.exists_outward_nonneg c x hmem
      obtain ⟨t, ht, ht1⟩ := exists_norm_eq_one_of_lt hv hlt
      obtain ⟨i, hi⟩ := hSphere (x + t • v) ht1
      exact ⟨i, le_trans (dist_le_dist_add_smul ht (hsep i)) hi⟩

/-- **原 root 的 consumer**：`RootRange u` + 凸包层 `hHull` ⟹ `Covers (centersOfRoot u) (u 6)`。

边界层由已证的 `circle_covered_of_range`（一般 `u`，无残余条件）供给，
经 `centersOfRoot_ring` 转成 `Fin 11` 索引。**不含** `qR`/`uCert` 替换。 -/
theorem covers_of_hull (u : Fin 12 → ℝ) (H : RootRange u)
    (hHull : ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot u)) →
      ∃ i : Fin 11, dist p (centersOfRoot u i) ≤ u 6) :
    Covers (centersOfRoot u) (u 6) := by
  refine covers_of_sphere_and_hull (centersOfRoot u) (u 6) ?_ hHull
  intro q hq
  obtain ⟨k, hk⟩ := circle_covered_of_range u H q hq
  exact ⟨⟨(k : ℕ), by omega⟩, by rwa [centersOfRoot_ring]⟩

/-- **盒版 consumer（只留 `hHull`）**：`InCertBox u` + 凸包层 ⟹ `Covers (centersOfRoot u) (u 6)`。

`RootRange` 由已证的 `RootRangeBoxFull.rootRange_of_box`（证书盒的有向区间读数）供给，
`u` 是**原 root**（`u 6` 原样作半径）。 -/
theorem covers_of_hull_of_box (u : Fin 12 → ℝ)
    (hu : RootRangeBoxFull.InCertBox u)
    (hHull : ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot u)) →
      ∃ i : Fin 11, dist p (centersOfRoot u i) ≤ u 6) :
    Covers (centersOfRoot u) (u 6) :=
  covers_of_hull u (RootRangeBoxFull.rootRange_of_box u hu) hHull

/-- **凸包层的有限三角化 consumer**：给定有限个三角形
`(c_{i₁ n}, c_{i₂ n}, c_{i₃ n})`，每个都有一个公共点 `O n` 到三顶点的距离 ≤ `u 6`，
并且凸包的每个点都是某个三角形的凸组合 —— 则凸包层 `hHull` 成立。

证明：逐个三角形用已证的 `tri_cover_pt_le`（松弛三角覆盖，允许紧等号）。

⇒ **`hHull` 的付清方式被钉成有限数据**：`(N, i₁, i₂, i₃, O)` 五样 + 每条 `dist (c_{i n}) (O n) ≤ u 6`
（活跃面由 `residual`/`RootRange` 精确供给，见 `active_U_faces_cover` 一族）。 -/
theorem hull_covered_of_triangles (u : Fin 12 → ℝ) (hR : 0 ≤ u 6) (N : ℕ)
    (i1 i2 i3 : Fin N → Fin 11) (O : Fin N → Point)
    (hO : ∀ n : Fin N, dist (centersOfRoot u (i1 n)) (O n) ≤ u 6 ∧
      dist (centersOfRoot u (i2 n)) (O n) ≤ u 6 ∧
      dist (centersOfRoot u (i3 n)) (O n) ≤ u 6)
    (hcover : ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot u)) →
      ∃ n : Fin N, ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
        p = la • centersOfRoot u (i1 n) + lb • centersOfRoot u (i2 n)
              + lc • centersOfRoot u (i3 n)) :
    ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot u)) →
      ∃ i : Fin 11, dist p (centersOfRoot u i) ≤ u 6 := by
  intro p hp
  obtain ⟨n, la, lb, lc, hla, hlb, hlc, hs, hrep⟩ := hcover p hp
  obtain ⟨h1, h2, h3⟩ := hO n
  rcases ResumeAttainment.tri_cover_pt_le (centersOfRoot u (i1 n)) (centersOfRoot u (i2 n))
    (centersOfRoot u (i3 n)) (O n) p (u 6) la lb lc hR hla hlb hlc hs h1 h2 h3 hrep with h | h | h
  · exact ⟨i1 n, h⟩
  · exact ⟨i2 n, h⟩
  · exact ⟨i3 n, h⟩

/-- **端到端（三角化版）**：`RootRange u` + 有限三角化数据 ⟹ `Covers (centersOfRoot u) (u 6)`。

这是把 `hHull` 完全替换为**有限数据**后的最终 consumer；`u` 仍是**原 root**。 -/
theorem covers_of_triangulation (u : Fin 12 → ℝ) (H : RootRange u) (N : ℕ)
    (i1 i2 i3 : Fin N → Fin 11) (O : Fin N → Point)
    (hO : ∀ n : Fin N, dist (centersOfRoot u (i1 n)) (O n) ≤ u 6 ∧
      dist (centersOfRoot u (i2 n)) (O n) ≤ u 6 ∧
      dist (centersOfRoot u (i3 n)) (O n) ≤ u 6)
    (hcover : ∀ p : Point, p ∈ convexHull ℝ (Set.range (centersOfRoot u)) →
      ∃ n : Fin N, ∃ la lb lc : ℝ, 0 ≤ la ∧ 0 ≤ lb ∧ 0 ≤ lc ∧ la + lb + lc = 1 ∧
        p = la • centersOfRoot u (i1 n) + lb • centersOfRoot u (i2 n)
              + lc • centersOfRoot u (i3 n)) :
    Covers (centersOfRoot u) (u 6) :=
  covers_of_hull u H (hull_covered_of_triangles u H.hR N i1 i2 i3 O hO hcover)

/-! ## §5 判别力对照：`hHull` **不可去**（消费已证件，非新数值）

只保留 9 个环盘（后两槽重复 `C_0`，不改变并集）时：**单位球面层为真**（已证 `circle_covered`），
但 **`Covers` 为假**（已证 `ringOnly_not_covers_origin_at_qR`：`dist 0 (C_k) = ρ_k ≥ 1/2 > qR`）。
⇒ 任何只消费「球面层」的判据都不可能推出覆盖；凸包层（或等价物）**必须**。
这是本 consumer 的**前提必要性对照**（比“改错报红的 mutant”更强：这里是**结论被证明为假**而另一前提为真）。 -/

/-- 仅环盘的 `Fin 11` 版本（后两槽重复 `C_0`）。 -/
def ringOnly (i : Fin 11) : Point :=
  if h : (i : ℕ) < 9 then ringCenter uCert ⟨(i : ℕ), h⟩ else ringCenter uCert 0

theorem ringOnly_nine (k : Fin 9) : ringOnly ⟨(k : ℕ), by omega⟩ = ringCenter uCert k := by
  simp only [ringOnly]
  rw [dif_pos (show ((⟨(k : ℕ), by omega⟩ : Fin 11) : ℕ) < 9 from k.isLt)]

/-- 球面层：`ringOnly` 仍然覆盖单位球面（直接消费 `circle_covered`）。 -/
theorem ringOnly_sphere : ∀ q : Point, ‖q‖ = 1 → ∃ i : Fin 11, dist q (ringOnly i) ≤ (qR : ℝ) := by
  intro q hq
  obtain ⟨k, hk⟩ := circle_covered q hq
  exact ⟨⟨(k : ℕ), by omega⟩, by rw [ringOnly_nine]; exact hk⟩

/-- **球面层不足以推出覆盖**（`hHull` 必要性对照，kernel-proved）。 -/
theorem ringOnly_not_covers : ¬ Covers ringOnly (qR : ℝ) := by
  intro h
  obtain ⟨i, hi⟩ := h 0 zero_mem_unitDisk
  by_cases h9 : (i : ℕ) < 9
  · have hci : ringOnly i = ringCenter uCert ⟨(i : ℕ), h9⟩ := by
      simp only [ringOnly]; rw [dif_pos h9]
    rw [hci] at hi
    exact ringOnly_not_covers_origin_at_qR ⟨⟨(i : ℕ), h9⟩, hi⟩
  · have hci : ringOnly i = ringCenter uCert 0 := by
      simp only [ringOnly]; rw [dif_neg h9]
    rw [hci] at hi
    exact ringOnly_not_covers_origin_at_qR ⟨0, hi⟩

/-- **前提必要性（判别力）**：球面层前提为真、结论为假 ⇒ `hHull` 不可去。 -/
theorem sphere_layer_not_sufficient :
    (∀ q : Point, ‖q‖ = 1 → ∃ i : Fin 11, dist q (ringOnly i) ≤ (qR : ℝ)) ∧
      ¬ Covers ringOnly (qR : ℝ) :=
  ⟨ringOnly_sphere, ringOnly_not_covers⟩

/-! ## §6 仪器校准：consumer 在“已知答案”实例上的读数

`covers_of_sphere_and_hull` 的**校准件**：取 11 个中心全为原点、半径 1。
两个前提都可核（球面层：`dist q 0 = ‖q‖ = 1 ≤ 1`；凸包层：凸包 = {0}，`dist 0 0 = 0 ≤ 1`），
结论 `Covers (fun _ => 0) 1` 也**可独立两行证出** ⇒ consumer 在已知答案上给出正确答案
（不是只“不报错”）。配套负半边：半径 0 时同一族**不**覆盖（`x ≠ 0` 处 `dist = ‖x‖ > 0`），
说明前提并非对任意半径都可满足。 -/

/-- 校准（正半边）：已知答案是「11 个原点盘、半径 1 覆盖 `D`」，consumer 复现它。 -/
theorem calibration_zero_center_covers :
    Covers (fun _ : Fin 11 => (0 : Point)) 1 :=
  covers_of_sphere_and_hull (fun _ : Fin 11 => (0 : Point)) 1
    (fun q hq => ⟨0, by rw [dist_zero_right]; exact le_of_eq hq⟩)
    (fun p hp => ⟨0, by
      have hr : Set.range (fun _ : Fin 11 => (0 : Point)) = ({0} : Set Point) := Set.range_const
      have hcs : convexHull ℝ ({0} : Set Point) = ({0} : Set Point) := convexHull_singleton (0 : Point)
      rw [hr, hcs] at hp
      have h0 : p = 0 := Set.mem_singleton_iff.mp hp
      rw [h0, dist_zero_right]
      simp⟩)

/-- 校准（负半边）：同族在半径 0 处**不**覆盖（`x = (1,0)` 处 `dist = 1 > 0`）。 -/
theorem calibration_zero_center_not_covers :
    ¬ Covers (fun _ : Fin 11 => (0 : Point)) 0 := by
  intro h
  obtain ⟨i, hi⟩ := h (!₂[(1 : ℝ), 0] : Point)
    (by rw [mem_unitDisk, cons_norm_eq_abs]; norm_num)
  rw [dist_zero_right, cons_norm_eq_abs, abs_one] at hi
  norm_num at hi

end N11Formalization.FlashBoundaryCaps

#print axioms N11Formalization.FlashBoundaryCaps.dist_le_dist_add_smul
#print axioms N11Formalization.FlashBoundaryCaps.exists_norm_eq_one_of_lt
#print axioms N11Formalization.FlashBoundaryCaps.covers_of_sphere_and_hull
#print axioms N11Formalization.FlashBoundaryCaps.covers_of_hull
#print axioms N11Formalization.FlashBoundaryCaps.covers_of_hull_of_box
#print axioms N11Formalization.FlashBoundaryCaps.hull_covered_of_triangles
#print axioms N11Formalization.FlashBoundaryCaps.covers_of_triangulation
#print axioms N11Formalization.FlashBoundaryCaps.sphere_layer_not_sufficient
#print axioms N11Formalization.FlashBoundaryCaps.calibration_zero_center_covers
#print axioms N11Formalization.FlashBoundaryCaps.calibration_zero_center_not_covers
