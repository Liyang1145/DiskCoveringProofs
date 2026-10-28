/-
n11-formalization —— **两中心面的 diagonal flip 实例**（tiling 的 central consumer 直接可用）。

写域：本文件（`evidence/flash-caps/`，不进 srcDir）+ 同目录证据。
**依赖**：`N11Formalization.FlashBoundaryCapsFlip.diagonal_flip`（已冻结/已入根，SHA256 `BD56A4A8…7AD5`），
本文件不修改它，只**消费**它。

## 0. 结论（tiling 的 intake 形状）

设 `u` 在证书盒内（`RootRangeBoxFull.InCertBox u`）。取

* `A := ringCenter u 2`、`B := ringCenter u 6`、`k0 := hub0 u`、`k1 := hub1 u`；
* `q := qinst u`（= `C_2` 与 `C_6` 的**坐标中点**）——由 `rc2_of_6`（`C_6 = refl C_2`）知
  `q = ((C_2).ofLp 0, 0)`，而**中点自动属闭线段 `[A,B]`**（退化也成立，不需 `sin` 符号/非退化/面积正）；

则
```
conv(hub0,C_2,C_6) ∪ conv(hub1,C_2,C_6) ⊆ conv(C_2,hub0,hub1) ∪ conv(C_6,hub0,hub1)
```

**唯一数值负担** = `u 5 ≤ (C_2).ofLp 0 ≤ u 4`（x 夹在两 hub 之间；实际 ≈ 0.0948 ∈ [−0.1494, 0.2729]），
用已证包络 `ndRingBox_mem` + `nd_eval` 的粗有理界给出（**不需要** `sin`/θ 的符号）。

## 1. 口径

* `Point = EuclideanSpace ℝ (Fin 2)`；`segment`/`convexHull` 取 `ℝ` 上结构；闭环段。
* 中心索引 raw TC（环 0..8、hub0 = 9、hub1 = 10）；半径/坐标一律用**原 root**。
* 无浮点、无 `sorry`、无自定义 axiom。
-/

import Mathlib
import N11Formalization.Definitions
import N11Formalization.TCSystem
import N11Formalization.RootRangeBoxFull
import N11Formalization.Assembly.G2Unified
import N11Formalization.ResumeAttainmentCentral2
import N11Formalization.FlashBoundaryCapsFlip

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section

namespace N11Formalization.FlashBoundaryCapsMidpoint

open N11Formalization
open N11Formalization.RootRangeBoxFull (InCertBox hQ)

/-! ## §1 两点搬运用引理 -/

/-- **坐标中点（参数 1/2）在闭线段上**（退化也成立，不需要内点假设）。 -/
theorem coordMid_mem_segment (A B : Point) :
    (!₂[(A.ofLp 0 + B.ofLp 0) / 2, (A.ofLp 1 + B.ofLp 1) / 2] : Point) ∈ segment ℝ A B := by
  rw [segment_eq_image ℝ A B]
  refine ⟨1 / 2, by norm_num, ?_⟩
  ext i
  fin_cases i <;> simp <;> ring

/-- **x 轴点夹在两 hub 之间**：`u 5 ≤ t ≤ u 4 ⇒ (t,0) ∈ [hub0 u, hub1 u]`。 -/
theorem mem_segment_hubs {u : Fin 12 → ℝ} {t : ℝ} (h45 : u 5 < u 4)
    (h1 : u 5 ≤ t) (h2 : t ≤ u 4) :
    (!₂[t, (0 : ℝ)] : Point) ∈ segment ℝ (hub0 u) (hub1 u) := by
  have hden : (0 : ℝ) < u 4 - u 5 := by linarith
  rw [segment_eq_image ℝ (hub0 u) (hub1 u)]
  refine ⟨(u 4 - t) / (u 4 - u 5), ⟨div_nonneg (by linarith) hden.le,
    (div_le_one hden).mpr (by linarith)⟩, ?_⟩
  ext i
  fin_cases i <;> simp [hub0, hub1]; field_simp; ring

/-! ## §2 唯一数值负担：`C_2` 的 x 坐标夹逼 -/

/-- `(ringCenter u 2).ofLp 0` 的粗有理夹逼（`ndRingBox_mem` + `nd_eval`；实际值 ≈ 0.0948）。 -/
theorem ringCenter_two_x_bounds (u : Fin 12 → ℝ) (hu : InCertBox u) :
    (1 : ℝ) / 100 ≤ (ringCenter u 2).ofLp 0 ∧
      (ringCenter u 2).ofLp 0 ≤ (20 : ℝ) / 100 := by
  have hQ : ∀ i, (ndBox i).Mem (u i) := RootRangeBoxFull.hQ u hu
  have hmem := ndRingBox_mem hQ (2 : Fin 9) (0 : Fin 2)
  constructor
  · have hlo : (((1 : ℚ) / 100)) ≤ (ndRingBox ndBox 2 0).lo := by nd_eval
    have hloR : ((1 : ℝ) / 100) ≤ (((ndRingBox ndBox 2 0).lo : ℚ) : ℝ) := by
      rw [show ((1 : ℝ) / 100) = ((((1 : ℚ) / 100) : ℚ) : ℝ) by norm_num, Rat.cast_le]
      exact hlo
    have hb : (((ndRingBox ndBox 2 0).lo : ℚ) : ℝ) ≤ (ringCenter u 2).ofLp 0 :=
      RatInterval.mem_lo_le hmem
    exact le_trans hloR hb
  · have hhi : (ndRingBox ndBox 2 0).hi ≤ ((20 : ℚ) / 100) := by nd_eval
    have hhiR : (((ndRingBox ndBox 2 0).hi : ℚ) : ℝ) ≤ ((20 : ℝ) / 100) := by
      rw [show ((20 : ℝ) / 100) = ((((20 : ℚ) / 100) : ℚ) : ℝ) by norm_num, Rat.cast_le]
      exact hhi
    have hb : (ringCenter u 2).ofLp 0 ≤ (((ndRingBox ndBox 2 0).hi : ℚ) : ℝ) :=
      RatInterval.mem_le_hi hmem
    exact le_trans hb hhiR

/-- `u 5 < u 4`（`u 5 ≤ −0.1494… < 0.2729… ≤ u 4`）。 -/
theorem hubs_x_lt (u : Fin 12 → ℝ) (hu : InCertBox u) : u 5 < u 4 := by
  have h4 : (1320038024120705549412715 : ℝ) / 2 ^ 82 ≤ u 4 := by
    have h := (hu 4).1
    rw [show boxLoCert 4 = (1320038024120705549412715 : ℚ) / 2 ^ 82 from rfl] at h
    push_cast at h; exact h
  have h5 : u 5 ≤ (-722591877320515100682603 : ℝ) / 2 ^ 82 := by
    have h := (hu 5).2
    rw [show boxHiCert 5 = (-722591877320515100682603 : ℚ) / 2 ^ 82 from rfl] at h
    push_cast at h; exact h
  have c5 : ((-722591877320515100682603 : ℝ) / 2 ^ 82)
      < (1320038024120705549412715 : ℝ) / 2 ^ 82 := by norm_num
  linarith

/-! ## §3 公共点 `q` 与两条线段成员 -/

/-- 实例用的公共点 `q := C_2 与 C_6 的坐标中点`。 -/
def qinst (u : Fin 12 → ℝ) : Point :=
  !₂[((ringCenter u 2).ofLp 0 + (ringCenter u 6).ofLp 0) / 2,
      ((ringCenter u 2).ofLp 1 + (ringCenter u 6).ofLp 1) / 2]

/-- `q ∈ [C_2, C_6]`（中点定理的直接实例；**退化也成立**）。 -/
theorem qinst_mem_AB (u : Fin 12 → ℝ) :
    qinst u ∈ segment ℝ (ringCenter u 2) (ringCenter u 6) :=
  coordMid_mem_segment _ _

/-- `q = ((C_2).ofLp 0, 0)`（由 `rc2_of_6`：`C_6 = refl C_2`）。 -/
theorem qinst_eq (u : Fin 12 → ℝ) :
    qinst u = (!₂[(ringCenter u 2).ofLp 0, (0 : ℝ)] : Point) := by
  obtain ⟨hx, hy⟩ := ResumeAttainment.rc2_of_6 u
  ext i
  fin_cases i <;> simp [qinst, hx, hy]

/-- `q ∈ [hub0, hub1]`：x 夹逼（`ndRingBox` 粗界 + 两 hub 的 x 界）。 -/
theorem qinst_mem_hubs (u : Fin 12 → ℝ) (hu : InCertBox u) :
    qinst u ∈ segment ℝ (hub0 u) (hub1 u) := by
  obtain ⟨hx1, hx2⟩ := ringCenter_two_x_bounds u hu
  have c5 : ((-722591877320515100682603 : ℝ) / 2 ^ 82) ≤ ((1 : ℝ) / 100) := by norm_num
  have c4 : (20 : ℝ) / 100 ≤ (1320038024120705549412715 : ℝ) / 2 ^ 82 := by norm_num
  have h5le : u 5 ≤ (ringCenter u 2).ofLp 0 := by
    have h := (hu 5).2
    rw [show boxHiCert 5 = (-722591877320515100682603 : ℚ) / 2 ^ 82 from rfl] at h
    push_cast at h
    linarith
  have hle4 : (ringCenter u 2).ofLp 0 ≤ u 4 := by
    have h := (hu 4).1
    rw [show boxLoCert 4 = (1320038024120705549412715 : ℚ) / 2 ^ 82 from rfl] at h
    push_cast at h
    linarith
  rw [qinst_eq u]
  exact mem_segment_hubs (hubs_x_lt u hu) h5le hle4

/-! ## §4 实例：两中心面的 diagonal flip -/

/-- **两中心面的 diagonal flip（tiling 直接可用）**：
`conv(hub0,C_2,C_6) ∪ conv(hub1,C_2,C_6) ⊆ conv(C_2,hub0,hub1) ∪ conv(C_6,hub0,hub1)`。

由冻结件的 `FlashBoundaryCapsFlip.diagonal_flip`（generic 形式）在
`A := C_2, B := C_6, k0 := hub0, k1 := hub1, q := qinst u` 上实例化。 -/
theorem central_flip_instance (u : Fin 12 → ℝ) (hu : InCertBox u) :
    convexHull ℝ ({hub0 u, ringCenter u 2, ringCenter u 6} : Set Point) ∪
        convexHull ℝ ({hub1 u, ringCenter u 2, ringCenter u 6} : Set Point) ⊆
      convexHull ℝ ({ringCenter u 2, hub0 u, hub1 u} : Set Point) ∪
        convexHull ℝ ({ringCenter u 6, hub0 u, hub1 u} : Set Point) :=
  FlashBoundaryCapsFlip.diagonal_flip (A := ringCenter u 2) (B := ringCenter u 6)
    (k0 := hub0 u) (k1 := hub1 u) (qinst_mem_AB u) (qinst_mem_hubs u hu)

end N11Formalization.FlashBoundaryCapsMidpoint

#print axioms N11Formalization.FlashBoundaryCapsMidpoint.coordMid_mem_segment
#print axioms N11Formalization.FlashBoundaryCapsMidpoint.mem_segment_hubs
#print axioms N11Formalization.FlashBoundaryCapsMidpoint.ringCenter_two_x_bounds
#print axioms N11Formalization.FlashBoundaryCapsMidpoint.hubs_x_lt
#print axioms N11Formalization.FlashBoundaryCapsMidpoint.qinst_mem_AB
#print axioms N11Formalization.FlashBoundaryCapsMidpoint.qinst_eq
#print axioms N11Formalization.FlashBoundaryCapsMidpoint.qinst_mem_hubs
#print axioms N11Formalization.FlashBoundaryCapsMidpoint.central_flip_instance
