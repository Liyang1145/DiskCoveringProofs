import N11Formalization.F1.BallD35C11
import N11Formalization.HessSeamMain

/-!
# Lead scratch：**一般点 KKT×z 的 `fderiv` 公式**（49 格链式法则那一环 ✓）

**目的**：`Jt'` 的 **KKT×z 块**（49 格 ✓）需要**一般点 `x`** 的
```
(fderiv ℝ TCSystem x (Pi.single (up7 j) 1)) (kkt12 i) = -(∑ mm, (last5 x mm) * hessEntryAt (first7 x) i j mm)
```
⇒ 中心版 `fderiv_TCSystem_kkt_z`（`ResidualDerivJT` **L520** ✓）是 `cCertR` 专用 ✗ ⇒ 本件**逐字升格** ✓。

**两件**：
1. `fderiv_adjointBlock_up7_any` ← 升格中心版 `fderiv_adjointBlock_up7`（**L460** ✓）
2. `fderiv_TCSystem_kkt_z_any` ← 升格中心版 `fderiv_TCSystem_kkt_z`（**L520** ✓）

**料（全在锥 ✓）**：`fderiv_adjointBlock_val_any`（`F1/BallD35C11` **L60** ✓）｜`hasFDerivAt_gFun_any`（C11 ✓）｜
`differentiableAt_adjointBlockRow_any`（C11 **L138** ✓）｜`TCSystem_row_eq_adjointBlock`（`ResidualDerivJT` **L481** ✓，**已是一般 `u`** ✓）｜
`proj7CLM_single_up7`／`up7_ne_up5`（一般 ✓）｜`hessEntryAt`（`HessSeamMain` **L224** ✓；`hessEntry_eq_hessEntryAt` **L227** ✓ 说明中心即一般版在 `u0`）

⚠ `hadj` 暂作**参数** ✓（DEAD §59 簿记切分 ✓；`hess-seam` 的 `Smoothness` 批已绿 ⇒ 待其真名到手即消 ✓）。
判据：**exit=0 且输出 0 行**。
-/

namespace N11Formalization.Lead.KktZ

open N11Formalization
open N11Formalization.HessSeam

/-- **一般点**：`adjointBlock` 行的 `z` 列导数 = `Σ mm (last5 x mm) · hessEntryAt (first7 x) i j mm` ✓。 -/
theorem fderiv_adjointBlock_up7_any (x : Fin 12 → ℝ)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) (first7 x))
    (i j : Fin 7) :
    (fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) x)
      (Pi.single (up7 j) (1 : ℝ))
      = ∑ mm : Fin 5, (last5 x mm) * hessEntryAt (first7 x) i j mm := by
  rw [fderiv_adjointBlock_val_any x hadj i]
  have h0 : ∀ mm : Fin 5,
      (fderiv ℝ (gFun i mm) (first7 x)) (proj7CLM (Pi.single (up7 j) (1 : ℝ)))
        = hessEntryAt (first7 x) i j mm := by
    intro mm
    rw [proj7CLM_single_up7, (hasFDerivAt_gFun_any (first7 x) hadj i mm).fderiv]
    simp only [ContinuousLinearMap.comp_apply, evCLM_apply, hessEntryAt]
  have h1 : ∀ mm : Fin 5, (Pi.single (up7 j) (1 : ℝ) : Fin 12 → ℝ) (up5 mm) = 0 := by
    intro mm
    rw [Pi.single_eq_of_ne (i := up7 j) (i' := up5 mm) (up7_ne_up5 j mm).symm]
  simp only [h0, h1, mul_zero, add_zero]

/-- **一般点 KKT×z 公式**：`TCSystem` 的 KKT 行对 `z` 的 `fderiv` 取值 ✓。 -/
theorem fderiv_TCSystem_kkt_z_any (x : Fin 12 → ℝ)
    (hdT : DifferentiableAt ℝ TCSystem x)
    (hadj : DifferentiableAt ℝ (fun z : Fin 7 → ℝ => fderiv ℝ residualFun z) (first7 x))
    (i j : Fin 7) :
    (fderiv ℝ TCSystem x (Pi.single (up7 j) (1 : ℝ))) (kkt12 i)
      = -(∑ mm : Fin 5, (last5 x mm) * hessEntryAt (first7 x) i j mm) := by
  rw [fderiv_apply_val hdT (kkt12 i) (Pi.single (up7 j) (1 : ℝ)),
    TCSystem_row_eq_adjointBlock i]
  have hA : HasFDerivAt (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i)
      (fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) x) x :=
    (differentiableAt_adjointBlockRow_any x hadj i).hasFDerivAt
  have hc : HasFDerivAt
      (fun _ : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0))
      (0 : (Fin 12 → ℝ) →L[ℝ] ℝ) x :=
    hasFDerivAt_const _ _
  have hsub : fderiv ℝ (fun u : Fin 12 → ℝ =>
        (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0)
          - adjointBlock (first7 u) (last5 u) i) x
      = 0 - fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) x := by
    rw [show (fun u : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0)
          - adjointBlock (first7 u) (last5 u) i)
        = (fun _ : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0))
          - (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) from rfl]
    exact (hc.sub hA).fderiv
  rw [hsub, sub_apply]
  simp only [zero_apply, zero_sub]
  rw [fderiv_adjointBlock_up7_any x hadj i j]

end N11Formalization.Lead.KktZ
