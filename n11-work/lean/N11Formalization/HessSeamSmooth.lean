import N11Formalization.HessSeamHL7
import N11Formalization.Transport

/-!
# hess-seam / 消掉 `hadj`：一般点的 `fderiv residualFun` 可微性（由光滑性 ＋ 非退化条件 ✓）

Lead ④ 的目标：`∀ x ∈ closedBall certCR ρ, DifferentiableAt ℝ (fun y => fderiv ℝ residualFun y) (first7 x)` ✓。
根内**已有**现成桥 ✓：`contDiffAt_residualFun`（分量级，z 空间 ✓）＋
**`contDiffAt_fderiv_residualFun {m} : ContDiffAt ℝ (m+1) (fun w => residualFun w) z → ContDiffAt ℝ m (fun w => fderiv ℝ residualFun w) z`** ✓
＋ `ContDiffAt.differentiableAt` ✓ ⇒ **`hadj` 可由光滑性 ＋ 7 条非退化条件推出** ✓✓（不必作装配参数 ✗）。
作用域：**任意 `z : Fin 7 → ℝ`**（非退化条件在该点成立即可 ⇒ 球上只需 `hnd*` 批 ✓）。
口径：无 `sorry`/公理/`native_decide`。
-/

noncomputable section

namespace N11Formalization

namespace HessSeam

open RatInterval

/-- 向量值光滑性：`residualFun : (Fin 7 → ℝ) → (Fin 5 → ℝ)` 在 `z` 处 `ContDiffAt ⊤`（5 分量 ＋ 7 条非退化条件 ✓）。 -/
theorem contDiffAt_residualFun_vec (z : Fin 7 → ℝ)
    (h1 : ∀ j : Fin 9, pad12 z 6 ^ 2 - Real.sin (angleVec (pad12 z) j) ^ 2 ≠ 0)
    (h2 : pad12 z 6 ^ 2 - ((pad12 z 5 - pad12 z 4) / 2) ^ 2 ≠ 0)
    (h3 : Uvec (pad12 z) 1 ≠ hub1 (pad12 z)) (h4 : Uvec (pad12 z) 2 ≠ hub0 (pad12 z))
    (h5 : Uvec (pad12 z) 3 ≠ hub0 (pad12 z)) (h6 : Uvec (pad12 z) 8 ≠ hub1 (pad12 z))
    (h7 : wPoint (pad12 z) ≠ ringCenter (pad12 z) 6) :
    ContDiffAt ℝ ⊤ (fun w : Fin 7 → ℝ => residualFun w) z :=
  (contDiffAt_pi).mpr (fun i =>
    contDiffAt_residualFun (n := ⊤) z h1 h2 h3 h4 h5 h6 h7 i)

/-- **`hadj` 的消解**：`DifferentiableAt (fderiv residualFun)`（任意点 `z`，非退化条件成立即可 ✓）。 -/
theorem differentiableAt_fderiv_residualFun_of_nondeg (z : Fin 7 → ℝ)
    (h1 : ∀ j : Fin 9, pad12 z 6 ^ 2 - Real.sin (angleVec (pad12 z) j) ^ 2 ≠ 0)
    (h2 : pad12 z 6 ^ 2 - ((pad12 z 5 - pad12 z 4) / 2) ^ 2 ≠ 0)
    (h3 : Uvec (pad12 z) 1 ≠ hub1 (pad12 z)) (h4 : Uvec (pad12 z) 2 ≠ hub0 (pad12 z))
    (h5 : Uvec (pad12 z) 3 ≠ hub0 (pad12 z)) (h6 : Uvec (pad12 z) 8 ≠ hub1 (pad12 z))
    (h7 : wPoint (pad12 z) ≠ ringCenter (pad12 z) 6) :
    DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) z :=
  (contDiffAt_fderiv_residualFun (m := ⊤)
    (contDiffAt_residualFun_vec z h1 h2 h3 h4 h5 h6 h7)).differentiableAt (by simp)

/-- **★ 球上 `hadj`（Lead 装配参数消解版，形状逐字对齐）**：
`∀ x ∈ closedBall certCR rhoCertR, DifferentiableAt ℝ (fun y => fderiv ℝ residualFun y) (first7 x)` ✓。

前提 = `BoxRstar` 签名里的**那 7 条球级非退化条件**（`hndRho`/`hndW`/`hndU1`/`hndU2`/`hndU3`/`hndU8`/`hndWp` ✓，
变量是 **`x : Fin 12 → ℝ`** ✓）；它们与我的 `h1…h7`（以 `pad12 z` 表述 ✓）之间由**根内 `Transport` 族**搭桥 ✓
（`angleVec_transport`/`Uvec_transport`/`hub0_transport`/`hub1_transport`/`wPoint_transport`/`ringCenter_transport` ✓，
取 `z := first7 x` ✓ —— 注意 `pad12 (first7 x) = x` **不成立** ✗✓ 但几何函数**只读 0..6 位** ✓ 故搬运等式成立 ✓）。 -/
theorem differentiableAt_fderiv_residualFun_ball
    (hndRho : ∀ x ∈ Metric.closedBall cCertR rhoCertR, ∀ j : Fin 9,
      (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0)
    (hndW : ∀ x ∈ Metric.closedBall cCertR rhoCertR, (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0)
    (hndU1 : ∀ x ∈ Metric.closedBall cCertR rhoCertR, Uvec x 1 ≠ hub1 x)
    (hndU2 : ∀ x ∈ Metric.closedBall cCertR rhoCertR, Uvec x 2 ≠ hub0 x)
    (hndU3 : ∀ x ∈ Metric.closedBall cCertR rhoCertR, Uvec x 3 ≠ hub0 x)
    (hndU8 : ∀ x ∈ Metric.closedBall cCertR rhoCertR, Uvec x 8 ≠ hub1 x)
    (hndWp : ∀ x ∈ Metric.closedBall cCertR rhoCertR, wPoint x ≠ ringCenter x 6) :
    ∀ x ∈ Metric.closedBall cCertR rhoCertR,
      DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) (first7 x) := by
  intro x hx
  have h6 : pad12 (first7 x) 6 = x 6 := by
    rw [pad12_six]
    rfl
  have h5 : pad12 (first7 x) 5 = x 5 := by
    rw [pad12_five]
    rfl
  have h4 : pad12 (first7 x) 4 = x 4 := by
    rw [pad12_four]
    rfl
  refine differentiableAt_fderiv_residualFun_of_nondeg (first7 x) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    rw [h6, angleVec_transport x]
    exact hndRho x hx j
  · rw [h6, h5, h4]
    exact hndW x hx
  · rw [Uvec_transport x 1, hub1_transport x]
    exact hndU1 x hx
  · rw [Uvec_transport x 2, hub0_transport x]
    exact hndU2 x hx
  · rw [Uvec_transport x 3, hub0_transport x]
    exact hndU3 x hx
  · rw [Uvec_transport x 8, hub1_transport x]
    exact hndU8 x hx
  · rw [wPoint_transport x, ringCenter_transport x 6]
    exact hndWp x hx

end HessSeam

end N11Formalization
