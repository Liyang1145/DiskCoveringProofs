/-
  evidence/f1-step2/F1-BallD35-C1.lean
  ====================================

  **F1 第 2 步 · 件 C 的第一片（`C1`）**：把**链式法则的第一层**从"点冻结于 `u0`"升级为
  **一般点 `z`** 的版本。

  **为什么这是件 C 里"可省的一环"** ✓✓：`angleVec (pad12 ·) j` 与
  `thetaOf (angleVec (pad12 ·)) j` 对 `z` 是**仿射**的（`ResidualDeriv.angleVec_pad12_affine` /
  `thetaOf_angleVec_affine` **本身就写成一般 `z`** ✓）⇒ 它们的 `HasFDerivAt` **CLM 与点无关**
  （常数整数矩阵 `daCLM` / `dthetaCLM`）⇒ 件 C 只需重做 `ρ`、`sin`/`cos`、`√`、乘积与 `dist`
  这几层，**不必重做角层** ✓✓（把这条从"断言"变成"定理"就是本片的目的）。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.ResidualDerivD

noncomputable section

namespace N11Formalization

/-! ## 1. 任意点的线性组合导数（`ResidualDeriv.fderiv_linComb` 的点无关版） -/

theorem hasFDerivAt_linComb_any (a : Fin 7 → ℝ) (z : Fin 7 → ℝ) :
    HasFDerivAt (fun z' : Fin 7 → ℝ => ∑ i : Fin 7, a i * z' i)
      (∑ i : Fin 7, a i • coord i) z := by
  rw [show (fun z' : Fin 7 → ℝ => ∑ i : Fin 7, a i * z' i)
      = ∑ i : Fin 7, fun z' : Fin 7 → ℝ => a i * z' i from rfl]
  refine HasFDerivAt.sum fun i _ => ?_
  exact (ContinuousLinearMap.hasFDerivAt (f := coord i) (x := z)).const_mul (a i)

/-! ## 2. 角层：`a_j` 与 `θ_j` 的 `HasFDerivAt` 在**任意点**（CLM 与点无关） -/

theorem hasFDerivAt_angleVec_any (j : Fin 9) (z : Fin 7 → ℝ) :
    HasFDerivAt (fun z' : Fin 7 → ℝ => angleVec (pad12 z') j) (daCLM j) z := by
  have h : (fun z' : Fin 7 → ℝ => angleVec (pad12 z') j)
      = fun z' => angleVec (pad12 0) j + ∑ i : Fin 7, (dAngle j i : ℝ) * z' i := by
    funext z'
    exact angleVec_pad12_affine j z'
  rw [h, daCLM]
  exact (hasFDerivAt_linComb_any (fun i => (dAngle j i : ℝ)) z).const_add _

theorem hasFDerivAt_thetaOf_any (j : Fin 9) (z : Fin 7 → ℝ) :
    HasFDerivAt (fun z' : Fin 7 → ℝ => thetaOf (angleVec (pad12 z')) j) (dthetaCLM j) z := by
  have h : (fun z' : Fin 7 → ℝ => thetaOf (angleVec (pad12 z')) j)
      = fun z' => thetaOf (angleVec (pad12 0)) j + ∑ i : Fin 7, (dTheta j i : ℝ) * z' i := by
    funext z'
    exact thetaOf_angleVec_affine j z'
  rw [h, dthetaCLM]
  exact (hasFDerivAt_linComb_any (fun i => (dTheta j i : ℝ)) z).const_add _

/-- **标量读数（一般点）**：`∂a_j/∂z_i = dAngle j i`（**与点无关**）。
不用独立求和，直接复用已证成的 `daCLM_apply_single` ✓。 -/
theorem fderiv_angleVec_any_single (j : Fin 9) (i : Fin 7) (z : Fin 7 → ℝ) :
    fderiv ℝ (fun z' : Fin 7 → ℝ => angleVec (pad12 z') j) z (Pi.single i 1)
      = (dAngle j i : ℝ) := by
  rw [(hasFDerivAt_angleVec_any j z).fderiv, daCLM_apply_single]

/-- **标量读数（一般点）**：`∂θ_j/∂z_i = dTheta j i`（**与点无关**）。
同理复用 `dthetaCLM_apply_single` ✓。 -/
theorem fderiv_thetaOf_any_single (j : Fin 9) (i : Fin 7) (z : Fin 7 → ℝ) :
    fderiv ℝ (fun z' : Fin 7 → ℝ => thetaOf (angleVec (pad12 z')) j) z (Pi.single i 1)
      = (dTheta j i : ℝ) := by
  rw [(hasFDerivAt_thetaOf_any j z).fderiv, dthetaCLM_apply_single]

/-- **收盘陈述（点无关性）**：角层的 `HasFDerivAt` 在**任意点** `z` 都可用、CLM 与点无关
⇒ 件 C 不必重做角层 ✓。 -/
theorem angle_layer_pointfree (z : Fin 7 → ℝ) :
    HasFDerivAt (fun z' : Fin 7 → ℝ => angleVec (pad12 z') 4) (daCLM 4) z ∧
      HasFDerivAt (fun z' : Fin 7 → ℝ => thetaOf (angleVec (pad12 z')) 6) (dthetaCLM 6) z :=
  ⟨hasFDerivAt_angleVec_any 4 z, hasFDerivAt_thetaOf_any 6 z⟩

end N11Formalization

#print axioms N11Formalization.hasFDerivAt_linComb_any
#print axioms N11Formalization.hasFDerivAt_angleVec_any
#print axioms N11Formalization.hasFDerivAt_thetaOf_any
#print axioms N11Formalization.fderiv_angleVec_any_single
#print axioms N11Formalization.fderiv_thetaOf_any_single
#print axioms N11Formalization.angle_layer_pointfree
