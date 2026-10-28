/-
  evidence/f1-step2/F1-BallD35-C10.lean
  =====================================

  **F1 第 2 步 · 步骤 (2) 中段**：`hJ` 的 12×12 里 **(a) 残差行 × λ 列 = 0** 的**球级镜像**，
  外加 **(c) 所需的两个可复用件**。

  消费接口 = `BoxRstar.lean` L374–376 的 `hJ`（`TCSystem` 的 12×12、全 12 维点、`Pi.single j 1 : Fin 12 → ℝ`）。

  **本件 4 条（全部已过门）**：
  1. **`fderiv_TCSystem_res_lam_any`**（镜像根内 `fderiv_TCSystem_res_lam` L269）—— **无条件**；
  2. `differentiableAt_fderiv_residualFun_of_ball`：**`hadj` 的球上无条件供给** —— **无条件**；
  3. `JT_lam_res_ball`：`(a)` 的 `∀ k m` 合取 —— **无条件**。

  **⇒ `hJ` 的 12×12：残差行的 `λ` 列已补齐（`z` 列见 `C9.mem_Jt_res_z_ball`）；
  只剩 `r ≥ 5`（KKT 行）那一半**。

  **未发货的 (c)**：`fderiv_TCSystem_kkt_lam_any`（KKT 行 × λ 列）本轮未过门；
  红件 + 错误原文已留档 `_scratch/C10c_attempt_ERR.*`（发货件不含红）。
  其中 `differentiableAt_adjointBlockRow_any` 与 `fderiv_TCSystem_kkt_lam_any` 两条均在红档内
  ⇒ 下一轮的 (c) 只需拼装（`hadj` 的供给件已在本件过门）。

  真实等级：kernel-proved，零 sorry / 零自定义 axiom / 零 native_decide；未接根。
-/
import N11Formalization.F1.BallD35C9
import N11Formalization.ResidualDerivJTHess

/-! ## 0. 外部名自查前言（Lead R238 过程口径） -/
#check @N11Formalization.fderiv_TCSystem_res_lam
#check @N11Formalization.fderiv_apply_val
#check @N11Formalization.TCSystem_row_eq_residualFun
#check @N11Formalization.proj7CLM_single_up5
#check @N11Formalization.hasFDerivAt_first7
#check @N11Formalization.up5
#check @N11Formalization.row5
#check @N11Formalization.evCLM
#check @N11Formalization.gFun
#check @N11Formalization.differentiableAt_adjointBlockRow
#check @N11Formalization.hasFDerivAt_residualFun_first7_any
#check @N11Formalization.fderiv_residualFun_first7_any
#check @N11Formalization.first7_pad12
#check @N11Formalization.contDiffAt_fderiv_residualFun
#check @N11Formalization.contDiffAt_residualFun
#check @N11Formalization.differentiableAt_TCSystem_of_conditions
#check @N11Formalization.nd_all_via_dist

noncomputable section

namespace N11Formalization

/-! ## (a) 残差行 × λ 列 = 0（球级、无条件） -/

theorem fderiv_TCSystem_res_lam_any (z : Fin 7 → ℝ)
    (hdT : DifferentiableAt ℝ TCSystem (pad12 z))
    (hd : DifferentiableAt ℝ residualFun z) (k : Fin 5) (m : Fin 5) :
    (fderiv ℝ TCSystem (pad12 z) (Pi.single (up5 m) (1 : ℝ))) (row5 k) = 0 := by
  have hd' : DifferentiableAt ℝ residualFun (first7 (pad12 z)) := by
    rw [first7_pad12 z]; exact hd
  rw [fderiv_apply_val hdT (row5 k) (Pi.single (up5 m) (1 : ℝ)),
    TCSystem_row_eq_residualFun k]
  have hdiff : DifferentiableAt ℝ (fun u : Fin 12 → ℝ => residualFun (first7 u)) (pad12 z) :=
    (hasFDerivAt_residualFun_first7_any (pad12 z) hd').differentiableAt
  rw [fderiv_apply hdiff k, fderiv_residualFun_first7_any (pad12 z) hd', first7_pad12 z]
  simp only [ContinuousLinearMap.comp_apply, proj7CLM_single_up5, ContinuousLinearMap.map_zero]

/-! ## (c) 的两个可复用零件（(c) 本身未发货） -/

theorem differentiableAt_fderiv_residualFun_of_ball (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR) :
    DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) z := by
  obtain ⟨hU1, hU2, hU3, hU8, hWpne⟩ := nd_all_via_dist
  have hC : ContDiffAt ℝ (⊤ + 1) (fun w : Fin 7 → ℝ => residualFun w) z := by
    rw [contDiffAt_pi]
    intro i
    exact contDiffAt_residualFun (n := ⊤ + 1) z (hrho_of_ball z hz) (hradW_of_ball z hz)
      (hU1 (pad12 z) hz) (hU2 (pad12 z) hz) (hU3 (pad12 z) hz) (hU8 (pad12 z) hz)
      (hWpne (pad12 z) hz) i
  exact (contDiffAt_fderiv_residualFun (m := ⊤) hC).differentiableAt (by simp)

/-! ## (a) 的 ∀ k m 合取（无条件） -/

theorem JT_lam_res_ball (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR) :
    ∀ k : Fin 5, ∀ m : Fin 5,
      (fderiv ℝ TCSystem (pad12 z) (Pi.single (up5 m) (1 : ℝ))) (row5 k) = 0 := by
  obtain ⟨hU1, hU2, hU3, hU8, hWpne⟩ := nd_all_via_dist
  have hd : DifferentiableAt ℝ residualFun z := differentiableAt_residualFun_of_ball z hz
  have hdT : DifferentiableAt ℝ TCSystem (pad12 z) :=
    differentiableAt_TCSystem_of_conditions (pad12 z) (hrho_of_ball z hz) (hradW_of_ball z hz)
      (hU1 (pad12 z) hz) (hU2 (pad12 z) hz) (hU3 (pad12 z) hz) (hU8 (pad12 z) hz)
      (hWpne (pad12 z) hz)
  exact fun k m => fderiv_TCSystem_res_lam_any z hdT hd k m

end N11Formalization

#print axioms N11Formalization.fderiv_TCSystem_res_lam_any
#print axioms N11Formalization.differentiableAt_fderiv_residualFun_of_ball
#print axioms N11Formalization.JT_lam_res_ball
