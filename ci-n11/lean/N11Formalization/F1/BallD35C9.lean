/-
  evidence/f1-step2/F1-BallD35-C9.lean
  ====================================

  **F1 第 2 步 · 步骤 (2) 前半：把已受审的两件并入**消费点 `hJ` 的形状**。**

  **消费接口（我实测读出的，`BoxRstar.lean` L374–376）** ✓✓：
  ```lean
  (Jt : Fin 12 → Fin 12 → RatInterval)
  (hJ : ∀ x ∈ Metric.closedBall certCR rhoCertR, ∀ k j : Fin 12,
        (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
  ```
  ⇒ **`hJ` 是 `TCSystem` 的 **12×12** Jacobian、在整个球上、且列方向是 `Pi.single j 1 : Fin 12 → ℝ`** ✗✓
  （**不是** 我此前的 `Fin 5 × Fin 7`、也不是 `Pi.single i 1 : Fin 7 → ℝ`）⇒ **形状必须转写**。

  **本件做的事**：
  * **残差行的 5×7 块**（`r < 5, c = up7 j`）**升级到消费点形状**：
    `(compIvBox k j).Mem ((fderiv ℝ TCSystem (pad12 z) (Pi.single (up7 j) 1)) (row5 k))` ✓✓
    —— 这是对 `ResidualDerivJT.mem_Jt_res_z`（**盒心**版，用 `D = compIv`）的
    **球级版本**（用**我的 `compIvBox`**），即原任务里"球级 `ndJT_res_z`"的**残差块部分** ✓；
  * 并把 C8 的逐格结论打包成 **`∀ k j` 合取（端到端无条件）** ✓。

  **未做的事（如实）** ✗：`hJ` 的其余块（`r ≥ 5` 的 KKT 行 + `c ≥ 7` 的 `λ` 列）**不在本件**：
  它们要 `Hess`（**根内自称"未证块的参数"** ✓）与二阶导数的一般点版 ⇒ **不同的义务族** ✓。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.F1.BallD35C8
import N11Formalization.ResidualDerivJT
import N11Formalization.Transport

/-! ## 0. **外部名自查前言**（Lead R238 过程口径） -/
#check @N11Formalization.hasFDerivAt_first7
#check @N11Formalization.hasFDerivAt_residualFun_first7
#check @N11Formalization.fderiv_residualFun_first7
#check @N11Formalization.fderiv_TCSystem_res_z
#check @N11Formalization.fderiv_apply_val
#check @N11Formalization.TCSystem_row_eq_residualFun
#check @N11Formalization.proj7CLM_single_up7
#check @N11Formalization.row5
#check @N11Formalization.up7
#check @N11Formalization.compIvBox
#check @N11Formalization.ndJT_res_z_box_uncond
#check @N11Formalization.differentiableAt_TCSystem_of_conditions
#check @N11Formalization.nd_all_via_dist
#check @N11Formalization.hrho_of_ball
#check @N11Formalization.hradW_of_ball

noncomputable section

namespace N11Formalization

/-! ## 1. `first7` 链式法则的**一般点**版（镜像 `ResidualDerivJT`，`u0 → first7 x`） -/

theorem hasFDerivAt_residualFun_first7_any (x : Fin 12 → ℝ)
    (hd : DifferentiableAt ℝ residualFun (first7 x)) :
    HasFDerivAt (fun u : Fin 12 → ℝ => residualFun (first7 u))
      ((fderiv ℝ residualFun (first7 x)).comp proj7CLM) x :=
  hd.hasFDerivAt.comp x (hasFDerivAt_first7 x)

theorem fderiv_residualFun_first7_any (x : Fin 12 → ℝ)
    (hd : DifferentiableAt ℝ residualFun (first7 x)) :
    fderiv ℝ (fun u : Fin 12 → ℝ => residualFun (first7 u)) x
      = (fderiv ℝ residualFun (first7 x)).comp proj7CLM :=
  (hasFDerivAt_residualFun_first7_any x hd).fderiv

/-- `first7 (pad12 z) = z`（`pad12` 与 `first7` 在 `Fin 7` 上互逆）。 -/
theorem first7_pad12 (z : Fin 7 → ℝ) : first7 (pad12 z) = z := by
  funext i
  simp only [first7, pad12, dif_pos i.isLt]

/-! ## 2. **一般点**的 `fderiv_TCSystem_res_z`（镜像 `ResidualDerivJT` L256，`cCertR → pad12 z`） -/

theorem fderiv_TCSystem_res_z_any (z : Fin 7 → ℝ)
    (hdT : DifferentiableAt ℝ TCSystem (pad12 z))
    (hd : DifferentiableAt ℝ residualFun z) (k : Fin 5) (j : Fin 7) :
    (fderiv ℝ TCSystem (pad12 z) (Pi.single (up7 j) (1 : ℝ))) (row5 k)
      = (fderiv ℝ residualFun z (Pi.single j 1)) k := by
  rw [fderiv_apply_val hdT (row5 k) (Pi.single (up7 j) (1 : ℝ)),
    TCSystem_row_eq_residualFun k]
  have hdiff : DifferentiableAt ℝ (fun u : Fin 12 → ℝ => residualFun (first7 u)) (pad12 z) :=
    (hasFDerivAt_residualFun_first7_any (pad12 z) (by rw [first7_pad12]; exact hd)).differentiableAt
  rw [fderiv_apply hdiff k, fderiv_residualFun_first7_any (pad12 z) (by rw [first7_pad12]; exact hd),
    first7_pad12 z]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    proj7CLM_single_up7]

/-! ## 3. **消费点形状的球级残差块**（对 `mem_Jt_res_z` 的球级升级） -/

theorem mem_Jt_res_z_ball (k : Fin 5) (j : Fin 7) (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR) :
    (compIvBox k j).Mem
      ((fderiv ℝ TCSystem (pad12 z) (Pi.single (up7 j) (1 : ℝ))) (row5 k)) := by
  obtain ⟨hU1, hU2, hU3, hU8, hWpne⟩ := nd_all_via_dist
  have hd : DifferentiableAt ℝ residualFun z := differentiableAt_residualFun_of_ball z hz
  have hdT : DifferentiableAt ℝ TCSystem (pad12 z) :=
    differentiableAt_TCSystem_of_conditions (pad12 z) (hrho_of_ball z hz) (hradW_of_ball z hz)
      (hU1 (pad12 z) hz) (hU2 (pad12 z) hz) (hU3 (pad12 z) hz) (hU8 (pad12 z) hz)
      (hWpne (pad12 z) hz)
  rw [fderiv_TCSystem_res_z_any z hdT hd k j]
  exact ndJT_res_z_box_uncond k j z hz

/-! ## 4. **端到端无条件的 `∀ k j` 合取**（消费点形状 + `residualFun` 形状） -/

/-- **球级残差块（无条件）**：两种形状一次给出 ——
* 消费点形状（`TCSystem` 的 12×12 块，`(row5 k, up7 j)`）；
* `residualFun` 形状（C8 的原样）。 -/
theorem ndJT_res_zBall_all (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR) :
    (∀ k : Fin 5, ∀ j : Fin 7,
        (compIvBox k j).Mem
          ((fderiv ℝ TCSystem (pad12 z) (Pi.single (up7 j) (1 : ℝ))) (row5 k)))
      ∧ (∀ k : Fin 5, ∀ j : Fin 7,
        (compIvBox k j).Mem ((fderiv ℝ residualFun z (Pi.single j 1)) k)) :=
  ⟨fun k j => mem_Jt_res_z_ball k j z hz, fun k j => ndJT_res_z_box_uncond k j z hz⟩

end N11Formalization

#print axioms N11Formalization.hasFDerivAt_residualFun_first7_any
#print axioms N11Formalization.fderiv_residualFun_first7_any
#print axioms N11Formalization.first7_pad12
#print axioms N11Formalization.fderiv_TCSystem_res_z_any
#print axioms N11Formalization.mem_Jt_res_z_ball
#print axioms N11Formalization.ndJT_res_zBall_all
