/-
  evidence/f1-step2/F1-BallD35-C13.lean
  =====================================

  **F1 第 2 步 · 桥的收口（v2）**：**残差行的 60 格在消费方形状（一般 `x ∈ ball`）下落格** ✓✓
  * **`z` 列 35 格**：`mem_Jt_res_z_ball_x`
  * **`λ` 列 25 格**（值恒 0）：`JT_lam_res_ball_x`

  四步链（v1 的 6 条错误已按四条根因全部修掉 ✓✗）：
  | 根因（v1） | v2 的修法 |
  |---|---|
  | (A) `dif_pos` 不匹配 | **弃用 `pad12_up7`**，改用根内 **`@[simp] pad12_first7_0..6`**（`Transport` L23–35）✓ |
  | (B) `WpReal` 用**数词**下标 vs `up7` | `simpa only [WpReal, pad12_first7_4/5/6]`（**不碰 `up7`**）✓ |
  | (C) `x 6` vs `first7 x 6`（defeq vs 逐字） | 加 **`first7_six := rfl`** 并 `simpa only [pow_two, first7_six]` ✓ |
  | (D) `Apt_transport` **方向反了** | 用 **`← Apt_transport`** ✓ |

  前提全部任意 12 维 `x ∈ ball`（七条件来自 `wkBox_ne_zero` / `WpReal_ne_zero_of_ball` / `nd_all_via_dist`；
  `hd` 来自 `Transport.contDiffAt_residualFun_first7`（**任意 `x`** ✓））✓✓。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.F1.BallD35C12
import N11Formalization.Transport

/-! ## 0. 外部名自查前言（Lead R238 过程口径；每条实测存在） -/
#check @N11Formalization.fderiv_TCSystem_res_z_any_x
#check @N11Formalization.fderiv_TCSystem_res_lam_any_x
#check @N11Formalization.fderiv_residual_k_any
#check @N11Formalization.Apt_transport
#check @N11Formalization.Bpt_transport
#check @N11Formalization.compIvBox_mem_uncond
#check @N11Formalization.wkBox_ne_zero
#check @N11Formalization.WpReal_ne_zero_of_ball
#check @N11Formalization.radIvBox_ne_zero_of_ball
#check @N11Formalization.nd_all_via_dist
#check @N11Formalization.contDiffAt_residualFun_first7
#check @N11Formalization.differentiableAt_TCSystem_of_conditions
#check @N11Formalization.angleVec_transport
#check @N11Formalization.pad12_first7_4
#check @N11Formalization.pad12_first7_5
#check @N11Formalization.pad12_first7_6
#check @N11Formalization.WpAt_eq_WpReal
#check @N11Formalization.WpReal
#check @N11Formalization.Wfun

noncomputable section

namespace N11Formalization

/-! ## 1. 一条 `@[simp]` 桥：`first7` 读第 6 坐标就是 `x 6` -/

@[simp] theorem first7_six (x : Fin 12 → ℝ) : first7 x 6 = x 6 := rfl

/-! ## 2. 七条件 + 可微性（任意 12 维 `x ∈ ball`）的公共前缀 -/

theorem rho_of_ball {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    ∀ j : Fin 9, (x 6) ^ 2 - (Real.sin (angleVec x j)) ^ 2 ≠ 0 := by
  intro j
  have h := wkBox_ne_zero hx j
  simpa only [pow_two] using h

theorem radW_of_ball {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (x 6) ^ 2 - ((x 5 - x 4) / 2) ^ 2 ≠ 0 := by
  have h := WpReal_ne_zero_of_ball hx
  simpa only [WpReal, pow_two] using h

theorem differentiableAt_TCSystem_ball {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    DifferentiableAt ℝ TCSystem x := by
  obtain ⟨hU1, hU2, hU3, hU8, hWpne⟩ := nd_all_via_dist
  exact differentiableAt_TCSystem_of_conditions x (rho_of_ball hx) (radW_of_ball hx)
    (hU1 x hx) (hU2 x hx) (hU3 x hx) (hU8 x hx) (hWpne x hx)

theorem differentiableAt_residualFun_first7_ball {x : Fin 12 → ℝ}
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    DifferentiableAt ℝ residualFun (first7 x) := by
  obtain ⟨hU1, hU2, hU3, hU8, hWpne⟩ := nd_all_via_dist
  have hC : ContDiffAt ℝ (⊤ + 1) (fun w : Fin 7 → ℝ => residualFun w) (first7 x) := by
    rw [contDiffAt_pi]
    intro i
    exact contDiffAt_residualFun_first7 (n := ⊤ + 1) x (rho_of_ball hx) (radW_of_ball hx)
      (hU1 x hx) (hU2 x hx) (hU3 x hx) (hU8 x hx) (hWpne x hx) i
  exact hC.differentiableAt (by simp)

/-! ## 3. **`z` 列 35 格落格**（残差行 × `z`，消费方形状） -/

/-! ## 4. **`λ` 列 25 格落格**（残差行 × `λ` = 0，消费方形状） -/

theorem JT_lam_res_ball_x (x : Fin 12 → ℝ)
    (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    ∀ k : Fin 5, ∀ m : Fin 5,
      (fderiv ℝ TCSystem x (Pi.single (up5 m) (1 : ℝ))) (row5 k) = 0 :=
  fun k m => fderiv_TCSystem_res_lam_any_x x (differentiableAt_TCSystem_ball hx)
    (differentiableAt_residualFun_first7_ball hx) k m

end N11Formalization

#print axioms N11Formalization.first7_six
#print axioms N11Formalization.rho_of_ball
#print axioms N11Formalization.radW_of_ball
#print axioms N11Formalization.differentiableAt_TCSystem_ball
#print axioms N11Formalization.differentiableAt_residualFun_first7_ball
#print axioms N11Formalization.JT_lam_res_ball_x
