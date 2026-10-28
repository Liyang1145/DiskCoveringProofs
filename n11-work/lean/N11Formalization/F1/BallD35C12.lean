/-
  evidence/f1-step2/F1-BallD35-C12.lean
  =====================================

  **F1 第 2 步 · 桥的两半（(S1) + (S2)）**：把 `fderiv` 形态与几何一致**都搬到一般 `x : Fin 12 → ℝ`** ✓✓

  **Lead 核过的现成件**（`Transport.lean`，**根 cone 内**）：`angleVec_transport` / `thetaOf_transport` /
  `rhoK_transport` / `hub0_transport` / `hub1_transport` / `ringCenter_transport` / `arcEnd_transport` /
  `Uvec_transport` / `wPoint_transport` / `residual_transport` —— **整族已在根里** ✓✓
  ⇒ **本件不再写任何 transport**（**我上一轮"6–9 条引理 + 表查询"的估计作废** ✗✓：
  `dAngle : Fin 9 → Fin 7 → ℤ` ⇒ "`i ≥ 7`" 对该指标**恒假、无内容** ✗）。

  **本件内容**：
  | # | 命题 | 来源 |
  |---|---|---|
  | (S1a) | `fderiv_TCSystem_res_z_any_x`：`(fderiv ℝ TCSystem x (Pi.single (up7 j) 1)) (row5 k) = (fderiv ℝ residualFun (first7 x) (Pi.single j 1)) k` | C9 的 `fderiv_TCSystem_res_z_any` 搬到一般 `x`（**证明逐字，且更短**：`hd` 直接取在 `first7 x`，**不需 `first7_pad12` 搬运** ✓✓） |
  | (S1b) | `fderiv_TCSystem_res_lam_any_x`：残差行 × λ 列 = 0（一般 `x`） | C10 的 `fderiv_TCSystem_res_lam_any` 搬到一般 `x` ✓ |
  | (S2) | `Apt_transport` / `Bpt_transport`：`Apt k (pad12 (first7 x)) = Apt k x`（与 `Bpt` 同） | 由 `Apt`/`Bpt` 的**定义**（`ResidualDerivD` L281/L288：`Uvec u 1/2/3/8`、`wPoint u`；`hub1/hub0/hub0/hub1/ringCenter u 6`）+ 根内 **`Uvec_transport`/`wPoint_transport`/`hub*_transport`/`ringCenter_transport`** 组合 ✓ |

  **⇒ 下一件**：`mem_Jt_res_z_ball_x (k) (j) {x} (hx : x ∈ ball) : (compIvBox k j).Mem ((fderiv ℝ TCSystem x (Pi.single (up7 j) 1)) (row5 k))`
  = `rw [fderiv_TCSystem_res_z_any_x …]` + `rw [fderiv_residual_k_any k j (first7 x) …]` + `simp only [Apt_transport, Bpt_transport]` + `exact compIvBox_mem_uncond k j hx` ✓（**近一行**）⇒ **计数 0 → 60** ✓

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.F1.BallD35C10
import N11Formalization.ResidualDerivJTHess

/-! ## 0. 外部名自查前言（Lead R238 过程口径；每条实测存在） -/
#check @N11Formalization.fderiv_apply_val
#check @N11Formalization.TCSystem_row_eq_residualFun
#check @N11Formalization.hasFDerivAt_residualFun_first7_any
#check @N11Formalization.fderiv_residualFun_first7_any
#check @N11Formalization.fderiv_TCSystem_res_z_any
#check @N11Formalization.proj7CLM_single_up5
#check @N11Formalization.proj7CLM_single_up7
#check @N11Formalization.up7
#check @N11Formalization.up5
#check @N11Formalization.row5
#check @N11Formalization.Apt
#check @N11Formalization.Bpt
#check @N11Formalization.Uvec_transport
#check @N11Formalization.wPoint_transport
#check @N11Formalization.hub0_transport
#check @N11Formalization.hub1_transport
#check @N11Formalization.ringCenter_transport

noncomputable section

namespace N11Formalization

/-! ## (S1a) 残差行 × `z` 列：`fderiv` 形态的**一般点**读数 -/

theorem fderiv_TCSystem_res_z_any_x (x : Fin 12 → ℝ)
    (hdT : DifferentiableAt ℝ TCSystem x)
    (hd : DifferentiableAt ℝ residualFun (first7 x)) (k : Fin 5) (j : Fin 7) :
    (fderiv ℝ TCSystem x (Pi.single (up7 j) (1 : ℝ))) (row5 k)
      = (fderiv ℝ residualFun (first7 x) (Pi.single j 1)) k := by
  rw [fderiv_apply_val hdT (row5 k) (Pi.single (up7 j) (1 : ℝ)),
    TCSystem_row_eq_residualFun k]
  have hdiff : DifferentiableAt ℝ (fun u : Fin 12 → ℝ => residualFun (first7 u)) x :=
    (hasFDerivAt_residualFun_first7_any x hd).differentiableAt
  rw [fderiv_apply hdiff k, fderiv_residualFun_first7_any x hd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    proj7CLM_single_up7]

/-! ## (S1b) 残差行 × `λ` 列 = 0（一般点） -/

theorem fderiv_TCSystem_res_lam_any_x (x : Fin 12 → ℝ)
    (hdT : DifferentiableAt ℝ TCSystem x)
    (hd : DifferentiableAt ℝ residualFun (first7 x)) (k : Fin 5) (m : Fin 5) :
    (fderiv ℝ TCSystem x (Pi.single (up5 m) (1 : ℝ))) (row5 k) = 0 := by
  rw [fderiv_apply_val hdT (row5 k) (Pi.single (up5 m) (1 : ℝ)),
    TCSystem_row_eq_residualFun k]
  have hdiff : DifferentiableAt ℝ (fun u : Fin 12 → ℝ => residualFun (first7 u)) x :=
    (hasFDerivAt_residualFun_first7_any x hd).differentiableAt
  rw [fderiv_apply hdiff k, fderiv_residualFun_first7_any x hd]
  simp only [ContinuousLinearMap.comp_apply, proj7CLM_single_up5,
    ContinuousLinearMap.map_zero]

/-! ## (S2) 几何一致：`Apt`/`Bpt` 在 `pad12 (first7 x)` 与 `x` 上相等 -/

theorem Apt_transport (k : Fin 5) (x : Fin 12 → ℝ) :
    Apt k (pad12 (first7 x)) = Apt k x := by
  match k with
  | 0 => simp only [Apt, Uvec_transport]
  | 1 => simp only [Apt, Uvec_transport]
  | 2 => simp only [Apt, Uvec_transport]
  | 3 => simp only [Apt, Uvec_transport]
  | 4 => simp only [Apt, wPoint_transport]

theorem Bpt_transport (k : Fin 5) (x : Fin 12 → ℝ) :
    Bpt k (pad12 (first7 x)) = Bpt k x := by
  match k with
  | 0 => simp only [Bpt, hub1_transport]
  | 1 => simp only [Bpt, hub0_transport]
  | 2 => simp only [Bpt, hub0_transport]
  | 3 => simp only [Bpt, hub1_transport]
  | 4 => simp only [Bpt, ringCenter_transport]

end N11Formalization

#print axioms N11Formalization.fderiv_TCSystem_res_z_any_x
#print axioms N11Formalization.fderiv_TCSystem_res_lam_any_x
#print axioms N11Formalization.Apt_transport
#print axioms N11Formalization.Bpt_transport
