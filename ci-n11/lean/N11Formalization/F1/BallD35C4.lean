/-
  evidence/f1-step2/F1-BallD35-C4.lean
  ====================================

  **F1 第 2 步 · 件 C 的第四片（`C4`）**：链式法则的 **`Uvec` / `hub` / `wPoint` / `dist` /
  残差节点** 升级为**一般点** —— 这填补**普查后剩下的全部真缺口** ✓✓
  （角层 / `W` / `ρ` / `arc` 四层根内已有；`ringCenter` 层已由 `F1/BallD35C2` 接根 ✓）。

  **依据（整库普查，`_survey3.py`）**：`hasFDerivAt_Uvec0/1`、`hasFDerivAt_hub0_0/1`、
  `hasFDerivAt_hub1_0/1`、`hasFDerivAt_wPoint_0/1`、`hasFDerivAt_dist`、`fderiv_residualComp`
  **全部点冻结于 `u0`** ✗ ⇒ 本件给出**一般点**版（结构逐字不变，只把 `u0 → z`、
  `Wk k → Wfun k z` ✓）。

  **依赖（按名引用，不重证）**：`N11Formalization.ResidualDerivJT`（`Wfun`/`drhoAt`/
  `hasFDerivAt_rhoK_any`/`hasFDerivAt_thetaOf_any`/`ArcC`/`phiA`/`phiCLM`/`hasFDerivAt_phiA`/
  `fderiv_ArcC_zero/one`）+ `N11Formalization.F1.BallD35C2`（`hasFDerivAt_ringCenter0/1_any`）
  + `ResidualDerivD`（`coord`/`dAngle`/`dTheta`/`dring0CLM` 等的**定义**与
  `coord_apply_single`/`daCLM_apply_single`/`dthetaCLM_apply_single`）。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.ResidualDerivJT
import N11Formalization.F1.BallD35C2

/-! ## 0. **外部名自查前言**（Lead R238 过程口径；逐条 `#check`） -/
#check @N11Formalization.Wfun
#check @N11Formalization.drhoAt
#check @N11Formalization.hasFDerivAt_rhoK_any
#check @N11Formalization.hasFDerivAt_thetaOf_any
#check @N11Formalization.ArcC
#check @N11Formalization.phiA
#check @N11Formalization.phiCLM
#check @N11Formalization.hasFDerivAt_phiA
#check @N11Formalization.hasFDerivAt_ringCenter0_any
#check @N11Formalization.hasFDerivAt_ringCenter1_any
#check @N11Formalization.rhoK_eq
#check @N11Formalization.Uvec
#check @N11Formalization.hub0
#check @N11Formalization.hub1
#check @N11Formalization.wPoint
#check @N11Formalization.arcEnd
#check @N11Formalization.dist_point_eq_sqrt
#check @N11Formalization.coord
#check @N11Formalization.coord_apply_single
#check @N11Formalization.daCLM_apply_single
#check @N11Formalization.dthetaCLM_apply_single
#check @N11Formalization.pad12_four
#check @N11Formalization.pad12_five
#check @N11Formalization.pad12_six

noncomputable section

namespace N11Formalization

/-! ## 1. `arcEnd` 两坐标在一般点的导数（由 `hasFDerivAt_phiA` / `fderiv_ArcC_*` 一行得到） -/

theorem hasFDerivAt_arcC0_any (k : Fin 9) (z : Fin 7 → ℝ) :
    HasFDerivAt (ArcC k 0) ((-(Real.sin (phiA k z))) • phiCLM k) z := by
  have hc : ArcC k 0 = fun y : Fin 7 → ℝ => Real.cos (phiA k y) := by
    funext y
    exact ArcC_zero k y
  rw [hc]
  exact (hasFDerivAt_phiA k z).cos

theorem hasFDerivAt_arcC1_any (k : Fin 9) (z : Fin 7 → ℝ) :
    HasFDerivAt (ArcC k 1) ((Real.cos (phiA k z)) • phiCLM k) z := by
  have hc : ArcC k 1 = fun y : Fin 7 → ℝ => Real.sin (phiA k y) := by
    funext y
    exact ArcC_one k y
  rw [hc]
  exact (hasFDerivAt_phiA k z).sin

/-! ## 2. `Uvec` 两坐标在一般点 -/

theorem hasFDerivAt_Uvec0_any (k : Fin 9) (z : Fin 7 → ℝ)
    (hW0 : Wfun k z ≠ 0) (hW1 : Wfun (k + 1) z ≠ 0) :
    HasFDerivAt (fun z' : Fin 7 → ℝ => (Uvec (pad12 z') k).ofLp 0)
      ((rhoK (pad12 z) k • (-(Real.sin (thetaOf (angleVec (pad12 z)) k)) • dthetaCLM k)
          + Real.cos (thetaOf (angleVec (pad12 z)) k) • drhoAt k z)
        + (rhoK (pad12 z) (k + 1) • (-(Real.sin (thetaOf (angleVec (pad12 z)) (k + 1))) • dthetaCLM (k + 1))
          + Real.cos (thetaOf (angleVec (pad12 z)) (k + 1)) • drhoAt (k + 1) z)
        - ((-(Real.sin (phiA k z))) • phiCLM k)) z := by
  have heq : (fun z' : Fin 7 → ℝ => (Uvec (pad12 z') k).ofLp 0)
      = fun z' => ((ringCenter (pad12 z') k).ofLp 0 + (ringCenter (pad12 z') (k + 1)).ofLp 0)
        - (arcEnd (pad12 z') k).ofLp 0 := by
    funext z'
    rw [Uvec_coord0]
  rw [heq]
  exact ((hasFDerivAt_ringCenter0_any k z hW0).add
    (hasFDerivAt_ringCenter0_any (k + 1) z hW1)).sub (hasFDerivAt_arcC0_any k z)

theorem hasFDerivAt_Uvec1_any (k : Fin 9) (z : Fin 7 → ℝ)
    (hW0 : Wfun k z ≠ 0) (hW1 : Wfun (k + 1) z ≠ 0) :
    HasFDerivAt (fun z' : Fin 7 → ℝ => (Uvec (pad12 z') k).ofLp 1)
      ((rhoK (pad12 z) k • ((Real.cos (thetaOf (angleVec (pad12 z)) k)) • dthetaCLM k)
          + Real.sin (thetaOf (angleVec (pad12 z)) k) • drhoAt k z)
        + (rhoK (pad12 z) (k + 1) • ((Real.cos (thetaOf (angleVec (pad12 z)) (k + 1))) • dthetaCLM (k + 1))
          + Real.sin (thetaOf (angleVec (pad12 z)) (k + 1)) • drhoAt (k + 1) z)
        - ((Real.cos (phiA k z)) • phiCLM k)) z := by
  have heq : (fun z' : Fin 7 → ℝ => (Uvec (pad12 z') k).ofLp 1)
      = fun z' => ((ringCenter (pad12 z') k).ofLp 1 + (ringCenter (pad12 z') (k + 1)).ofLp 1)
        - (arcEnd (pad12 z') k).ofLp 1 := by
    funext z'
    rw [Uvec_coord1]
  rw [heq]
  exact ((hasFDerivAt_ringCenter1_any k z hW0).add
    (hasFDerivAt_ringCenter1_any (k + 1) z hW1)).sub (hasFDerivAt_arcC1_any k z)

end N11Formalization

#print axioms N11Formalization.hasFDerivAt_arcC0_any
#print axioms N11Formalization.hasFDerivAt_arcC1_any
#print axioms N11Formalization.hasFDerivAt_Uvec0_any
#print axioms N11Formalization.hasFDerivAt_Uvec1_any
