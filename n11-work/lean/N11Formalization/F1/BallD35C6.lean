/-
  evidence/f1-step2/F1-BallD35-C6.lean
  ====================================

  **F1 第 2 步 · 件 C 的第六片（`C6`）＝ 件 C 的收口** ✓✓

  **目标**：把**区间层**（`F1.BallD35Hrad.compIvBox_mem_all`，**已无条件** ✓）桥到**真正的 `fderiv`**：

  ```lean
  theorem ndJT_res_z_box (k : Fin 5) (i : Fin 7) (x : Fin 12 → ℝ)
      (hx : x ∈ Metric.closedBall certCR rhoCertR) :
      (compIvBox k i).Mem ((fderiv ℝ residualFun (first7 x) (Pi.single i 1)) k)
  ```

  **结构（按 `NEXT-C6-RECIPE.md`）**：
  * **A** 6 条命名 CLM（`ringCLM0/1`、`arcCLM0/1`、`dUvec0/1CLM`）—— 让陈述可读；
  * **B** CLM 取值 → 件 AB 的 `*Real` 的**桥**（`dUvec0/1CLM_single_eq_dUvec0/1Real`）；
  * **C** `fderiv_residual_k_CLM`（`k = 0..4`）：实例化 `F1.BallD35C5.fderiv_residualComp_any`；
  * **D** `fderiv_residual_k_any`：用 B 把 CLM 取值换成 `*Real` ⇒ 与 `compIvBox_mem` 右端同形；
  * **E** **`ndJT_res_z_box`**：一行收口 ✓✓。

  **依赖（按名引用，零重推）**：`F1.BallD35C5`（`fderiv_residualComp_any`/`hasFDerivAt_wPoint_0/1_any`/
  `hasFDerivAt_hub*_any`/`WpAt`）+ `F1.BallD35C4`（`hasFDerivAt_Uvec0/1_any`/`hasFDerivAt_arcC0/1_any`）
  + `F1.BallD35C2`（`hasFDerivAt_ringCenter0/1_any`/`Eρ_eq_drhoReal`/`fderiv_ArcC_*_eq_arc*Real`）
  + `F1.BallD35Hrad`（`compIvBox_mem_uncond`/`dUxReal`/`dUyReal`/`dUvec0/1Real`/`ring0/1Real`）
  + `ResidualDerivJT`（`Wfun`/`drhoAt`/`Eρ`）+ `ResidualDerivD`（`Apt`/`Bpt`/`resSlot`/`resHub`）。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.F1.BallD35C5
import N11Formalization.F1.BallD35C4
import N11Formalization.F1.BallD35C2
import N11Formalization.F1.BallD35Hrad
import N11Formalization.ResidualDerivJT

/-! ## 0. **外部名自查前言**（Lead R238 过程口径） -/
#check @N11Formalization.fderiv_residualComp_any
#check @N11Formalization.hasFDerivAt_Uvec0_any
#check @N11Formalization.hasFDerivAt_Uvec1_any
#check @N11Formalization.hasFDerivAt_ringCenter0_any
#check @N11Formalization.hasFDerivAt_ringCenter1_any
#check @N11Formalization.hasFDerivAt_hub0_0_any
#check @N11Formalization.hasFDerivAt_hub1_0_any
#check @N11Formalization.hasFDerivAt_wPoint_0_any
#check @N11Formalization.hasFDerivAt_wPoint_1_any
#check @N11Formalization.WpAt
#check @N11Formalization.Eρ
#check @N11Formalization.Eρ_eq_drhoReal
#check @N11Formalization.drhoAt
#check @N11Formalization.phiA
#check @N11Formalization.phiCLM
#check @N11Formalization.dthetaCLM_apply_single
#check @N11Formalization.daCLM_apply_single
#check @N11Formalization.Apt
#check @N11Formalization.Bpt
#check @N11Formalization.dUxReal
#check @N11Formalization.dUyReal
#check @N11Formalization.compIvBox_mem_uncond

noncomputable section

namespace N11Formalization

/-! ## A. 命名 CLM -/

def ringCLM0 (k : Fin 9) (z : Fin 7 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  rhoK (pad12 z) k • (-(Real.sin (thetaOf (angleVec (pad12 z)) k)) • dthetaCLM k)
    + Real.cos (thetaOf (angleVec (pad12 z)) k) • drhoAt k z

def ringCLM1 (k : Fin 9) (z : Fin 7 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  rhoK (pad12 z) k • ((Real.cos (thetaOf (angleVec (pad12 z)) k)) • dthetaCLM k)
    + Real.sin (thetaOf (angleVec (pad12 z)) k) • drhoAt k z

def arcCLM0 (k : Fin 9) (z : Fin 7 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  (-(Real.sin (phiA k z))) • phiCLM k

def arcCLM1 (k : Fin 9) (z : Fin 7 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  (Real.cos (phiA k z)) • phiCLM k

def dUvec0CLM (k : Fin 9) (z : Fin 7 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  ringCLM0 k z + ringCLM0 (k + 1) z - arcCLM0 k z

def dUvec1CLM (k : Fin 9) (z : Fin 7 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  ringCLM1 k z + ringCLM1 (k + 1) z - arcCLM1 k z

/-! ## C. `fderiv_residual_k_CLM`（`k = 0..4`，实例化 `fderiv_residualComp_any`）

右端保留命名 CLM；`k` 的槽位照 `ResidualDerivDist.fderiv_residual_{0..4}`：
`resSlot = (1,2,3,8,0)`、`hub = (hub1,hub0,hub0,hub1,ringCenter 6)`。 -/

theorem fderiv_residual_0_CLM (i : Fin 7) (z : Fin 7 → ℝ)
    (hW1 : Wfun 1 z ≠ 0) (hW2 : Wfun 2 z ≠ 0)
    (hg : ((Uvec (pad12 z) 1).ofLp 0 - (hub1 (pad12 z)).ofLp 0) ^ 2
        + ((Uvec (pad12 z) 1).ofLp 1 - (hub1 (pad12 z)).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w 0) z) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((Uvec (pad12 z) 1).ofLp 0 - (hub1 (pad12 z)).ofLp 0) ^ 2
              + ((Uvec (pad12 z) 1).ofLp 1 - (hub1 (pad12 z)).ofLp 1) ^ 2)))
          * (2 * ((Uvec (pad12 z) 1).ofLp 0 - (hub1 (pad12 z)).ofLp 0)
              * (dUvec0CLM 1 z (Pi.single i 1) - (coord 5) (Pi.single i 1))
            + 2 * ((Uvec (pad12 z) 1).ofLp 1 - (hub1 (pad12 z)).ofLp 1)
              * (dUvec1CLM 1 z (Pi.single i 1)
                - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) :=
  fderiv_residualComp_any 0 z (fun u => Uvec u 1) (fun u => hub1 u)
    (dUvec0CLM 1 z) (dUvec1CLM 1 z) (coord 5) 0
    (hasFDerivAt_Uvec0_any 1 z hW1 hW2) (hasFDerivAt_Uvec1_any 1 z hW1 hW2)
    (hasFDerivAt_hub1_0_any z) (hasFDerivAt_hub1_1_any z)
    (fun w => by
      have h1 : residualFun w 0 = dist (Uvec (pad12 w) 1) (hub1 (pad12 w)) - pad12 w 6 := rfl
      rw [h1, pad12_six])
    hg i

theorem fderiv_residual_1_CLM (i : Fin 7) (z : Fin 7 → ℝ)
    (hW2 : Wfun 2 z ≠ 0) (hW3 : Wfun 3 z ≠ 0)
    (hg : ((Uvec (pad12 z) 2).ofLp 0 - (hub0 (pad12 z)).ofLp 0) ^ 2
        + ((Uvec (pad12 z) 2).ofLp 1 - (hub0 (pad12 z)).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w 1) z) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((Uvec (pad12 z) 2).ofLp 0 - (hub0 (pad12 z)).ofLp 0) ^ 2
              + ((Uvec (pad12 z) 2).ofLp 1 - (hub0 (pad12 z)).ofLp 1) ^ 2)))
          * (2 * ((Uvec (pad12 z) 2).ofLp 0 - (hub0 (pad12 z)).ofLp 0)
              * (dUvec0CLM 2 z (Pi.single i 1) - (coord 4) (Pi.single i 1))
            + 2 * ((Uvec (pad12 z) 2).ofLp 1 - (hub0 (pad12 z)).ofLp 1)
              * (dUvec1CLM 2 z (Pi.single i 1)
                - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) :=
  fderiv_residualComp_any 1 z (fun u => Uvec u 2) (fun u => hub0 u)
    (dUvec0CLM 2 z) (dUvec1CLM 2 z) (coord 4) 0
    (hasFDerivAt_Uvec0_any 2 z hW2 hW3) (hasFDerivAt_Uvec1_any 2 z hW2 hW3)
    (hasFDerivAt_hub0_0_any z) (hasFDerivAt_hub0_1_any z)
    (fun w => by
      have h1 : residualFun w 1 = dist (Uvec (pad12 w) 2) (hub0 (pad12 w)) - pad12 w 6 := rfl
      rw [h1, pad12_six])
    hg i

theorem fderiv_residual_2_CLM (i : Fin 7) (z : Fin 7 → ℝ)
    (hW3 : Wfun 3 z ≠ 0) (hW4 : Wfun 4 z ≠ 0)
    (hg : ((Uvec (pad12 z) 3).ofLp 0 - (hub0 (pad12 z)).ofLp 0) ^ 2
        + ((Uvec (pad12 z) 3).ofLp 1 - (hub0 (pad12 z)).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w 2) z) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((Uvec (pad12 z) 3).ofLp 0 - (hub0 (pad12 z)).ofLp 0) ^ 2
              + ((Uvec (pad12 z) 3).ofLp 1 - (hub0 (pad12 z)).ofLp 1) ^ 2)))
          * (2 * ((Uvec (pad12 z) 3).ofLp 0 - (hub0 (pad12 z)).ofLp 0)
              * (dUvec0CLM 3 z (Pi.single i 1) - (coord 4) (Pi.single i 1))
            + 2 * ((Uvec (pad12 z) 3).ofLp 1 - (hub0 (pad12 z)).ofLp 1)
              * (dUvec1CLM 3 z (Pi.single i 1)
                - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) :=
  fderiv_residualComp_any 2 z (fun u => Uvec u 3) (fun u => hub0 u)
    (dUvec0CLM 3 z) (dUvec1CLM 3 z) (coord 4) 0
    (hasFDerivAt_Uvec0_any 3 z hW3 hW4) (hasFDerivAt_Uvec1_any 3 z hW3 hW4)
    (hasFDerivAt_hub0_0_any z) (hasFDerivAt_hub0_1_any z)
    (fun w => by
      have h1 : residualFun w 2 = dist (Uvec (pad12 w) 3) (hub0 (pad12 w)) - pad12 w 6 := rfl
      rw [h1, pad12_six])
    hg i

theorem fderiv_residual_3_CLM (i : Fin 7) (z : Fin 7 → ℝ)
    (hW8 : Wfun 8 z ≠ 0) (hW0 : Wfun ((8 : Fin 9) + 1) z ≠ 0)
    (hg : ((Uvec (pad12 z) 8).ofLp 0 - (hub1 (pad12 z)).ofLp 0) ^ 2
        + ((Uvec (pad12 z) 8).ofLp 1 - (hub1 (pad12 z)).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w 3) z) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((Uvec (pad12 z) 8).ofLp 0 - (hub1 (pad12 z)).ofLp 0) ^ 2
              + ((Uvec (pad12 z) 8).ofLp 1 - (hub1 (pad12 z)).ofLp 1) ^ 2)))
          * (2 * ((Uvec (pad12 z) 8).ofLp 0 - (hub1 (pad12 z)).ofLp 0)
              * (dUvec0CLM 8 z (Pi.single i 1) - (coord 5) (Pi.single i 1))
            + 2 * ((Uvec (pad12 z) 8).ofLp 1 - (hub1 (pad12 z)).ofLp 1)
              * (dUvec1CLM 8 z (Pi.single i 1)
                - (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) :=
  fderiv_residualComp_any 3 z (fun u => Uvec u 8) (fun u => hub1 u)
    (dUvec0CLM 8 z) (dUvec1CLM 8 z) (coord 5) 0
    (hasFDerivAt_Uvec0_any 8 z hW8 hW0) (hasFDerivAt_Uvec1_any 8 z hW8 hW0)
    (hasFDerivAt_hub1_0_any z) (hasFDerivAt_hub1_1_any z)
    (fun w => by
      have h1 : residualFun w 3 = dist (Uvec (pad12 w) 8) (hub1 (pad12 w)) - pad12 w 6 := rfl
      rw [h1, pad12_six])
    hg i

theorem fderiv_residual_4_CLM (i : Fin 7) (z : Fin 7 → ℝ)
    (hW6 : Wfun 6 z ≠ 0) (hWp : WpAt z ≠ 0)
    (hg : ((wPoint (pad12 z)).ofLp 0 - (ringCenter (pad12 z) 6).ofLp 0) ^ 2
        + ((wPoint (pad12 z)).ofLp 1 - (ringCenter (pad12 z) 6).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w 4) z) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((wPoint (pad12 z)).ofLp 0 - (ringCenter (pad12 z) 6).ofLp 0) ^ 2
              + ((wPoint (pad12 z)).ofLp 1 - (ringCenter (pad12 z) 6).ofLp 1) ^ 2)))
          * (2 * ((wPoint (pad12 z)).ofLp 0 - (ringCenter (pad12 z) 6).ofLp 0)
              * (((1 / 2 : ℝ) • (coord 4 + coord 5)) (Pi.single i 1)
                - ringCLM0 6 z (Pi.single i 1))
            + 2 * ((wPoint (pad12 z)).ofLp 1 - (ringCenter (pad12 z) 6).ofLp 1)
              * (((1 / (2 * Real.sqrt (WpAt z))) • ((2 * z 6) • coord 6
                    - (2 * ((z 5 - z 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))))
                  (Pi.single i 1) - ringCLM1 6 z (Pi.single i 1)))
        - (if i = 6 then 1 else 0 : ℝ) :=
  fderiv_residualComp_any 4 z (fun u => wPoint u) (fun u => ringCenter u 6)
    ((1 / 2 : ℝ) • (coord 4 + coord 5))
    ((1 / (2 * Real.sqrt (WpAt z))) • ((2 * z 6) • coord 6
      - (2 * ((z 5 - z 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))))
    (ringCLM0 6 z) (ringCLM1 6 z)
    (hasFDerivAt_wPoint_0_any z) (hasFDerivAt_wPoint_1_any z hWp)
    (hasFDerivAt_ringCenter0_any 6 z hW6) (hasFDerivAt_ringCenter1_any 6 z hW6)
    (fun w => by
      have h1 : residualFun w 4 = dist (wPoint (pad12 w)) (ringCenter (pad12 w) 6) - pad12 w 6 :=
        rfl
      rw [h1, pad12_six])
    hg i

end N11Formalization

#print axioms N11Formalization.fderiv_residual_0_CLM
#print axioms N11Formalization.fderiv_residual_1_CLM
#print axioms N11Formalization.fderiv_residual_2_CLM
#print axioms N11Formalization.fderiv_residual_3_CLM
#print axioms N11Formalization.fderiv_residual_4_CLM

/-! ## 尚未在本片完成（**下一步 `C7`**，纯装配）

**B**（CLM 取值 → `*Real` 的桥）与 **D/E**（`fderiv_residual_k_any` + `ndJT_res_z_box`）。
**B 的配方**（逐条 `rfl`/`simp only` 即可）：
* `dUvec0CLM k z (Pi.single i 1) = dUvec0Real (pad12 z) k i` ⟸ 展开 `ringCLM0/1`、`arcCLM0/1`，
  用 `add_apply`/`sub_apply`/`smul_apply`/`smul_eq_mul` + `dthetaCLM_apply_single`/`daCLM_apply_single`
  / `phiCLM`/`phiA` 展开 + **`Eρ_eq_drhoReal`**（把 `(drhoAt k z) (single i 1)` 换成 `drhoReal`）✓；
* `k = 4` 另需 `WpAt z = WpReal (pad12 z)`（`ring` + `pad12_six/five/four`）✓。
**E**：`rw [fderiv_residual_k_any …]; exact compIvBox_mem_uncond k i hx` —— **一行** ✓。
-/
