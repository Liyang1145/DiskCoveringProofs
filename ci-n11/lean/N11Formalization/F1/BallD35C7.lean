/-
  evidence/f1-step2/F1-BallD35-C7.lean
  ====================================

  **F1 第 2 步 · 件 C 的第七片（`C7`）＝ 件 C 的收口** ✓✓

  * `F1-BallD35C6`（**已接根**，`c27cc1d5f15cfabb`）已给出**五条一般点 `fderiv` 读数**（CLM 形式）；
  * **本片补 B/D/E**：**B** CLM 取值 → 件 AB 的 `*Real`；**D** `fderiv_residual_k_any`；**E** **收口**。

  **⇒ E 即 F1 球级 `hJ` 的那一段** ✓：
  `(compIvBox k i).Mem ((fderiv ℝ residualFun (first7 x) (Pi.single i 1)) k)`

  **前提口径**（照 Lead 裁决）：`hW`/`hWp`/`hg`（球上非退化）**未被本片证** ⇒ 结论**条件式** ✓；
  `hresid`（`residualFun` 在 `first7 x` 可微）用于把 `fderiv` 取分量。

  **本片修的两处（照 Lead 批准的正解）**：
  * **`k = 4`**：**不用 `simp only`**（它会把 `√((a−b)²+(c−d)²)` **展开**成 `√(a²−2ab+b²+…)` ⇒ 与目标不同形）
    ⇒ 改**显式 `rw [show … from rfl]`** 逐项对齐 ✓（形状残差用形状工具）；
  * **`fderiv_apply`**：本 mathlib 签名是
    `fderiv_apply h i : fderiv 𝕜 (fun x => Φ x i) x = ContinuousLinearMap.proj i ∘SL fderiv 𝕜 Φ x`
    ⇒ 先 `show (Φ v) k = (proj k ∘SL Φ) v from rfl`，再 `rw [← fderiv_apply h i]` ✓。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.F1.BallD35C6
import N11Formalization.F1.BallD35C2
import N11Formalization.F1.BallD35Hrad

/-! ## 0. **外部名自查前言**（Lead R238 过程口径） -/
#check @N11Formalization.dUvec0CLM
#check @N11Formalization.dUvec1CLM
#check @N11Formalization.ringCLM0
#check @N11Formalization.ringCLM1
#check @N11Formalization.fderiv_residual_0_CLM
#check @N11Formalization.fderiv_residual_4_CLM
#check @N11Formalization.dUvec0Real
#check @N11Formalization.dUvec1Real
#check @N11Formalization.ring0Real
#check @N11Formalization.ring1Real
#check @N11Formalization.dUxReal
#check @N11Formalization.dUyReal
#check @N11Formalization.WpReal
#check @N11Formalization.WpAt
#check @N11Formalization.Eρ
#check @N11Formalization.Eρ_eq_drhoReal
#check @N11Formalization.drhoReal
#check @N11Formalization.Apt
#check @N11Formalization.Bpt
#check @N11Formalization.compIvBox_mem_uncond

noncomputable section

namespace N11Formalization

/-! ## B. CLM 取值 → 件 AB 的 `*Real`（**桥**） -/

theorem dUvec0CLM_single_eq_dUvec0Real (k : Fin 9) (i : Fin 7) (z : Fin 7 → ℝ) :
    dUvec0CLM k z (Pi.single i 1) = dUvec0Real (pad12 z) k i := by
  have hk : (drhoAt k z) (Pi.single i 1) = drhoReal (pad12 z) k i := by
    rw [show (drhoAt k z) (Pi.single i 1) = Eρ k i z from rfl, Eρ_eq_drhoReal k i z]
  have hk1 : (drhoAt (k + 1) z) (Pi.single i 1) = drhoReal (pad12 z) (k + 1) i := by
    rw [show (drhoAt (k + 1) z) (Pi.single i 1) = Eρ (k + 1) i z from rfl,
      Eρ_eq_drhoReal (k + 1) i z]
  simp only [dUvec0CLM, dUvec0Real, ringCLM0, arcCLM0,
    ring0Real, arc0Real, phiCLM, phiA,
    dthetaCLM_apply_single, daCLM_apply_single,
    add_apply, sub_apply, smul_apply, smul_eq_mul, hk, hk1]

theorem dUvec1CLM_single_eq_dUvec1Real (k : Fin 9) (i : Fin 7) (z : Fin 7 → ℝ) :
    dUvec1CLM k z (Pi.single i 1) = dUvec1Real (pad12 z) k i := by
  have hk : (drhoAt k z) (Pi.single i 1) = drhoReal (pad12 z) k i := by
    rw [show (drhoAt k z) (Pi.single i 1) = Eρ k i z from rfl, Eρ_eq_drhoReal k i z]
  have hk1 : (drhoAt (k + 1) z) (Pi.single i 1) = drhoReal (pad12 z) (k + 1) i := by
    rw [show (drhoAt (k + 1) z) (Pi.single i 1) = Eρ (k + 1) i z from rfl,
      Eρ_eq_drhoReal (k + 1) i z]
  simp only [dUvec1CLM, dUvec1Real, ringCLM1, arcCLM1,
    ring1Real, arc1Real, phiCLM, phiA,
    dthetaCLM_apply_single, daCLM_apply_single,
    add_apply, sub_apply, smul_apply, smul_eq_mul, hk, hk1]

theorem ringCLM0_single_eq_ring0Real (i : Fin 7) (z : Fin 7 → ℝ) (_hW6 : Wfun 6 z ≠ 0) :
    ringCLM0 6 z (Pi.single i 1) = ring0Real (pad12 z) 6 i := by
  have h6 : (drhoAt 6 z) (Pi.single i 1) = drhoReal (pad12 z) 6 i := by
    rw [show (drhoAt 6 z) (Pi.single i 1) = Eρ 6 i z from rfl, Eρ_eq_drhoReal 6 i z]
  simp only [ringCLM0, ring0Real, add_apply, smul_apply, smul_eq_mul,
    dthetaCLM_apply_single, h6]

theorem ringCLM1_single_eq_ring1Real (i : Fin 7) (z : Fin 7 → ℝ) (_hW6 : Wfun 6 z ≠ 0) :
    ringCLM1 6 z (Pi.single i 1) = ring1Real (pad12 z) 6 i := by
  have h6 : (drhoAt 6 z) (Pi.single i 1) = drhoReal (pad12 z) 6 i := by
    rw [show (drhoAt 6 z) (Pi.single i 1) = Eρ 6 i z from rfl, Eρ_eq_drhoReal 6 i z]
  simp only [ringCLM1, ring1Real, add_apply, smul_apply, smul_eq_mul,
    dthetaCLM_apply_single, h6]

/-- `WpAt z = WpReal (pad12 z)`（`k = 4` 行用）。 -/
theorem WpAt_eq_WpReal (z : Fin 7 → ℝ) : WpAt z = WpReal (pad12 z) := by
  simp only [WpAt, WpReal, pad12_six z, pad12_five z, pad12_four z]

/-! ## D. `fderiv_residual_k_any`（`k = 0..4`，右端 = 件 AB 的 `*Real` 形态） -/

theorem fderiv_residual_k_any (k : Fin 5) (i : Fin 7) (z : Fin 7 → ℝ)
    (hW : ∀ j : Fin 9, Wfun j z ≠ 0) (hWp : WpAt z ≠ 0)
    (hg : ((Apt k (pad12 z)).ofLp 0 - (Bpt k (pad12 z)).ofLp 0) ^ 2
        + ((Apt k (pad12 z)).ofLp 1 - (Bpt k (pad12 z)).ofLp 1) ^ 2 ≠ 0) :
    (fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w k) z) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (((Apt k (pad12 z)).ofLp 0 - (Bpt k (pad12 z)).ofLp 0) ^ 2
              + ((Apt k (pad12 z)).ofLp 1 - (Bpt k (pad12 z)).ofLp 1) ^ 2)))
          * (2 * ((Apt k (pad12 z)).ofLp 0 - (Bpt k (pad12 z)).ofLp 0)
              * dUxReal k i (pad12 z)
            + 2 * ((Apt k (pad12 z)).ofLp 1 - (Bpt k (pad12 z)).ofLp 1)
              * dUyReal k i (pad12 z))
        - (if i = 6 then 1 else 0 : ℝ) := by
  match k with
  | 0 =>
    rw [fderiv_residual_0_CLM i z (hW 1) (hW 2) (by simpa only [Apt, Bpt] using hg)]
    simp only [Apt, Bpt, dUxReal, dUyReal, dUvec0CLM_single_eq_dUvec0Real,
      dUvec1CLM_single_eq_dUvec1Real]
  | 1 =>
    rw [fderiv_residual_1_CLM i z (hW 2) (hW 3) (by simpa only [Apt, Bpt] using hg)]
    simp only [Apt, Bpt, dUxReal, dUyReal, dUvec0CLM_single_eq_dUvec0Real,
      dUvec1CLM_single_eq_dUvec1Real]
  | 2 =>
    rw [fderiv_residual_2_CLM i z (hW 3) (hW 4) (by simpa only [Apt, Bpt] using hg)]
    simp only [Apt, Bpt, dUxReal, dUyReal, dUvec0CLM_single_eq_dUvec0Real,
      dUvec1CLM_single_eq_dUvec1Real]
  | 3 =>
    rw [fderiv_residual_3_CLM i z (hW 8) (hW ((8 : Fin 9) + 1)) (by simpa only [Apt, Bpt] using hg)]
    simp only [Apt, Bpt, dUxReal, dUyReal, dUvec0CLM_single_eq_dUvec0Real,
      dUvec1CLM_single_eq_dUvec1Real]
  | 4 =>
    -- **不用 `simp only`**（它会展开 `√` 的参数 ⇒ 与目标不同形）⇒ 逐项 `rw [show … from rfl]` 对齐
    rw [fderiv_residual_4_CLM i z (hW 6) hWp (by simpa only [Apt, Bpt] using hg)]
    rw [show (Apt 4 (pad12 z)) = wPoint (pad12 z) from rfl,
      show (Bpt 4 (pad12 z)) = ringCenter (pad12 z) 6 from rfl]
    rw [show dUxReal 4 i (pad12 z)
          = ((1 / 2 : ℝ) • (coord 4 + coord 5)) (Pi.single i 1) - ring0Real (pad12 z) 6 i
        from rfl,
      show dUyReal 4 i (pad12 z)
          = ((1 / (2 * Real.sqrt (WpReal (pad12 z)))) • ((2 * (pad12 z) 6) • coord 6
              - (2 * (((pad12 z) 5 - (pad12 z) 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))))
              (Pi.single i 1) - ring1Real (pad12 z) 6 i
        from rfl]
    rw [ringCLM0_single_eq_ring0Real i z (hW 6), ringCLM1_single_eq_ring1Real i z (hW 6),
      WpAt_eq_WpReal z, pad12_six z, pad12_five z, pad12_four z]

/-! ## E. **收口** ✓✓ -/

set_option maxHeartbeats 1000000 in
/-- **F1 第 2 步的收口**：球级 35 格对**真正的 `fderiv`** 的 `Mem`。

**参数口径**：以 `z : Fin 7 → ℝ`（`first7` 侧的点）为参数、球成员写作 `pad12 z ∈ closedBall`
——这样 `fderiv_residual_k_any` 的右端（`Apt k (pad12 z)`）与 `compIvBox_mem_uncond` 的右端
**逐字同形** ✓（`Apt`/`Bpt` 只经 `pad12 z` 取用）。

**条件式** ✓：`hW`/`hWp`/`hg`（球上非退化）**未被本片证**；`hresid` 用于取 `fderiv` 分量。 -/
theorem ndJT_res_z_box (k : Fin 5) (i : Fin 7) (z : Fin 7 → ℝ)
    (hz : pad12 z ∈ Metric.closedBall certCR rhoCertR)
    (hresid : DifferentiableAt ℝ residualFun z)
    (hW : ∀ j : Fin 9, Wfun j z ≠ 0) (hWp : WpAt z ≠ 0)
    (hg : ((Apt k (pad12 z)).ofLp 0 - (Bpt k (pad12 z)).ofLp 0) ^ 2
        + ((Apt k (pad12 z)).ofLp 1 - (Bpt k (pad12 z)).ofLp 1) ^ 2 ≠ 0) :
    (compIvBox k i).Mem ((fderiv ℝ residualFun z (Pi.single i 1)) k) := by
  have hcomp : (fderiv ℝ residualFun z (Pi.single i 1)) k
      = (fderiv ℝ (fun w : Fin 7 → ℝ => residualFun w k) z) (Pi.single i 1) := by
    rw [show (fderiv ℝ residualFun z (Pi.single i 1)) k
        = (ContinuousLinearMap.proj k ∘SL fderiv ℝ residualFun z) (Pi.single i 1) from rfl]
    rw [← fderiv_apply hresid k]
  rw [hcomp]
  rw [fderiv_residual_k_any k i z hW hWp hg]
  exact compIvBox_mem_uncond k i hz

end N11Formalization

#print axioms N11Formalization.dUvec0CLM_single_eq_dUvec0Real
#print axioms N11Formalization.dUvec1CLM_single_eq_dUvec1Real
#print axioms N11Formalization.ringCLM0_single_eq_ring0Real
#print axioms N11Formalization.ringCLM1_single_eq_ring1Real
#print axioms N11Formalization.WpAt_eq_WpReal
#print axioms N11Formalization.fderiv_residual_k_any
#print axioms N11Formalization.ndJT_res_z_box
