/-
  evidence/f1-step2/F1-BallD35-C2.lean
  ====================================

  **F1 第 2 步 · 件 C 的第二片（`C2`，**精简版**）** —— 按 Lead R247 裁决与**整库普查**重做。

  **为什么精简** ✗✓：`ResidualDerivJT.lean`（**已在根 cone**）**已含件 C 的前三层**：
  * 角层：`hasFDerivAt_angleVec_any`（L616）、`hasFDerivAt_thetaOf_any`（L733）；
  * `W` 层：`Wfun`（L607）、`dWfun`（L611）、`hasFDerivAt_Wfun`（L634）；
  * **ρ 层**：`drhoAt`（L652）、`hasFDerivAt_rhoK_any`（L656）、**`Eρ`（L687）+ `Eρ_eq`（L690）
    = 一般点标量读数**；
  * **arc 层**：`ArcC`（L719）、`phiA`（L722）、`phiCLM`（L726）、`hasFDerivAt_phiA`（L749）、
    **`fderiv_ArcC_zero/one`（L756/764）**。
  ⇒ 我上一版 `C2` 的 `hasFDerivAt_radicand_any` / `rhoCLMAt` / `hasFDerivAt_rhoK_any` /
  `fderiv_rhoK_any_single` **全部与根内同义** ⇒ **删**（**不重推已受审件** ✓）。

  **本件只留"根内没有的"** ✓✓：
  1. **`Eρ_eq_drhoReal`**：ρ 层**接合**——根内 `Eρ`（一般点标量读数）**就是**件 AB 的 `drhoReal`；
  2. **`fderiv_ArcC_zero_eq_arc0Real` / `fderiv_ArcC_one_eq_arc1Real`**：arc 层**接合**——
     根内 `fderiv_ArcC_zero/one` **就是**件 AB 的 `arc0Real`/`arc1Real`；
  3. **`hasFDerivAt_ringCenter0_any` / `hasFDerivAt_ringCenter1_any`**：**真缺口**（一般点的
     `ρ_k·cos θ_k` / `ρ_k·sin θ_k`；一行 = 根内 `hasFDerivAt_rhoK_any` × `hasFDerivAt_thetaOf_any.cos/.sin` ✓）；
  4. **`fderiv_ringCenter0_any_eq_ring0Real` / `fderiv_ringCenter1_any_eq_ring1Real`**：ring 层**接合**。

  **⇒ 全部是"桥"或"真缺口层"，零重推** ✓（我用整库普查核过：8 条与 `srcDir` 全部既有声明**无交集** ✓）。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.ResidualDerivJT
import N11Formalization.F1.BallD35Hrad

/-! ## 0. **外部名自查前言**（Lead R238 过程口径；逐条 `#check`） -/
#check @N11Formalization.Eρ
#check @N11Formalization.Eρ_eq
#check @N11Formalization.drhoAt
#check @N11Formalization.hasFDerivAt_rhoK_any
#check @N11Formalization.hasFDerivAt_thetaOf_any
#check @N11Formalization.Wfun
#check @N11Formalization.ArcC
#check @N11Formalization.fderiv_ArcC_zero
#check @N11Formalization.fderiv_ArcC_one
#check @N11Formalization.phiA
#check @N11Formalization.phiCLM
#check @N11Formalization.dthetaCLM_apply_single
#check @N11Formalization.daCLM_apply_single
#check @N11Formalization.drhoReal
#check @N11Formalization.ring0Real
#check @N11Formalization.ring1Real
#check @N11Formalization.arc0Real
#check @N11Formalization.arc1Real
#check @N11Formalization.pad12_six

noncomputable section

namespace N11Formalization

/-! ## 1. ρ 层接合：根内 `Eρ` ↔ 件 AB 的 `drhoReal` -/

/-- **一般点 ρ 标量读数（根内 `Eρ`）就是件 AB 的 `drhoReal`** ✓✓
（只差 `(x6)²`/`x6*x6`、`sin²`/`sin*sin`、`2 sin cos dA` 的括号写法，`ring` 级相等）。 -/
theorem Eρ_eq_drhoReal (k : Fin 9) (i : Fin 7) (x : Fin 7 → ℝ) :
    Eρ k i x = drhoReal (pad12 x) k i := by
  rw [Eρ_eq k i x, drhoReal, Wfun, pad12_six x, pow_two (x 6)]
  have h2 : (Real.sin (angleVec (pad12 x) k)) ^ 2
      = Real.sin (angleVec (pad12 x) k) * Real.sin (angleVec (pad12 x) k) := by ring
  rw [h2]
  ring

/-! ## 2. arc 层接合：根内 `fderiv_ArcC_zero/one` ↔ 件 AB 的 `arc0Real`/`arc1Real` -/

theorem fderiv_ArcC_zero_eq_arc0Real (k : Fin 9) (i : Fin 7) (z : Fin 7 → ℝ) :
    (fderiv ℝ (ArcC k 0) z) (Pi.single i 1) = arc0Real (pad12 z) k i := by
  rw [fderiv_ArcC_zero k z, arc0Real, phiA, phiCLM]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [dthetaCLM_apply_single k i, daCLM_apply_single k i]

theorem fderiv_ArcC_one_eq_arc1Real (k : Fin 9) (i : Fin 7) (z : Fin 7 → ℝ) :
    (fderiv ℝ (ArcC k 1) z) (Pi.single i 1) = arc1Real (pad12 z) k i := by
  rw [fderiv_ArcC_one k z, arc1Real, phiA, phiCLM]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [dthetaCLM_apply_single k i, daCLM_apply_single k i]

/-! ## 3. `ringCenter` 层（**真缺口**）：一般点的 `ρ_k·cos θ_k` / `ρ_k·sin θ_k` -/

theorem hasFDerivAt_ringCenter0_any (k : Fin 9) (z : Fin 7 → ℝ) (hW : Wfun k z ≠ 0) :
    HasFDerivAt
      (fun z' : Fin 7 → ℝ => rhoK (pad12 z') k * Real.cos (thetaOf (angleVec (pad12 z')) k))
      (rhoK (pad12 z) k • (-(Real.sin (thetaOf (angleVec (pad12 z)) k)) • dthetaCLM k)
        + Real.cos (thetaOf (angleVec (pad12 z)) k) • drhoAt k z) z :=
  (hasFDerivAt_rhoK_any k z hW).mul ((hasFDerivAt_thetaOf_any k z).cos)

theorem hasFDerivAt_ringCenter1_any (k : Fin 9) (z : Fin 7 → ℝ) (hW : Wfun k z ≠ 0) :
    HasFDerivAt
      (fun z' : Fin 7 → ℝ => rhoK (pad12 z') k * Real.sin (thetaOf (angleVec (pad12 z')) k))
      (rhoK (pad12 z) k • ((Real.cos (thetaOf (angleVec (pad12 z)) k)) • dthetaCLM k)
        + Real.sin (thetaOf (angleVec (pad12 z)) k) • drhoAt k z) z :=
  (hasFDerivAt_rhoK_any k z hW).mul ((hasFDerivAt_thetaOf_any k z).sin)

/-! ## 4. ring 层接合：真导数 ↔ 件 AB 的 `ring0Real`/`ring1Real` -/

theorem fderiv_ringCenter0_any_eq_ring0Real (k : Fin 9) (i : Fin 7) (z : Fin 7 → ℝ)
    (hW : Wfun k z ≠ 0) :
    (fderiv ℝ (fun z' : Fin 7 → ℝ =>
        rhoK (pad12 z') k * Real.cos (thetaOf (angleVec (pad12 z')) k)) z) (Pi.single i 1)
      = ring0Real (pad12 z) k i := by
  rw [(hasFDerivAt_ringCenter0_any k z hW).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [dthetaCLM_apply_single k i,
    show (drhoAt k z) (Pi.single i 1) = Eρ k i z from rfl, Eρ_eq_drhoReal k i z, ring0Real]

theorem fderiv_ringCenter1_any_eq_ring1Real (k : Fin 9) (i : Fin 7) (z : Fin 7 → ℝ)
    (hW : Wfun k z ≠ 0) :
    (fderiv ℝ (fun z' : Fin 7 → ℝ =>
        rhoK (pad12 z') k * Real.sin (thetaOf (angleVec (pad12 z')) k)) z) (Pi.single i 1)
      = ring1Real (pad12 z) k i := by
  rw [(hasFDerivAt_ringCenter1_any k z hW).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [dthetaCLM_apply_single k i,
    show (drhoAt k z) (Pi.single i 1) = Eρ k i z from rfl, Eρ_eq_drhoReal k i z, ring1Real]

end N11Formalization

#print axioms N11Formalization.Eρ_eq_drhoReal
#print axioms N11Formalization.fderiv_ArcC_zero_eq_arc0Real
#print axioms N11Formalization.fderiv_ArcC_one_eq_arc1Real
#print axioms N11Formalization.hasFDerivAt_ringCenter0_any
#print axioms N11Formalization.hasFDerivAt_ringCenter1_any
#print axioms N11Formalization.fderiv_ringCenter0_any_eq_ring0Real
#print axioms N11Formalization.fderiv_ringCenter1_any_eq_ring1Real

/-! ## 件 C 的剩余缺口（普查后，只剩两层）

`Uvec`（`C_k + C_{k+1} − B_k`，吃本件的 ring 层 + arc 层接合）、`hub0/hub1`/`wPoint`、
`dist` 链、`fderiv_residualComp` 的一般点版。
-/
