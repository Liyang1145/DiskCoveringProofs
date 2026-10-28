import N11Formalization.ResidualDerivJTHess

/-!
# `d2xIv` / `d2yIv`：`Δ` 的二阶区间族（+ `Mem`）—— **scratch 交付件**

**任务**（Lead 派发）：造 `d2xIv d2yIv : Fin 5 → Fin 7 → Fin 7 → RatInterval`
（= `ResidualDerivJTHess.hessIv` 的两个参数类型 ✓）并证出 `Mem`（= `∂²Δx_k/∂z_i∂z_j` 在盒心）。

**本件状态：** 见 `evidence/d2-leaves/REPORT.md` 的分层读数（层数 / 条件数 / 门读数）。

## 口径（逐条写死，供复核）

* **值形态**：全部结论在盒心 `u0 = first7 cCertR`；`secondPartial F u0 i j := ((fderiv ℝ (fun y => fderiv ℝ F y) u0)
  (Pi.single j 1)) (Pi.single i 1)`（`i` = 一阶方向、`j` = 二阶方向，与 `hessEntry` 同序）。
* **原始形态纪律**（照 `ResidualDerivJT.lean` §10 的冻结裁决）：`√` 侧一律**保留原始叶子形态**
  `(2√W)⁻¹`、`((2√W)·(2√W))⁻¹`，**不做** `1/(4W^{3/2})` 归一化（那需要 `√W·√W = W` 的
  `√`-内部改写，`jt-build` 已付 5 次失败代价）；归一化推给消费侧。
* **零公理/零 sorry/native_decide**：全部结论 kernel 证明。
* **未消前提**：只有"有限有理不等式"型前缀（`0 < (WkIv j).lo`、`0 < WpIv.lo`），
  与 `ResidualDerivD.hD_0..hD_4` **完全相同**的两批（一阶层已付）。
* **不重定义**：`Wk`/`Wfun`/`dWfun`/`drhoCLM`/`WkD1`/`dring0CLM`/`dring1CLM`/`darc0CLM`/`darc1CLM`/`Wp`
  /`arc2`/`mem_arc2`/`secondPartial_*`/`hasFDerivAt_fderiv_{add,sub,mul_scalar,comp_scalar}`
  /`hasDerivAt_deriv_sqrt` 一律**只读复用**（逐名 `#check` 过，见 `evidence/d2-leaves/scratch/Probe1.lean`）。
-/

noncomputable section

namespace N11Formalization

open RatInterval

-- `d2xIv_mem` 在 `k = 4` 支不用 `hWp`（`d2yIv_mem` 用）；为保持两族前提**同一形状**，此处关掉该 linter。
set_option linter.unusedVariables false

/-! ## 0. `W_k` 的二阶：`radicand (z₆)² − sin²a_k`（`daCLM` 一侧）

本节的形态**逐字取自** `evidence/jt-build/Leaf2Wire.lean`（在飞件、未过门）的 (a) 段，
本件把它**编译过门** ⇒ 该段从此有 kernel 读数。 -/

/-- `W_k` 的二阶 CLM（`∂²W_k = 2δ_{i6}δ_{j6} − 2(cos²a_k − sin²a_k)α_iα_j` 的 CLM 形态）。 -/
def L2Wfun (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.toSpanSingleton ℝ (coord 6)).comp ((2 : ℝ) • coord 6))
    - ((2 * Real.sin (angleVec (pad12 u0) k))
        • ((ContinuousLinearMap.toSpanSingleton ℝ (daCLM k)).comp
            ((-(Real.sin (angleVec (pad12 u0) k))) • daCLM k))
      + (((2 : ℝ) • ((Real.cos (angleVec (pad12 u0) k)) • daCLM k)).smulRight
          ((Real.cos (angleVec (pad12 u0) k)) • daCLM k)))

theorem hasFDerivAt_fderiv_Wfun (k : Fin 9) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (Wfun k) z) (L2Wfun k) u0 := by
  have he : (fun z : Fin 7 → ℝ => fderiv ℝ (Wfun k) z) = dWfun k := by
    funext z
    exact (hasFDerivAt_Wfun k z).fderiv
  rw [he, L2Wfun]
  have hA : HasFDerivAt (fun z : Fin 7 → ℝ => (2 * z 6) • coord 6)
      ((ContinuousLinearMap.toSpanSingleton ℝ (coord 6)).comp ((2 : ℝ) • coord 6)) u0 := by
    have h2 : HasFDerivAt (fun z : Fin 7 → ℝ => 2 * z 6) ((2 : ℝ) • coord 6) u0 :=
      (ContinuousLinearMap.hasFDerivAt (f := (2 : ℝ) • coord 6) (x := u0)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => by rfl)
    exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (coord 6))
      (x := 2 * u0 6)).comp u0 h2
  have hBd : HasFDerivAt
      (fun z : Fin 7 → ℝ => (Real.cos (angleVec (pad12 z) k)) • daCLM k)
      ((ContinuousLinearMap.toSpanSingleton ℝ (daCLM k)).comp
        ((-(Real.sin (angleVec (pad12 u0) k))) • daCLM k)) u0 := by
    have hc : HasFDerivAt (fun z : Fin 7 → ℝ => Real.cos (angleVec (pad12 z) k))
        ((-(Real.sin (angleVec (pad12 u0) k))) • daCLM k) u0 :=
      (hasFDerivAt_angleVec_any k u0).cos
    exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (daCLM k))
      (x := Real.cos (angleVec (pad12 u0) k))).comp u0 hc
  have hs : HasFDerivAt (fun z : Fin 7 → ℝ => 2 * Real.sin (angleVec (pad12 z) k))
      ((2 : ℝ) • ((Real.cos (angleVec (pad12 u0) k)) • daCLM k)) u0 :=
    ((hasFDerivAt_angleVec_any k u0).sin).const_mul (2 : ℝ)
  have hB : HasFDerivAt
      (fun z : Fin 7 → ℝ => (2 * Real.sin (angleVec (pad12 z) k))
        • ((Real.cos (angleVec (pad12 z) k)) • daCLM k))
      ((2 * Real.sin (angleVec (pad12 u0) k))
          • ((ContinuousLinearMap.toSpanSingleton ℝ (daCLM k)).comp
              ((-(Real.sin (angleVec (pad12 u0) k))) • daCLM k))
        + (((2 : ℝ) • ((Real.cos (angleVec (pad12 u0) k)) • daCLM k)).smulRight
            ((Real.cos (angleVec (pad12 u0) k)) • daCLM k))) u0 :=
    hs.smul hBd
  exact hA.sub hB

/-- `∂²W_k/∂z_i∂z_j` 的**规范实数形态**（`= jt-build` 的 `WkD2` 经 `cos 2a = cos²a − sin²a`
的等价写法；本件选 `cos²−sin²` 形态，故区间侧只需 `sub (sq cosAIv) (sq sinAIv)`，**不需**倍角恒等式）。 -/
def W2R (k : Fin 9) (i j : Fin 7) : ℝ :=
  2 * (if i = 6 then 1 else 0) * (if j = 6 then 1 else 0)
    - 2 * (Real.cos (angleVec (pad12 u0) k) ^ 2 - Real.sin (angleVec (pad12 u0) k) ^ 2)
        * (dAngle k i : ℝ) * (dAngle k j : ℝ)

/-- **`∂²W_k` 的取值形态**（区间侧的实数靶）。 -/
theorem Wfun2_single (k : Fin 9) (i j : Fin 7) :
    (L2Wfun k (Pi.single j 1)) (Pi.single i 1) = W2R k i j := by
  rw [W2R, L2Wfun]
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, coord_six_apply_single, daCLM_apply_single]
  ring

/-- `dWfun` 沿 `Pi.single i 1` 的取值（= `∂W_k/∂z_i` 的原始形态）。 -/
theorem dWfun_single (k : Fin 9) (i : Fin 7) :
    (dWfun k u0) (Pi.single i 1)
      = 2 * u0 6 * (if i = 6 then 1 else 0)
        - 2 * Real.sin (angleVec (pad12 u0) k)
            * ((Real.cos (angleVec (pad12 u0) k)) * (dAngle k i : ℝ)) := by
  simp only [dWfun, sub_apply, smul_apply, smul_eq_mul, coord_six_apply_single,
    daCLM_apply_single]

/-! ## 1. `√W_k` 的二阶（`T2` = `hasFDerivAt_fderiv_comp_scalar` 的实例化；形态照 `Leaf2Wire` (c)） -/

/-- `√ ∘ W_k` 的二阶 CLM（**原始形态**，不归一化）。 -/
def L2SqrtW (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (deriv Real.sqrt (Wfun k u0)) • (L2Wfun k)
    + (((fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (Wfun k u0)).comp (dWfun k u0)).smulRight
        (dWfun k u0))

theorem hasFDerivAt_fderiv_sqrtW (k : Fin 9) (hW : 0 < Wfun k u0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => Real.sqrt (Wfun k z)) z)
      (L2SqrtW k) u0 := by
  rw [L2SqrtW]
  refine hasFDerivAt_fderiv_comp_scalar (g := Wfun k) (u := Real.sqrt)
    (hasFDerivAt_Wfun k u0) (hasFDerivAt_fderiv_Wfun k) ?_ ?_ ?_
  · have h0 := (hasDerivAt_deriv_sqrt hW).hasFDerivAt
    have h1 : HasFDerivAt (fun t : ℝ => deriv Real.sqrt t)
        (fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (Wfun k u0)) (Wfun k u0) := by
      rw [h0.fderiv]
      exact h0
    exact h1
  · exact Filter.Eventually.of_forall fun z => (hasFDerivAt_Wfun k z).differentiableAt
  · filter_upwards [(hasFDerivAt_Wfun k u0).continuousAt.eventually
      (eventually_gt_nhds hW)] with z hz
    exact (Real.hasDerivAt_sqrt (ne_of_gt hz)).differentiableAt

/-- `ℝ →L ℝ` 的取值 = `v * g 1`（把 `fderiv` 的标量取值降到 `deriv`）。 -/
theorem d2_fderivReal_apply_eq_mul_one (g : ℝ →L[ℝ] ℝ) (v : ℝ) : g v = v * g 1 := by
  have h := ContinuousLinearMap.map_smul g v (1 : ℝ)
  simpa [smul_eq_mul] using h

/-- **`∂²(√W_k)` 的取值形态**（`deriv`/`fderiv` 全部显式化；区间侧的实数靶）。 -/
theorem sqrtW2_single (k : Fin 9) (i j : Fin 7) (hW : 0 < Wfun k u0) :
    (L2SqrtW k (Pi.single j 1)) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (Wfun k u0))) * (W2R k i j)
        + ((-2) * (1 / (2 * Real.sqrt (Wfun k u0))))
            * ((2 * Real.sqrt (Wfun k u0)) * (2 * Real.sqrt (Wfun k u0)))⁻¹
            * (2 * u0 6 * (if j = 6 then 1 else 0)
                - 2 * Real.sin (angleVec (pad12 u0) k)
                    * ((Real.cos (angleVec (pad12 u0) k)) * (dAngle k j : ℝ)))
            * (2 * u0 6 * (if i = 6 then 1 else 0)
                - 2 * Real.sin (angleVec (pad12 u0) k)
                    * ((Real.cos (angleVec (pad12 u0) k)) * (dAngle k i : ℝ))) := by
  rw [L2SqrtW]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [d2_fderivReal_apply_eq_mul_one, fderiv_apply_one_eq_deriv]
  rw [HasDerivAt.deriv (Real.hasDerivAt_sqrt (ne_of_gt hW))]
  rw [HasDerivAt.deriv (hasDerivAt_deriv_sqrt hW)]
  rw [Wfun2_single k i j, dWfun_single k j, dWfun_single k i]
  ring

/-! ## 2. `cos a_k`（`daCLM` 系数）与 `cos/sin θ_k`（`dthetaCLM` 系数）的二阶

模板 = `secondPartial_ArcC` 的两支（`phiA`/`phiCLM` → `angleVec`/`daCLM` 与 `thetaOf`/`dthetaCLM`），
**系数**分别为 `α_{k,·} = dAngle`（本节的 `A` 族）与 `β_{k,·} = dTheta`（`θ` 族）。 -/

/-- `∂²(cos a_k)` 的 CLM。 -/
def L2CosA (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ (daCLM k)).comp
    (-(Real.cos (angleVec (pad12 u0) k) • daCLM k))

theorem hasFDerivAt_fderiv_cosA (k : Fin 9) :
    HasFDerivAt (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.cos (angleVec (pad12 z) k)) y) (L2CosA k) u0 := by
  have h1 : (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.cos (angleVec (pad12 z) k)) y)
      = fun y : Fin 7 → ℝ => (-(Real.sin (angleVec (pad12 y) k))) • daCLM k := by
    funext y
    exact ((hasFDerivAt_angleVec_any k y).cos).fderiv
  rw [h1, L2CosA]
  have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (daCLM k))
    (x := -(Real.sin (angleVec (pad12 u0) k)))).comp u0 ((hasFDerivAt_angleVec_any k u0).sin.neg)
  have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (daCLM k)) ∘
        (-(fun x : Fin 7 → ℝ => Real.sin (angleVec (pad12 x) k))))
      = fun y : Fin 7 → ℝ => (-(Real.sin (angleVec (pad12 y) k))) • daCLM k := by
    funext y
    rw [Function.comp_apply, Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [he] at h
  exact h

/-- **`∂²(cos a_k)` 的取值形态**。 -/
theorem cosA2_single (k : Fin 9) (i j : Fin 7) :
    (L2CosA k (Pi.single j 1)) (Pi.single i 1)
      = -(Real.cos (angleVec (pad12 u0) k)) * (dAngle k i : ℝ) * (dAngle k j : ℝ) := by
  rw [L2CosA]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, neg_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, daCLM_apply_single]
  ring

/-- `∂²(cos θ_k)` 的 CLM（系数 = `dTheta`）。 -/
def L2CosTheta (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k)).comp
    (-(Real.cos (thetaOf (angleVec (pad12 u0)) k) • dthetaCLM k))

/-- `∂²(sin θ_k)` 的 CLM。 -/
def L2SinTheta (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k)).comp
    ((-(Real.sin (thetaOf (angleVec (pad12 u0)) k))) • dthetaCLM k)

theorem hasFDerivAt_fderiv_cosTheta (k : Fin 9) :
    HasFDerivAt (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 z)) k)) y)
      (L2CosTheta k) u0 := by
  have h1 : (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 z)) k)) y)
      = fun y : Fin 7 → ℝ => (-(Real.sin (thetaOf (angleVec (pad12 y)) k))) • dthetaCLM k := by
    funext y
    exact ((hasFDerivAt_thetaOf_any k y).cos).fderiv
  rw [h1, L2CosTheta]
  have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k))
    (x := -(Real.sin (thetaOf (angleVec (pad12 u0)) k)))).comp u0
    ((hasFDerivAt_thetaOf_any k u0).sin.neg)
  have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k)) ∘
        (-(fun x : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 x)) k))))
      = fun y : Fin 7 → ℝ => (-(Real.sin (thetaOf (angleVec (pad12 y)) k))) • dthetaCLM k := by
    funext y
    rw [Function.comp_apply, Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [he] at h
  exact h

theorem hasFDerivAt_fderiv_sinTheta (k : Fin 9) :
    HasFDerivAt (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 z)) k)) y)
      (L2SinTheta k) u0 := by
  have h1 : (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 z)) k)) y)
      = fun y : Fin 7 → ℝ => (Real.cos (thetaOf (angleVec (pad12 y)) k)) • dthetaCLM k := by
    funext y
    exact ((hasFDerivAt_thetaOf_any k y).sin).fderiv
  rw [h1, L2SinTheta]
  have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k))
    (x := Real.cos (thetaOf (angleVec (pad12 u0)) k))).comp u0
    ((hasFDerivAt_thetaOf_any k u0).cos)
  have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k)) ∘
        (fun x : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 x)) k)))
      = fun y : Fin 7 → ℝ => (Real.cos (thetaOf (angleVec (pad12 y)) k)) • dthetaCLM k := by
    funext y
    rw [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [he] at h
  exact h

/-- **`∂²(cos θ_k)` 的取值形态**。 -/
theorem cosTheta2_single (k : Fin 9) (i j : Fin 7) :
    (L2CosTheta k (Pi.single j 1)) (Pi.single i 1)
      = -(Real.cos (thetaOf (angleVec (pad12 u0)) k))
          * (dTheta k i : ℝ) * (dTheta k j : ℝ) := by
  rw [L2CosTheta]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, neg_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, dthetaCLM_apply_single]
  ring

/-- **`∂²(sin θ_k)` 的取值形态**。 -/
theorem sinTheta2_single (k : Fin 9) (i j : Fin 7) :
    (L2SinTheta k (Pi.single j 1)) (Pi.single i 1)
      = -(Real.sin (thetaOf (angleVec (pad12 u0)) k))
          * (dTheta k i : ℝ) * (dTheta k j : ℝ) := by
  rw [L2SinTheta]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, dthetaCLM_apply_single]
  ring

/-! ## 3. `ρ_k = cos a_k − √W_k` 的二阶（T1b = `hasFDerivAt_fderiv_sub` 相减） -/

/-- `∂²ρ_k` 的 CLM。 -/
def L2Rho (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  L2CosA k - L2SqrtW k

/-- `ρ_k ∘ pad12 = cos a_k − √W_k`（T1b 的**函数形态**前提）。 -/
theorem rhoF_eq_cos_sub_sqrt (k : Fin 9) :
    (fun z : Fin 7 → ℝ => rhoK (pad12 z) k)
      = (fun z : Fin 7 → ℝ => Real.cos (angleVec (pad12 z) k) - Real.sqrt (Wfun k z)) := by
  funext z
  simp only [rhoK_eq, Wfun, pad12_six]

theorem hasFDerivAt_fderiv_rhoF (k : Fin 9) (hW : 0 < Wfun k u0) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) z)
      (L2Rho k) u0 := by
  have hfun : (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) z)
      = (fun z : Fin 7 → ℝ => fderiv ℝ
          (fun z : Fin 7 → ℝ => Real.cos (angleVec (pad12 z) k) - Real.sqrt (Wfun k z)) z) := by
    rw [rhoF_eq_cos_sub_sqrt]
  rw [hfun, L2Rho]
  refine hasFDerivAt_fderiv_sub (hasFDerivAt_fderiv_cosA k) (hasFDerivAt_fderiv_sqrtW k hW) ?_ ?_
  · exact Filter.Eventually.of_forall fun z =>
      ((hasFDerivAt_angleVec_any k z).cos).differentiableAt
  · filter_upwards [(hasFDerivAt_Wfun k u0).continuousAt.eventually
      (eventually_gt_nhds hW)] with z hz
    exact ((Real.hasDerivAt_sqrt (ne_of_gt hz)).differentiableAt.comp z
      (hasFDerivAt_Wfun k z).differentiableAt)

/-- `Wfun k u0 = Wk k`（两个 def 的**同一性**；`Wk` 是一阶层用的名字）。 -/
theorem Wfun_u0_eq_Wk (k : Fin 9) : Wfun k u0 = Wk k := rfl

/-- `∂ρ_k/∂z_i` 的**规范实数形态**（`= drhoCLM k (Pi.single i 1)` 的显式化）。 -/
def rho1R (k : Fin 9) (i : Fin 7) : ℝ :=
  -(Real.sin (angleVec (pad12 u0) k)) * (dAngle k i : ℝ)
    - (1 / (2 * Real.sqrt (Wfun k u0))) * (WkD1 k i)

/-- `∂²ρ_k/∂z_i∂z_j` 的**规范实数形态**（**原始未归一化**：`√` 侧保留 `((2√W)·(2√W))⁻¹`）。 -/
def rho2R (k : Fin 9) (i j : Fin 7) : ℝ :=
  -(Real.cos (angleVec (pad12 u0) k) * (dAngle k i : ℝ) * (dAngle k j : ℝ))
    - (1 / (2 * Real.sqrt (Wfun k u0))) * (W2R k i j)
    - ((-2) * (1 / (2 * Real.sqrt (Wfun k u0))))
        * ((2 * Real.sqrt (Wfun k u0)) * (2 * Real.sqrt (Wfun k u0)))⁻¹
        * (WkD1 k j * WkD1 k i)

/-- **`∂²ρ_k` 的取值形态**（区间侧 `rho2Iv` 的实数靶）。 -/
theorem rho2_single (k : Fin 9) (i j : Fin 7) (hW : 0 < Wfun k u0) :
    (L2Rho k (Pi.single j 1)) (Pi.single i 1) = rho2R k i j := by
  rw [L2Rho, sub_apply, sub_apply, cosA2_single k i j, sqrtW2_single k i j hW]
  unfold rho2R W2R WkD1
  ring

/-- `drhoCLM k (Pi.single i 1)` = 规范形态 `rho1R k i`（下游 `ring2` 的桥）。 -/
theorem drhoCLM_single_eq_rho1R (k : Fin 9) (i : Fin 7) :
    (drhoCLM k) (Pi.single i 1) = rho1R k i := by
  rw [drhoCLM_single k i, ← Wfun_u0_eq_Wk k]
  unfold rho1R WkD1
  ring

/-! ## 4. `C_k` 的分量二阶（T3 = `hasFDerivAt_fderiv_mul_scalar`；形态照 `HESS-SPEC` L2） -/

/-- `∂²(C_{k,x})` 的 CLM。 -/
def L2RingC0 (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (rhoK (pad12 u0) k • L2CosTheta k
      + (drhoCLM k).smulRight ((-(Real.sin (thetaOf (angleVec (pad12 u0)) k))) • dthetaCLM k))
    + (Real.cos (thetaOf (angleVec (pad12 u0)) k) • L2Rho k
      + ((-(Real.sin (thetaOf (angleVec (pad12 u0)) k))) • dthetaCLM k).smulRight (drhoCLM k))

/-- `∂²(C_{k,y})` 的 CLM。 -/
def L2RingC1 (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (rhoK (pad12 u0) k • L2SinTheta k
      + (drhoCLM k).smulRight ((Real.cos (thetaOf (angleVec (pad12 u0)) k)) • dthetaCLM k))
    + (Real.sin (thetaOf (angleVec (pad12 u0)) k) • L2Rho k
      + ((Real.cos (thetaOf (angleVec (pad12 u0)) k)) • dthetaCLM k).smulRight (drhoCLM k))

theorem hasFDerivAt_fderiv_ringC0 (k : Fin 9) (hW : 0 < Wfun k u0) :
    HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0) z) (L2RingC0 k) u0 := by
  have hφ : HasFDerivAt (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) (drhoCLM k) u0 :=
    hasFDerivAt_rhoK' k (ne_of_gt hW)
  have hψ : HasFDerivAt (fun z : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 z)) k))
      ((-(Real.sin (thetaOf (angleVec (pad12 u0)) k))) • dthetaCLM k) u0 :=
    (hasFDerivAt_thetaOf k).cos
  have hφd : ∀ᶠ z in nhds u0,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) z := by
    filter_upwards [(hasFDerivAt_Wfun k u0).continuousAt.eventually
      (eventually_gt_nhds hW)] with z hz
    exact (hasFDerivAt_rhoK_any k z (ne_of_gt hz)).differentiableAt
  have hψd : ∀ᶠ z in nhds u0,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 z)) k)) z :=
    Filter.Eventually.of_forall fun z => ((hasFDerivAt_thetaOf_any k z).cos).differentiableAt
  have h := hasFDerivAt_fderiv_mul_scalar hφ (hasFDerivAt_fderiv_rhoF k hW) hψ
    (hasFDerivAt_fderiv_cosTheta k) hφd hψd
  have hfun : (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0)
      = (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.cos (thetaOf (angleVec (pad12 z)) k)) := by
    funext z
    rw [ringCenter_coord0]
  have hfun2 : (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0) z)
      = (fun z : Fin 7 → ℝ => fderiv ℝ
          (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.cos (thetaOf (angleVec (pad12 z)) k)) z) := by
    rw [hfun]
  rw [hfun2, L2RingC0]
  exact h

theorem hasFDerivAt_fderiv_ringC1 (k : Fin 9) (hW : 0 < Wfun k u0) :
    HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1) z) (L2RingC1 k) u0 := by
  have hφ : HasFDerivAt (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) (drhoCLM k) u0 :=
    hasFDerivAt_rhoK' k (ne_of_gt hW)
  have hψ : HasFDerivAt (fun z : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 z)) k))
      ((Real.cos (thetaOf (angleVec (pad12 u0)) k)) • dthetaCLM k) u0 :=
    (hasFDerivAt_thetaOf k).sin
  have hφd : ∀ᶠ z in nhds u0,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) z := by
    filter_upwards [(hasFDerivAt_Wfun k u0).continuousAt.eventually
      (eventually_gt_nhds hW)] with z hz
    exact (hasFDerivAt_rhoK_any k z (ne_of_gt hz)).differentiableAt
  have hψd : ∀ᶠ z in nhds u0,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 z)) k)) z :=
    Filter.Eventually.of_forall fun z => ((hasFDerivAt_thetaOf_any k z).sin).differentiableAt
  have h := hasFDerivAt_fderiv_mul_scalar hφ (hasFDerivAt_fderiv_rhoF k hW) hψ
    (hasFDerivAt_fderiv_sinTheta k) hφd hψd
  have hfun : (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1)
      = (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.sin (thetaOf (angleVec (pad12 z)) k)) := by
    funext z
    rw [ringCenter_coord1]
  have hfun2 : (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1) z)
      = (fun z : Fin 7 → ℝ => fderiv ℝ
          (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.sin (thetaOf (angleVec (pad12 z)) k)) z) := by
    rw [hfun]
  rw [hfun2, L2RingC1]
  exact h

/-- **`∂²(C_{k,x})` 的取值形态**（`HESS-SPEC` L2 的 `C_{k,x,ij}`）。 -/
theorem ringC0_2_single (k : Fin 9) (i j : Fin 7) (hW : 0 < Wfun k u0) :
    (L2RingC0 k (Pi.single j 1)) (Pi.single i 1)
      = rho2R k i j * Real.cos (thetaOf (angleVec (pad12 u0)) k)
        - rho1R k i * Real.sin (thetaOf (angleVec (pad12 u0)) k) * (dTheta k j : ℝ)
        - rho1R k j * Real.sin (thetaOf (angleVec (pad12 u0)) k) * (dTheta k i : ℝ)
        - rhoK (pad12 u0) k * Real.cos (thetaOf (angleVec (pad12 u0)) k)
            * (dTheta k i : ℝ) * (dTheta k j : ℝ) := by
  rw [L2RingC0]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    dthetaCLM_apply_single]
  rw [cosTheta2_single k i j, rho2_single k i j hW,
    drhoCLM_single_eq_rho1R k i, drhoCLM_single_eq_rho1R k j]
  ring

/-- **`∂²(C_{k,y})` 的取值形态**（`HESS-SPEC` L2 的 `C_{k,y,ij}`）。 -/
theorem ringC1_2_single (k : Fin 9) (i j : Fin 7) (hW : 0 < Wfun k u0) :
    (L2RingC1 k (Pi.single j 1)) (Pi.single i 1)
      = rho2R k i j * Real.sin (thetaOf (angleVec (pad12 u0)) k)
        + rho1R k i * Real.cos (thetaOf (angleVec (pad12 u0)) k) * (dTheta k j : ℝ)
        + rho1R k j * Real.cos (thetaOf (angleVec (pad12 u0)) k) * (dTheta k i : ℝ)
        - rhoK (pad12 u0) k * Real.sin (thetaOf (angleVec (pad12 u0)) k)
            * (dTheta k i : ℝ) * (dTheta k j : ℝ) := by
  rw [L2RingC1]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    dthetaCLM_apply_single]
  rw [sinTheta2_single k i j, rho2_single k i j hW,
    drhoCLM_single_eq_rho1R k i, drhoCLM_single_eq_rho1R k j]
  ring

/-! ## 5. `wPoint` 的两个分量：`x` 仿射（二阶 0）、`y = √Wp`（T2 + `HESS-SPEC` L6） -/

/-- `wPoint` 纵坐标的 radicand（**任意点**）：`Wp(z) = (z₆)² − ((z₅−z₄)/2)²`。 -/
def Wpf : (Fin 7 → ℝ) → ℝ := fun z => (z 6) ^ 2 - ((z 5 - z 4) / 2) ^ 2

theorem Wpf_u0 : Wpf u0 = Wp := rfl

/-- `Wpf` 在任意点的导数 CLM。 -/
def dWpfAt (z : Fin 7 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  (2 * z 6) • coord 6 - (2 * ((z 5 - z 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))

theorem hasFDerivAt_Wpf_any (z : Fin 7 → ℝ) : HasFDerivAt Wpf (dWpfAt z) z := by
  rw [dWpfAt]
  have h6 : HasFDerivAt (fun z : Fin 7 → ℝ => z 6) (coord 6) z :=
    ContinuousLinearMap.hasFDerivAt (f := coord 6) (x := z)
  have h6sq : HasFDerivAt (fun z : Fin 7 → ℝ => (z 6) ^ 2) ((2 * z 6) • coord 6) z := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using h6.pow 2
  have h54 : HasFDerivAt (fun z : Fin 7 → ℝ => z 5 - z 4) (coord 5 - coord 4) z :=
    (ContinuousLinearMap.hasFDerivAt (f := coord 5) (x := z)).sub
      (ContinuousLinearMap.hasFDerivAt (f := coord 4) (x := z))
  have hhalf : HasFDerivAt (fun z : Fin 7 → ℝ => (z 5 - z 4) / 2)
      ((1 / 2 : ℝ) • (coord 5 - coord 4)) z := by
    have he : (fun z : Fin 7 → ℝ => (z 5 - z 4) / 2) = fun z => (1 / 2 : ℝ) * (z 5 - z 4) := by
      funext z
      ring
    rw [he]
    exact h54.const_mul (1 / 2)
  have hhalf2 : HasFDerivAt (fun z : Fin 7 → ℝ => ((z 5 - z 4) / 2) ^ 2)
      ((2 * ((z 5 - z 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4))) z := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using hhalf.pow 2
  exact h6sq.sub hhalf2

/-- `Wpf` 的二阶 CLM。 -/
def L2Wpf : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.toSpanSingleton ℝ (coord 6)).comp ((2 : ℝ) • coord 6))
    - ((ContinuousLinearMap.toSpanSingleton ℝ ((1 / 2 : ℝ) • (coord 5 - coord 4))).comp
        ((2 : ℝ) • ((1 / 2 : ℝ) • (coord 5 - coord 4))))

theorem hasFDerivAt_fderiv_Wpf :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ Wpf z) (L2Wpf) u0 := by
  have he : (fun z : Fin 7 → ℝ => fderiv ℝ Wpf z) = dWpfAt := by
    funext z
    exact (hasFDerivAt_Wpf_any z).fderiv
  rw [he, L2Wpf]
  have hA : HasFDerivAt (fun z : Fin 7 → ℝ => (2 * z 6) • coord 6)
      ((ContinuousLinearMap.toSpanSingleton ℝ (coord 6)).comp ((2 : ℝ) • coord 6)) u0 := by
    have h2 : HasFDerivAt (fun z : Fin 7 → ℝ => 2 * z 6) ((2 : ℝ) • coord 6) u0 :=
      (ContinuousLinearMap.hasFDerivAt (f := (2 : ℝ) • coord 6) (x := u0)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => by rfl)
    exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (coord 6))
      (x := 2 * u0 6)).comp u0 h2
  have hm0 : HasFDerivAt (fun z : Fin 7 → ℝ => (z 5 - z 4) / 2)
      ((1 / 2 : ℝ) • (coord 5 - coord 4)) u0 := by
    have he2 : (fun z : Fin 7 → ℝ => (z 5 - z 4) / 2) = fun z => (1 / 2 : ℝ) * (z 5 - z 4) := by
      funext z
      ring
    rw [he2]
    exact ((ContinuousLinearMap.hasFDerivAt (f := coord 5) (x := u0)).sub
      (ContinuousLinearMap.hasFDerivAt (f := coord 4) (x := u0))).const_mul (1 / 2)
  have hm : HasFDerivAt (fun z : Fin 7 → ℝ => 2 * ((z 5 - z 4) / 2))
      ((2 : ℝ) • ((1 / 2 : ℝ) • (coord 5 - coord 4))) u0 := hm0.const_mul 2
  have hB : HasFDerivAt
      (fun z : Fin 7 → ℝ => (2 * ((z 5 - z 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))
      ((ContinuousLinearMap.toSpanSingleton ℝ ((1 / 2 : ℝ) • (coord 5 - coord 4))).comp
        ((2 : ℝ) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))) u0 :=
    (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.toSpanSingleton ℝ ((1 / 2 : ℝ) • (coord 5 - coord 4)))
      (x := 2 * ((u0 5 - u0 4) / 2))).comp u0 hm
  exact hA.sub hB

/-- `∂Wp/∂z_i` 的**规范实数形态**。 -/
def Wp1R (i : Fin 7) : ℝ :=
  2 * u0 6 * (if i = 6 then 1 else 0)
    - (2 * ((u0 5 - u0 4) / 2))
        * ((1 / 2 : ℝ) * ((if i = 5 then 1 else 0) - (if i = 4 then 1 else 0)))

/-- `∂²Wp/∂z_i∂z_j` 的**规范实数形态**。 -/
def Wp2R (i j : Fin 7) : ℝ :=
  2 * (if i = 6 then 1 else 0) * (if j = 6 then 1 else 0)
    - 2 * ((1 / 2 : ℝ) * ((if i = 5 then 1 else 0) - (if i = 4 then 1 else 0)))
        * ((1 / 2 : ℝ) * ((if j = 5 then 1 else 0) - (if j = 4 then 1 else 0)))

theorem dWpf_single (i : Fin 7) : (dWpfAt u0) (Pi.single i 1) = Wp1R i := by
  rw [dWpfAt, Wp1R]
  simp only [sub_apply, smul_apply, smul_eq_mul, coord_apply_single]

theorem Wpf2_single (i j : Fin 7) : (L2Wpf (Pi.single j 1)) (Pi.single i 1) = Wp2R i j := by
  rw [L2Wpf, Wp2R]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, coord_apply_single]
  ring

/-- `(wPoint (pad12 ·)).ofLp 1 = √(Wpf ·)`。 -/
theorem wpF_eq_sqrt :
    (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1) = fun z : Fin 7 → ℝ => Real.sqrt (Wpf z) := by
  funext z
  rw [wPoint_coord1, pad12_six, pad12_five, pad12_four, Wpf]

/-- `∂²(√Wp)` 的 CLM（原始形态）。 -/
def L2Wy : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (deriv Real.sqrt (Wpf u0)) • L2Wpf
    + (((fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (Wpf u0)).comp (dWpfAt u0)).smulRight
        (dWpfAt u0))

theorem hasFDerivAt_fderiv_wyF (hWp : 0 < Wpf u0) :
    HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1) z) (L2Wy) u0 := by
  rw [wpF_eq_sqrt, L2Wy]
  refine hasFDerivAt_fderiv_comp_scalar (g := Wpf) (u := Real.sqrt)
    (hasFDerivAt_Wpf_any u0) (hasFDerivAt_fderiv_Wpf) ?_ ?_ ?_
  · have h0 := (hasDerivAt_deriv_sqrt hWp).hasFDerivAt
    have h1 : HasFDerivAt (fun t : ℝ => deriv Real.sqrt t)
        (fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (Wpf u0)) (Wpf u0) := by
      rw [h0.fderiv]
      exact h0
    exact h1
  · exact Filter.Eventually.of_forall fun z => (hasFDerivAt_Wpf_any z).differentiableAt
  · filter_upwards [(hasFDerivAt_Wpf_any u0).continuousAt.eventually
      (eventually_gt_nhds hWp)] with z hz
    exact (Real.hasDerivAt_sqrt (ne_of_gt hz)).differentiableAt

/-- `∂²(wPoint.y)/∂z_i∂z_j` 的**规范实数形态**（原始未归一化）。 -/
def wy2R (i j : Fin 7) : ℝ :=
  (1 / (2 * Real.sqrt (Wpf u0))) * (Wp2R i j)
    + ((-2) * (1 / (2 * Real.sqrt (Wpf u0))))
        * ((2 * Real.sqrt (Wpf u0)) * (2 * Real.sqrt (Wpf u0)))⁻¹
        * (Wp1R j * Wp1R i)

theorem wy2_single (i j : Fin 7) (hWp : 0 < Wpf u0) :
    (L2Wy (Pi.single j 1)) (Pi.single i 1) = wy2R i j := by
  rw [L2Wy]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [d2_fderivReal_apply_eq_mul_one, fderiv_apply_one_eq_deriv]
  rw [HasDerivAt.deriv (Real.hasDerivAt_sqrt (ne_of_gt hWp))]
  rw [HasDerivAt.deriv (hasDerivAt_deriv_sqrt hWp)]
  rw [Wpf2_single i j, dWpf_single j, dWpf_single i]
  unfold wy2R Wp2R Wp1R
  ring

/-- `wPoint` 横坐标的二阶为 0（`(z₄+z₅)/2` 是 `coord` 的线性组合）。 -/
theorem secondPartial_wxF (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0) u0 i j = 0 := by
  have hclm : (fun z : Fin 7 → ℝ => ((1 / 2 : ℝ) • (coord 4 + coord 5)) z)
      = fun z : Fin 7 → ℝ => (1 / 2 : ℝ) * (z 4 + z 5) := by
    funext z
    rw [smul_apply, add_apply, smul_eq_mul]
    rfl
  have hfun : (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0)
      = fun z : Fin 7 → ℝ => (1 / 2 : ℝ) * (z 4 + z 5) := by
    funext z
    rw [wPoint_coord0, pad12_four, pad12_five]
    ring
  rw [hfun, ← hclm]
  exact secondPartial_clm ((1 / 2 : ℝ) • (coord 4 + coord 5)) u0 i j

/-! ## 6. 区间侧叶子（逐条镜像 §0–§5 的实数形态）

**端点来源纪律**：全部由 `ofRat`/`deltaIv`/`sinAIv`/`cosAIv`/`sinTIv`/`cosTIv`/`WkIv`/`rhoIv`/`drhoIv`
（= 一阶层 `D` 已用的同一批叶子）经 `add`/`sub`/`mul`/`neg`/`sq`/`sqrt`/`invPos` 组合 ⇒ **不含外部数值表常数**。 -/

/-- `0 < B.lo ⟹ 0 < (sq B).lo`（`sq` 的第一支取 `lo·lo`）。 -/
theorem sq_pos (B : RatInterval) (h : 0 < B.lo) : 0 < (sq B).lo := by
  unfold RatInterval.sq
  rw [if_pos (le_of_lt h)]
  exact mul_pos h h

/-- `0 < (WkIv j).lo ⟹ 0 < (twoSqrtWkIv j).lo`（照 `hD_0` 的内联写法具名化）。 -/
theorem twoSqrtWkIv_pos (j : Fin 9) (h : 0 < (WkIv j).lo) : 0 < (twoSqrtWkIv j).lo :=
  twoMulIv_pos (sqrtWkIv j) (sqrtLo_pos h) (valid_of_mem (sqrtWkIv_mem j))

/-- `∂W_k/∂z_i` 的区间（= `drhoIv` 的内层因子）。 -/
def WiIv (k : Fin 9) (i : Fin 7) : RatInterval :=
  sub (mul (ofRat (2 * cCert 6)) (deltaIv 6 i))
    (mul (mul (ofRat 2) (sinAIv k)) (mul (cosAIv k) (ofRat (dAngle k i))))

theorem WiIv_mem (k : Fin 9) (i : Fin 7) : (WiIv k i).Mem (WkD1 k i) := by
  have h1 : (mul (ofRat (2 * cCert 6)) (deltaIv 6 i)).Mem
      (2 * u0 6 * (if i = 6 then 1 else 0)) := by
    have h := mul_mem (ofRat_mem (2 * cCert 6)) (deltaIv_mem 6 i)
    have hc : (((2 * cCert 6 : ℚ)) : ℝ) = 2 * u0 6 := by
      rw [u0_six]
      push_cast
      rfl
    rwa [hc] at h
  have h2 : (mul (mul (ofRat 2) (sinAIv k)) (mul (cosAIv k) (ofRat (dAngle k i)))).Mem
      (2 * Real.sin (angleVec (pad12 u0) k) * Real.cos (angleVec (pad12 u0) k)
        * (dAngle k i : ℝ)) := by
    have h := mul_mem (mul_mem (ofRat_mem (2 : ℚ)) (sinAIv_mem k))
      (mul_mem (cosAIv_mem k) (ofRat_mem ((dAngle k i : ℤ) : ℚ)))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  rw [WkD1, WiIv]
  exact sub_mem h1 h2

/-- `cos(2a_k)` 的等价区间：`cos²a_k − sin²a_k`（避开倍角恒等式）。 -/
def cos2aIv (k : Fin 9) : RatInterval := sub (sq (cosAIv k)) (sq (sinAIv k))

theorem cos2aIv_mem (k : Fin 9) :
    (cos2aIv k).Mem
      (Real.cos (angleVec (pad12 u0) k) ^ 2 - Real.sin (angleVec (pad12 u0) k) ^ 2) := by
  rw [cos2aIv]
  exact sub_mem (sq_mem_pow (cosAIv_mem k)) (sq_mem_pow (sinAIv_mem k))

/-- `∂²W_k/∂z_i∂z_j` 的区间。 -/
def WijIv (k : Fin 9) (i j : Fin 7) : RatInterval :=
  sub (mul (ofRat 2) (mul (deltaIv 6 i) (deltaIv 6 j)))
    (mul (mul (ofRat 2) (cos2aIv k)) (ofRat (dAngle k i * dAngle k j)))

theorem WijIv_mem (k : Fin 9) (i j : Fin 7) : (WijIv k i j).Mem (W2R k i j) := by
  have h1 : (mul (ofRat 2) (mul (deltaIv 6 i) (deltaIv 6 j))).Mem
      (2 * (if i = 6 then 1 else 0) * (if j = 6 then 1 else 0)) := by
    have h := mul_mem (ofRat_mem (2 : ℚ)) (mul_mem (deltaIv_mem 6 i) (deltaIv_mem 6 j))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h2 : (mul (mul (ofRat 2) (cos2aIv k)) (ofRat (dAngle k i * dAngle k j))).Mem
      (2 * (Real.cos (angleVec (pad12 u0) k) ^ 2 - Real.sin (angleVec (pad12 u0) k) ^ 2)
        * (dAngle k i : ℝ) * (dAngle k j : ℝ)) := by
    have h := mul_mem (mul_mem (ofRat_mem (2 : ℚ)) (cos2aIv_mem k))
      (ofRat_mem ((dAngle k i * dAngle k j : ℤ) : ℚ))
    have hc : ((((dAngle k i * dAngle k j : ℤ) : ℚ)) : ℝ)
        = (dAngle k i : ℝ) * (dAngle k j : ℝ) := by
      push_cast
      ring
    rw [hc] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  rw [W2R, WijIv]
  exact sub_mem h1 h2

/-- `((2√W)·(2√W))⁻¹` 的区间。 -/
def invSq2SqrtWkIv (k : Fin 9) : RatInterval := invPos (sq (twoSqrtWkIv k))

theorem invSq2SqrtWkIv_mem (k : Fin 9) (h : 0 < (WkIv k).lo) :
    (invSq2SqrtWkIv k).Mem (((2 * √(Wk k)) * (2 * √(Wk k)))⁻¹) := by
  rw [invSq2SqrtWkIv]
  exact invPos_mem (sq_mem (twoSqrtWkIv_mem k))
    (sq_pos (twoSqrtWkIv k) (twoSqrtWkIv_pos k h))

/-- `∂²ρ_k/∂z_i∂z_j` 的区间（**原始未归一化**，与 `rho2R` 逐项对号）。 -/
def rho2Iv (k : Fin 9) (i j : Fin 7) : RatInterval :=
  sub
    (sub (neg (mul (mul (cosAIv k) (ofRat (dAngle k i))) (ofRat (dAngle k j))))
      (mul (invPos (twoSqrtWkIv k)) (WijIv k i j)))
    (mul (mul (mul (ofRat (-2)) (invPos (twoSqrtWkIv k))) (invSq2SqrtWkIv k))
      (mul (WiIv k j) (WiIv k i)))

theorem rho2Iv_mem (k : Fin 9) (i j : Fin 7) (hW : 0 < (WkIv k).lo) :
    (rho2Iv k i j).Mem (rho2R k i j) := by
  have h2 := twoSqrtWkIv_pos k hW
  have hnk : (neg (mul (mul (cosAIv k) (ofRat (dAngle k i))) (ofRat (dAngle k j)))).Mem
      (-(Real.cos (angleVec (pad12 u0) k) * (dAngle k i : ℝ) * (dAngle k j : ℝ))) := by
    refine neg_mem ?_
    have h := mul_mem (mul_mem (cosAIv_mem k) (ofRat_mem ((dAngle k i : ℤ) : ℚ)))
      (ofRat_mem ((dAngle k j : ℤ) : ℚ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hw : (mul (invPos (twoSqrtWkIv k)) (WijIv k i j)).Mem
      ((1 / (2 * √(Wk k))) * (W2R k i j)) :=
    mul_mem (invPos_mem_div (twoSqrtWkIv_mem k) h2) (WijIv_mem k i j)
  have h3 : (mul (mul (mul (ofRat (-2)) (invPos (twoSqrtWkIv k))) (invSq2SqrtWkIv k))
      (mul (WiIv k j) (WiIv k i))).Mem
      (((-2) * (1 / (2 * √(Wk k)))) * ((2 * √(Wk k)) * (2 * √(Wk k)))⁻¹
        * (WkD1 k j * WkD1 k i)) := by
    have h := mul_mem (mul_mem (mul_mem (ofRat_mem (-2 : ℚ))
      (invPos_mem_div (twoSqrtWkIv_mem k) h2)) (invSq2SqrtWkIv_mem k hW))
      (mul_mem (WiIv_mem k j) (WiIv_mem k i))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  rw [rho2Iv, rho2R]
  refine sub_mem (sub_mem ?_ ?_) ?_
  · simpa [Wfun_u0_eq_Wk k] using hnk
  · simpa [Wfun_u0_eq_Wk k] using hw
  · simpa [Wfun_u0_eq_Wk k, mul_comm, mul_left_comm, mul_assoc] using h3

/-- `C_k` 分量二阶的**规范实数形态**（`HESS-SPEC` L2 的 `C_{k,x,ij}` / `C_{k,y,ij}`）。 -/
def ringC2R (k : Fin 9) (c : Fin 2) (i j : Fin 7) : ℝ :=
  if c = 0 then
    rho2R k i j * Real.cos (thetaOf (angleVec (pad12 u0)) k)
      - rho1R k i * Real.sin (thetaOf (angleVec (pad12 u0)) k) * (dTheta k j : ℝ)
      - rho1R k j * Real.sin (thetaOf (angleVec (pad12 u0)) k) * (dTheta k i : ℝ)
      - rhoK (pad12 u0) k * Real.cos (thetaOf (angleVec (pad12 u0)) k)
          * (dTheta k i : ℝ) * (dTheta k j : ℝ)
  else
    rho2R k i j * Real.sin (thetaOf (angleVec (pad12 u0)) k)
      + rho1R k i * Real.cos (thetaOf (angleVec (pad12 u0)) k) * (dTheta k j : ℝ)
      + rho1R k j * Real.cos (thetaOf (angleVec (pad12 u0)) k) * (dTheta k i : ℝ)
      - rhoK (pad12 u0) k * Real.sin (thetaOf (angleVec (pad12 u0)) k)
          * (dTheta k i : ℝ) * (dTheta k j : ℝ)

/-- `C_k` 分量二阶的取值形态（`secondPartial` 版；`H3` 的消费形状）。 -/
theorem secondPartial_ringC (k : Fin 9) (c : Fin 2) (i j : Fin 7) (hW : 0 < Wfun k u0) :
    secondPartial (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp c) u0 i j
      = ringC2R k c i j := by
  by_cases hc0 : c = 0
  · subst hc0
    rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_ringC0 k hW) i j,
      ringC2R, if_pos rfl]
    exact ringC0_2_single k i j hW
  · have hc1 : c = 1 := by fin_cases c <;> simp_all
    subst hc1
    rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_ringC1 k hW) i j,
      ringC2R, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    exact ringC1_2_single k i j hW

/-- `arcEnd` 分量二阶的取值形态（= 根内 `secondPartial_ArcC` 的 `secondPartial` 读法）。 -/
theorem secondPartial_arcF (k : Fin 9) (c : Fin 2) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp c) u0 i j
      = -(if c = 0 then Real.cos (phiA k u0) else Real.sin (phiA k u0))
        * ((dTheta k i : ℝ) + (dAngle k i : ℝ))
        * ((dTheta k j : ℝ) + (dAngle k j : ℝ)) :=
  secondPartial_ArcC k c i j

/-- `wPoint.y` 二阶的取值形态（`secondPartial` 版）。 -/
theorem secondPartial_wyF (i j : Fin 7) (hWp : 0 < Wpf u0) :
    secondPartial (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1) u0 i j = wy2R i j := by
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_wyF hWp) i j]
  exact wy2_single i j hWp

/-- `C_k` 分量二阶的区间（`HESS-SPEC` L2 的区间版；`c=0` 用 `cosTIv`、`c=1` 用 `sinTIv`）。 -/
def ring2 (k : Fin 9) (c : Fin 2) (i j : Fin 7) : RatInterval :=
  if c = 0 then
    sub (sub (sub (mul (rho2Iv k i j) (cosTIv k))
              (mul (mul (drhoIv k i) (sinTIv k)) (ofRat (dTheta k j))))
            (mul (mul (drhoIv k j) (sinTIv k)) (ofRat (dTheta k i))))
      (mul (mul (rhoIv k) (cosTIv k)) (ofRat (dTheta k i * dTheta k j)))
  else
    sub (add (add (mul (rho2Iv k i j) (sinTIv k))
              (mul (mul (drhoIv k i) (cosTIv k)) (ofRat (dTheta k j))))
            (mul (mul (drhoIv k j) (cosTIv k)) (ofRat (dTheta k i))))
      (mul (mul (rhoIv k) (sinTIv k)) (ofRat (dTheta k i * dTheta k j)))

theorem ring2_mem (k : Fin 9) (c : Fin 2) (i j : Fin 7) (hW : 0 < (WkIv k).lo) :
    (ring2 k c i j).Mem (ringC2R k c i j) := by
  have h2 := twoSqrtWkIv_pos k hW
  have hWk : 0 < Wfun k u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast hW) (mem_lo_le (WkIv_mem k))
  have hρ2 := rho2Iv_mem k i j hW
  have hρ1i : (drhoIv k i).Mem (rho1R k i) := by
    have h := drhoIv_mem k i h2
    rw [drhoCLM_single_eq_rho1R k i] at h
    exact h
  have hρ1j : (drhoIv k j).Mem (rho1R k j) := by
    have h := drhoIv_mem k j h2
    rw [drhoCLM_single_eq_rho1R k j] at h
    exact h
  have hβi : (ofRat ((dTheta k i : ℤ) : ℚ)).Mem (dTheta k i : ℝ) := ofRat_mem _
  have hβj : (ofRat ((dTheta k j : ℤ) : ℚ)).Mem (dTheta k j : ℝ) := ofRat_mem _
  have hβij : (ofRat (dTheta k i * dTheta k j)).Mem ((dTheta k i : ℝ) * (dTheta k j : ℝ)) := by
    have h := ofRat_mem ((dTheta k i * dTheta k j : ℤ) : ℚ)
    push_cast at h
    exact h
  by_cases hc0 : c = 0
  · subst hc0
    rw [ring2, if_pos rfl, ringC2R, if_pos rfl]
    have h := sub_mem (sub_mem (sub_mem (mul_mem hρ2 (cosTIv_mem k))
        (mul_mem (mul_mem hρ1i (sinTIv_mem k)) hβj))
        (mul_mem (mul_mem hρ1j (sinTIv_mem k)) hβi))
      (mul_mem (mul_mem (rhoIv_mem k) (cosTIv_mem k)) hβij)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  · have hc1 : c = 1 := by fin_cases c <;> simp_all
    subst hc1
    rw [ring2, if_neg (by decide : ¬ ((1 : Fin 2) = 0)), ringC2R,
      if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    have h := sub_mem (add_mem (add_mem (mul_mem hρ2 (sinTIv_mem k))
        (mul_mem (mul_mem hρ1i (cosTIv_mem k)) hβj))
        (mul_mem (mul_mem hρ1j (cosTIv_mem k)) hβi))
      (mul_mem (mul_mem (rhoIv_mem k) (sinTIv_mem k)) hβij)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-! ### `wPoint` 纵坐标（`Wy = √Wp`）的区间 -/

/-- `∂Wp/∂z_i` 的区间。 -/
def WpiIv (i : Fin 7) : RatInterval :=
  sub (mul (ofRat (2 * cCert 6)) (deltaIv 6 i))
    (mul (ofRat (2 * ((cCert 5 - cCert 4) / 2)))
      (mul (ofRat (1 / 2)) (sub (deltaIv 5 i) (deltaIv 4 i))))

/-- `∂²Wp/∂z_i∂z_j` 的区间。 -/
def WpijIv (i j : Fin 7) : RatInterval :=
  sub (mul (ofRat 2) (mul (deltaIv 6 i) (deltaIv 6 j)))
    (mul (mul (ofRat 2) (mul (ofRat (1 / 2)) (sub (deltaIv 5 i) (deltaIv 4 i))))
      (mul (ofRat (1 / 2)) (sub (deltaIv 5 j) (deltaIv 4 j))))

/-- `((2√Wp)·(2√Wp))⁻¹` 的区间。 -/
def invSq2SqrtWpIv : RatInterval := invPos (sq twoSqrtWpIv)

theorem WpiIv_mem (i : Fin 7) : (WpiIv i).Mem (Wp1R i) := by
  have h1 : (mul (ofRat (2 * cCert 6)) (deltaIv 6 i)).Mem
      (2 * u0 6 * (if i = 6 then 1 else 0)) := by
    have h := mul_mem (ofRat_mem (2 * cCert 6)) (deltaIv_mem 6 i)
    have hc : (((2 * cCert 6 : ℚ)) : ℝ) = 2 * u0 6 := by
      rw [u0_six]
      push_cast
      rfl
    rwa [hc] at h
  have h2 : (mul (ofRat (2 * ((cCert 5 - cCert 4) / 2)))
      (mul (ofRat (1 / 2)) (sub (deltaIv 5 i) (deltaIv 4 i)))).Mem
      ((2 * ((u0 5 - u0 4) / 2))
        * ((1 / 2 : ℝ) * ((if i = 5 then 1 else 0) - (if i = 4 then 1 else 0)))) := by
    have h := mul_mem (ofRat_mem (2 * ((cCert 5 - cCert 4) / 2)))
      (mul_mem (ofRat_mem ((1 / 2 : ℚ))) (sub_mem (deltaIv_mem 5 i) (deltaIv_mem 4 i)))
    have hc1 : (((2 * ((cCert 5 - cCert 4) / 2) : ℚ)) : ℝ) = 2 * ((u0 5 - u0 4) / 2) := by
      simp only [u0_five, u0_four, cCertR]
      push_cast
      ring
    have hc2 : (((1 / 2 : ℚ)) : ℝ) = (1 / 2 : ℝ) := by norm_num
    rw [hc1, hc2] at h
    exact h
  rw [Wp1R, WpiIv]
  exact sub_mem h1 h2

theorem WpijIv_mem (i j : Fin 7) : (WpijIv i j).Mem (Wp2R i j) := by
  have h1 : (mul (ofRat 2) (mul (deltaIv 6 i) (deltaIv 6 j))).Mem
      (2 * (if i = 6 then 1 else 0) * (if j = 6 then 1 else 0)) := by
    have h := mul_mem (ofRat_mem (2 : ℚ)) (mul_mem (deltaIv_mem 6 i) (deltaIv_mem 6 j))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h2 : (mul (mul (ofRat 2) (mul (ofRat (1 / 2)) (sub (deltaIv 5 i) (deltaIv 4 i))))
      (mul (ofRat (1 / 2)) (sub (deltaIv 5 j) (deltaIv 4 j)))).Mem
      (2 * ((1 / 2 : ℝ) * ((if i = 5 then 1 else 0) - (if i = 4 then 1 else 0)))
        * ((1 / 2 : ℝ) * ((if j = 5 then 1 else 0) - (if j = 4 then 1 else 0)))) := by
    have h := mul_mem (mul_mem (ofRat_mem (2 : ℚ))
      (mul_mem (ofRat_mem ((1 / 2 : ℚ))) (sub_mem (deltaIv_mem 5 i) (deltaIv_mem 4 i))))
      (mul_mem (ofRat_mem ((1 / 2 : ℚ))) (sub_mem (deltaIv_mem 5 j) (deltaIv_mem 4 j)))
    have hc2 : (((1 / 2 : ℚ)) : ℝ) = (1 / 2 : ℝ) := by norm_num
    rw [hc2] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  rw [Wp2R, WpijIv]
  exact sub_mem h1 h2

theorem invSq2SqrtWpIv_mem (hWp : 0 < WpIv.lo) :
    invSq2SqrtWpIv.Mem (((2 * √Wp) * (2 * √Wp))⁻¹) := by
  rw [invSq2SqrtWpIv]
  exact invPos_mem (sq_mem twoSqrtWpIv_mem) (sq_pos twoSqrtWpIv (twoSqrtWpIv_pos hWp))

/-- `(wPoint.y)` 二阶的区间（与 `wy2R` 逐项对号）。 -/
def Wy2 (i j : Fin 7) : RatInterval :=
  add (mul (invPos twoSqrtWpIv) (WpijIv i j))
    (mul (mul (mul (ofRat (-2)) (invPos twoSqrtWpIv)) invSq2SqrtWpIv)
      (mul (WpiIv j) (WpiIv i)))

theorem Wy2_mem (i j : Fin 7) (hWp : 0 < WpIv.lo) : (Wy2 i j).Mem (wy2R i j) := by
  have hp := twoSqrtWpIv_pos hWp
  have h1 : (mul (invPos twoSqrtWpIv) (WpijIv i j)).Mem
      ((1 / (2 * √Wp)) * (Wp2R i j)) :=
    mul_mem (invPos_mem_div twoSqrtWpIv_mem hp) (WpijIv_mem i j)
  have h2 : (mul (mul (mul (ofRat (-2)) (invPos twoSqrtWpIv)) invSq2SqrtWpIv)
      (mul (WpiIv j) (WpiIv i))).Mem
      (((-2) * (1 / (2 * √Wp))) * ((2 * √Wp) * (2 * √Wp))⁻¹ * (Wp1R j * Wp1R i)) := by
    have h := mul_mem (mul_mem (mul_mem (ofRat_mem (-2 : ℚ))
      (invPos_mem_div twoSqrtWpIv_mem hp)) (invSq2SqrtWpIv_mem hWp))
      (mul_mem (WpiIv_mem j) (WpiIv_mem i))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  rw [wy2R, Wy2]
  refine add_mem ?_ ?_
  · simpa [Wpf_u0] using h1
  · simpa [Wpf_u0] using h2

/-! ## 7. `arcEnd` / `CLM` / `hub` 的"fderiv 的导数"与邻域可微性（装配层需要的前提） -/

/-- `∂²(arcEnd_c)` 的 CLM（从 `secondPartial_ArcC` 的两支提出）。 -/
def L2ArcC (k : Fin 9) (c : Fin 2) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  if c = 0 then
    (ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)).comp (-(Real.cos (phiA k u0) • phiCLM k))
  else
    (ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)).comp
      ((-(Real.sin (phiA k u0))) • phiCLM k)

theorem hasFDerivAt_fderiv_arcC (k : Fin 9) (c : Fin 2) :
    HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp c) z) (L2ArcC k c) u0 := by
  have hbr : (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp c) = ArcC k c := rfl
  rw [show (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp c) z)
      = (fun y : Fin 7 → ℝ => fderiv ℝ (ArcC k c) y) from by rw [hbr]]
  by_cases hc0 : c = 0
  · subst hc0
    have h1 : (fun y : Fin 7 → ℝ => fderiv ℝ (ArcC k 0) y)
        = fun y : Fin 7 → ℝ => (-(Real.sin (phiA k y))) • phiCLM k := by
      funext y
      exact fderiv_ArcC_zero k y
    rw [h1, L2ArcC, if_pos rfl]
    have hL2 : HasFDerivAt (fun y : Fin 7 → ℝ => (-(Real.sin (phiA k y))) • phiCLM k)
        ((ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)).comp
          (-(Real.cos (phiA k u0) • phiCLM k))) u0 := by
      have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k))
        (x := -(Real.sin (phiA k u0)))).comp u0 ((hasFDerivAt_phiA k u0).sin.neg)
      have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)) ∘
            (-(fun x : Fin 7 → ℝ => Real.sin (phiA k x))))
          = fun y : Fin 7 → ℝ => (-(Real.sin (phiA k y))) • phiCLM k := by
        funext y
        rw [Function.comp_apply, Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply]
      rw [he] at h
      exact h
    exact hL2
  · have hc1 : c = 1 := by fin_cases c <;> simp_all
    subst hc1
    have h1 : (fun y : Fin 7 → ℝ => fderiv ℝ (ArcC k 1) y)
        = fun y : Fin 7 → ℝ => (Real.cos (phiA k y)) • phiCLM k := by
      funext y
      exact fderiv_ArcC_one k y
    rw [h1, L2ArcC, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    have hL2 : HasFDerivAt (fun y : Fin 7 → ℝ => (Real.cos (phiA k y)) • phiCLM k)
        ((ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)).comp
          ((-(Real.sin (phiA k u0))) • phiCLM k)) u0 := by
      have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k))
        (x := Real.cos (phiA k u0))).comp u0 ((hasFDerivAt_phiA k u0).cos)
      have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)) ∘
            (fun x : Fin 7 → ℝ => Real.cos (phiA k x)))
          = fun y : Fin 7 → ℝ => (Real.cos (phiA k y)) • phiCLM k := by
        funext y
        rw [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
      rw [he] at h
      exact h
    exact hL2

/-- CLM 函数的 `fderiv` 的导数恒为 0。 -/
theorem hasFDerivAt_fderiv_clm (L : (Fin 7 → ℝ) →L[ℝ] ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => L z) y)
      (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) u0 := by
  have hfun : (fun y : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => L z) y) = fun _ => L := by
    funext y
    exact (ContinuousLinearMap.hasFDerivAt (f := L) (x := y)).fderiv
  rw [hfun]
  exact hasFDerivAt_const L u0

/-- 常值函数的 `fderiv` 的导数恒为 0。 -/
theorem hasFDerivAt_fderiv_const (c : ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ (fun _ : Fin 7 → ℝ => c) y)
      (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) u0 := by
  have hfun : (fun y : Fin 7 → ℝ => fderiv ℝ (fun _ : Fin 7 → ℝ => c) y)
      = fun _ => (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) := by
    funext y
    exact fderiv_const_apply c
  rw [hfun]
  exact hasFDerivAt_const (0 : (Fin 7 → ℝ) →L[ℝ] ℝ) u0

/-- 与 CLM 相同的函数：`fderiv` 的导数为 0。 -/
theorem hasFDerivAt_fderiv_of_eq_clm {φ : (Fin 7 → ℝ) → ℝ} {L : (Fin 7 → ℝ) →L[ℝ] ℝ}
    (h : φ = fun z => L z) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ φ y)
      (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) u0 := by
  rw [h]
  exact hasFDerivAt_fderiv_clm L

/-- 与常值函数相同的函数：`fderiv` 的导数为 0。 -/
theorem hasFDerivAt_fderiv_of_eq_const {φ : (Fin 7 → ℝ) → ℝ} {c : ℝ}
    (h : φ = fun _ => c) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ φ y)
      (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) u0 := by
  rw [h]
  exact hasFDerivAt_fderiv_const c

/-- 与 CLM 相同的函数：处处可微。 -/
theorem eventually_diff_of_eq_clm {φ : (Fin 7 → ℝ) → ℝ} {L : (Fin 7 → ℝ) →L[ℝ] ℝ}
    (h : φ = fun z => L z) : ∀ᶠ z in nhds u0, DifferentiableAt ℝ φ z := by
  rw [h]
  exact Filter.Eventually.of_forall fun z =>
    (ContinuousLinearMap.hasFDerivAt (f := L) (x := z)).differentiableAt

/-- 与常值函数相同的函数：处处可微。 -/
theorem eventually_diff_of_eq_const {φ : (Fin 7 → ℝ) → ℝ} {c : ℝ} (h : φ = fun _ => c) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ φ z := by
  rw [h]
  exact Filter.Eventually.of_forall fun _ => differentiableAt_const c

/-- `hub1` 横坐标作为 `z` 的函数 = `coord 5`。 -/
theorem hub1xF_eq : (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0) = fun z => coord 5 z := by
  funext z
  exact (hub1_coord0 (pad12 z)).trans (pad12_five z)

/-- `hub0` 横坐标作为 `z` 的函数 = `coord 4`。 -/
theorem hub0xF_eq : (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0) = fun z => coord 4 z := by
  funext z
  exact (hub0_coord0 (pad12 z)).trans (pad12_four z)

/-- `hub1` 纵坐标恒为 0。 -/
theorem hub1yF_eq : (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1) = fun _ => (0 : ℝ) := by
  funext z
  rw [hub1_coord1]

/-- `hub0` 纵坐标恒为 0。 -/
theorem hub0yF_eq : (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1) = fun _ => (0 : ℝ) := by
  funext z
  rw [hub0_coord1]

/-- `C_k` 横坐标的邻域可微性。 -/
theorem eventually_diff_ringC0 (k : Fin 9) (hW : 0 < Wfun k u0) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0) z := by
  have hfun : (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0)
      = fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.cos (thetaOf (angleVec (pad12 z)) k) := by
    funext z
    rw [ringCenter_coord0]
  have hev : ∀ᶠ z in nhds u0, DifferentiableAt ℝ
      (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.cos (thetaOf (angleVec (pad12 z)) k)) z := by
    filter_upwards [(hasFDerivAt_Wfun k u0).continuousAt.eventually
      (eventually_gt_nhds hW)] with z hz
    exact ((hasFDerivAt_rhoK_any k z (ne_of_gt hz)).mul
      ((hasFDerivAt_thetaOf_any k z).cos)).differentiableAt
  filter_upwards [hev] with z hz
  simpa only [hfun] using hz

/-- `C_k` 纵坐标的邻域可微性。 -/
theorem eventually_diff_ringC1 (k : Fin 9) (hW : 0 < Wfun k u0) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1) z := by
  have hfun : (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1)
      = fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.sin (thetaOf (angleVec (pad12 z)) k) := by
    funext z
    rw [ringCenter_coord1]
  have hev : ∀ᶠ z in nhds u0, DifferentiableAt ℝ
      (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.sin (thetaOf (angleVec (pad12 z)) k)) z := by
    filter_upwards [(hasFDerivAt_Wfun k u0).continuousAt.eventually
      (eventually_gt_nhds hW)] with z hz
    exact ((hasFDerivAt_rhoK_any k z (ne_of_gt hz)).mul
      ((hasFDerivAt_thetaOf_any k z).sin)).differentiableAt
  filter_upwards [hev] with z hz
  simpa only [hfun] using hz

/-- `B_k` 横坐标的邻域可微性。 -/
theorem eventually_diff_arcC0 (k : Fin 9) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 0) z := by
  have hfun : (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 0)
      = fun z : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k) := by
    funext z
    rw [arcEnd_coord0]
  have hev : ∀ᶠ z in nhds u0, DifferentiableAt ℝ
      (fun z : Fin 7 → ℝ =>
        Real.cos (thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k)) z := by
    filter_upwards [Filter.Eventually.of_forall fun z : Fin 7 → ℝ =>
      ((hasFDerivAt_thetaOf_any k z).add (hasFDerivAt_angleVec_any k z)).cos.differentiableAt]
      with z hz
    exact hz
  filter_upwards [hev] with z hz
  rw [hfun]
  exact hz

/-- `B_k` 纵坐标的邻域可微性。 -/
theorem eventually_diff_arcC1 (k : Fin 9) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 1) z := by
  have hfun : (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) k).ofLp 1)
      = fun z : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k) := by
    funext z
    rw [arcEnd_coord1]
  have hev : ∀ᶠ z in nhds u0, DifferentiableAt ℝ
      (fun z : Fin 7 → ℝ =>
        Real.sin (thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k)) z := by
    filter_upwards [Filter.Eventually.of_forall fun z : Fin 7 → ℝ =>
      ((hasFDerivAt_thetaOf_any k z).add (hasFDerivAt_angleVec_any k z)).sin.differentiableAt]
      with z hz
    exact hz
  filter_upwards [hev] with z hz
  rw [hfun]
  exact hz

/-! ## 8. `Uvec` 分量的"fderiv 的导数"（T1：`C_s + C_{s+1} − B_s`） -/

/-- `∂²(U_s.x)` 的 CLM。 -/
def L2UvecC0 (s : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (L2RingC0 s + L2RingC0 (s + 1)) - L2ArcC s 0

/-- `∂²(U_s.y)` 的 CLM。 -/
def L2UvecC1 (s : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (L2RingC1 s + L2RingC1 (s + 1)) - L2ArcC s 1

theorem hasFDerivAt_fderiv_UvecC0 (s : Fin 9)
    (h0 : 0 < (WkIv s).lo) (h1 : 0 < (WkIv (s + 1)).lo) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 0) z)
      (L2UvecC0 s) u0 := by
  have hW0 : 0 < Wfun s u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h0) (mem_lo_le (WkIv_mem s))
  have hW1 : 0 < Wfun (s + 1) u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h1) (mem_lo_le (WkIv_mem (s + 1)))
  have hC := hasFDerivAt_fderiv_ringC0 s hW0
  have hC' := hasFDerivAt_fderiv_ringC0 (s + 1) hW1
  have hA := hasFDerivAt_fderiv_arcC s 0
  have hCd := eventually_diff_ringC0 s hW0
  have hC'd := eventually_diff_ringC0 (s + 1) hW1
  have hAd := eventually_diff_arcC0 s
  have hfun : (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 0)
      = (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 0)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 0)
        - (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) s).ofLp 0) := by
    funext z
    rw [Uvec_coord0]
    rfl
  have hsum : HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ
      ((fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 0)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 0)) z)
      (L2RingC0 s + L2RingC0 (s + 1)) u0 :=
    hasFDerivAt_fderiv_add hC hC' hCd hC'd
  have hsumd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ
      ((fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 0)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 0)) z :=
    (hCd.and hC'd).mono fun z hz => hz.1.add hz.2
  have hsub := hasFDerivAt_fderiv_sub hsum hA hsumd hAd
  rw [show (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 0) z)
      = (fun z : Fin 7 → ℝ => fderiv ℝ
          ((fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 0)
            + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 0)
            - (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) s).ofLp 0)) z) from by rw [hfun]]
  rw [L2UvecC0]
  exact hsub

theorem hasFDerivAt_fderiv_UvecC1 (s : Fin 9)
    (h0 : 0 < (WkIv s).lo) (h1 : 0 < (WkIv (s + 1)).lo) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 1) z)
      (L2UvecC1 s) u0 := by
  have hW0 : 0 < Wfun s u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h0) (mem_lo_le (WkIv_mem s))
  have hW1 : 0 < Wfun (s + 1) u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h1) (mem_lo_le (WkIv_mem (s + 1)))
  have hC := hasFDerivAt_fderiv_ringC1 s hW0
  have hC' := hasFDerivAt_fderiv_ringC1 (s + 1) hW1
  have hA := hasFDerivAt_fderiv_arcC s 1
  have hCd := eventually_diff_ringC1 s hW0
  have hC'd := eventually_diff_ringC1 (s + 1) hW1
  have hAd := eventually_diff_arcC1 s
  have hfun : (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 1)
      = (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 1)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 1)
        - (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) s).ofLp 1) := by
    funext z
    rw [Uvec_coord1]
    rfl
  have hsum : HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ
      ((fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 1)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 1)) z)
      (L2RingC1 s + L2RingC1 (s + 1)) u0 :=
    hasFDerivAt_fderiv_add hC hC' hCd hC'd
  have hsumd : ∀ᶠ z in nhds u0, DifferentiableAt ℝ
      ((fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 1)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 1)) z :=
    (hCd.and hC'd).mono fun z hz => hz.1.add hz.2
  have hsub := hasFDerivAt_fderiv_sub hsum hA hsumd hAd
  rw [show (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 1) z)
      = (fun z : Fin 7 → ℝ => fderiv ℝ
          ((fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 1)
            + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 1)
            - (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) s).ofLp 1)) z) from by rw [hfun]]
  rw [L2UvecC1]
  exact hsub

/-- `U_s` 横坐标的邻域可微性。 -/
theorem eventually_diff_UvecC0 (s : Fin 9)
    (h0 : 0 < (WkIv s).lo) (h1 : 0 < (WkIv (s + 1)).lo) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 0) z := by
  have hW0 : 0 < Wfun s u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h0) (mem_lo_le (WkIv_mem s))
  have hW1 : 0 < Wfun (s + 1) u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h1) (mem_lo_le (WkIv_mem (s + 1)))
  have hfun : (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 0)
      = (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 0)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 0)
        - (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) s).ofLp 0) := by
    funext z
    rw [Uvec_coord0]
    rfl
  filter_upwards [eventually_diff_ringC0 s hW0, eventually_diff_ringC0 (s + 1) hW1,
    eventually_diff_arcC0 s] with z h1' h2' h3'
  simpa only [hfun] using (h1'.add h2').sub h3'

/-- `U_s` 纵坐标的邻域可微性。 -/
theorem eventually_diff_UvecC1 (s : Fin 9)
    (h0 : 0 < (WkIv s).lo) (h1 : 0 < (WkIv (s + 1)).lo) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 1) z := by
  have hW0 : 0 < Wfun s u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h0) (mem_lo_le (WkIv_mem s))
  have hW1 : 0 < Wfun (s + 1) u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h1) (mem_lo_le (WkIv_mem (s + 1)))
  have hfun : (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 1)
      = (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) s).ofLp 1)
        + (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) (s + 1)).ofLp 1)
        - (fun z : Fin 7 → ℝ => (arcEnd (pad12 z) s).ofLp 1) := by
    funext z
    rw [Uvec_coord1]
    rfl
  filter_upwards [eventually_diff_ringC1 s hW0, eventually_diff_ringC1 (s + 1) hW1,
    eventually_diff_arcC1 s] with z h1' h2' h3'
  simpa only [hfun] using (h1'.add h2').sub h3'

/-- `wPoint.x` 的 `fderiv` 的导数 = 0（`(z₄+z₅)/2` 是 CLM）。 -/
theorem hasFDerivAt_fderiv_wxF :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0) y)
      (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) u0 := by
  have hclm : (fun z : Fin 7 → ℝ => ((1 / 2 : ℝ) • (coord 4 + coord 5)) z)
      = fun z : Fin 7 → ℝ => (1 / 2 : ℝ) * (z 4 + z 5) := by
    funext z
    rw [smul_apply, add_apply, smul_eq_mul]
    rfl
  have hfun : (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0)
      = fun z : Fin 7 → ℝ => (1 / 2 : ℝ) * (z 4 + z 5) := by
    funext z
    rw [wPoint_coord0, pad12_four, pad12_five]
    ring
  have hφ : (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0)
      = fun z : Fin 7 → ℝ => ((1 / 2 : ℝ) • (coord 4 + coord 5)) z := by
    rw [hfun, hclm]
  rw [show (fun y : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0) y)
      = (fun y : Fin 7 → ℝ => fderiv ℝ
          (fun z : Fin 7 → ℝ => ((1 / 2 : ℝ) • (coord 4 + coord 5)) z) y) from by rw [hφ]]
  exact hasFDerivAt_fderiv_clm ((1 / 2 : ℝ) • (coord 4 + coord 5))

/-- `wPoint.x` 的邻域可微性。 -/
theorem eventually_diff_wxF :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0) z := by
  have hfun : (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0)
      = fun z : Fin 7 → ℝ => (1 / 2 : ℝ) * (z 4 + z 5) := by
    funext z
    rw [wPoint_coord0, pad12_four, pad12_five]
    ring
  have hev : ∀ᶠ z in nhds u0, DifferentiableAt ℝ
      (fun z : Fin 7 → ℝ => (1 / 2 : ℝ) * (z 4 + z 5)) z :=
    Filter.Eventually.of_forall fun z =>
      (((ContinuousLinearMap.hasFDerivAt (f := coord 4) (x := z)).add
        (ContinuousLinearMap.hasFDerivAt (f := coord 5) (x := z))).const_mul (1 / 2)).differentiableAt
  filter_upwards [hev] with z hz
  simpa only [hfun] using hz

/-- `wPoint.y` 的邻域可微性。 -/
theorem eventually_diff_wyF (hWp : 0 < Wpf u0) :
    ∀ᶠ z in nhds u0, DifferentiableAt ℝ (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1) z := by
  filter_upwards [(hasFDerivAt_Wpf_any u0).continuousAt.eventually
    (eventually_gt_nhds hWp)] with z hz
  rw [wpF_eq_sqrt]
  exact (((Real.hasDerivAt_sqrt (ne_of_gt hz)).differentiableAt).comp z
    (hasFDerivAt_Wpf_any z).differentiableAt)

/-! ## 9. `Δ` 的二阶区间族 `d2xIv` / `d2yIv`（= `hessIv` 的两个参数）与 `Mem` -/

/-- `Δx_k = (Apt k).x − (Bpt k).x`（真值形态；`Apt`/`Bpt` 是 `ResidualDerivD` 的 5→1 化归）。 -/
def DeltaX (k : Fin 5) : (Fin 7 → ℝ) → ℝ :=
  fun z => ((Apt k) (pad12 z)).ofLp 0 - ((Bpt k) (pad12 z)).ofLp 0

/-- `Δy_k`。 -/
def DeltaY (k : Fin 5) : (Fin 7 → ℝ) → ℝ :=
  fun z => ((Apt k) (pad12 z)).ofLp 1 - ((Bpt k) (pad12 z)).ofLp 1

/-- **`Δ` 的二阶 x 分量**（`Fin 5 → Fin 7 → Fin 7 → RatInterval`，与 `hessIv` 的参数类型一致）：
`k = 4` 走 `wPoint`/`ringCenter 6` 支；`k = 0..3` 走 `Uvec`/`hub` 支（`hub` 的二阶为 0 ⇒ 尾项 `ofRat 0`）。 -/
def d2xIv (k : Fin 5) (i j : Fin 7) : RatInterval :=
  if k = 4 then neg (ring2 6 0 i j)
  else sub (sub (add (ring2 (resSlot k) 0 i j) (ring2 ((resSlot k) + 1) 0 i j))
      (arc2 (resSlot k) 0 i j)) (ofRat 0)

/-- **`Δ` 的二阶 y 分量**。 -/
def d2yIv (k : Fin 5) (i j : Fin 7) : RatInterval :=
  if k = 4 then sub (Wy2 i j) (ring2 6 1 i j)
  else sub (sub (add (ring2 (resSlot k) 1 i j) (ring2 ((resSlot k) + 1) 1 i j))
      (arc2 (resSlot k) 1 i j)) (ofRat 0)

/-- `Δx`（`Uvec` 支，`B = hub0`：`mm = 1, 2`）的 Mem。 -/
theorem d2xIv_mem_uvec_hub0 (s : Fin 9) (i j : Fin 7)
    (h0 : 0 < (WkIv s).lo) (h1 : 0 < (WkIv (s + 1)).lo) :
    (sub (sub (add (ring2 s 0 i j) (ring2 (s + 1) 0 i j)) (arc2 s 0 i j)) (ofRat 0)).Mem
      (secondPartial (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 0 - (hub0 (pad12 z)).ofLp 0)
        u0 i j) := by
  have hW0 : 0 < Wfun s u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h0) (mem_lo_le (WkIv_mem s))
  have hW1 : 0 < Wfun (s + 1) u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h1) (mem_lo_le (WkIv_mem (s + 1)))
  rw [secondPartial_sub (hasFDerivAt_fderiv_UvecC0 s h0 h1)
    (hasFDerivAt_fderiv_of_eq_clm hub0xF_eq)
    (eventually_diff_UvecC0 s h0 h1) (eventually_diff_of_eq_clm hub0xF_eq)]
  rw [secondPartial_Uvec_coord s 0 i j (hasFDerivAt_fderiv_ringC0 s hW0)
    (hasFDerivAt_fderiv_ringC0 (s + 1) hW1) (hasFDerivAt_fderiv_arcC s 0)
    (eventually_diff_ringC0 s hW0) (eventually_diff_ringC0 (s + 1) hW1)
    (eventually_diff_arcC0 s)]
  rw [secondPartial_hub0_coord0 i j]
  rw [secondPartial_ringC s 0 i j hW0, secondPartial_ringC (s + 1) 0 i j hW1,
    secondPartial_arcF s 0 i j]
  have h0m : (ofRat (0 : ℚ)).Mem (0 : ℝ) := by simpa using ofRat_mem (0 : ℚ)
  exact RatInterval.sub_mem (RatInterval.sub_mem
    (RatInterval.add_mem (ring2_mem s 0 i j h0) (ring2_mem (s + 1) 0 i j h1))
    (mem_arc2 s 0 i j)) h0m

/-- `Δx`（`Uvec` 支，`B = hub1`：`mm = 0, 3`）的 Mem。 -/
theorem d2xIv_mem_uvec_hub1 (s : Fin 9) (i j : Fin 7)
    (h0 : 0 < (WkIv s).lo) (h1 : 0 < (WkIv (s + 1)).lo) :
    (sub (sub (add (ring2 s 0 i j) (ring2 (s + 1) 0 i j)) (arc2 s 0 i j)) (ofRat 0)).Mem
      (secondPartial (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 0 - (hub1 (pad12 z)).ofLp 0)
        u0 i j) := by
  have hW0 : 0 < Wfun s u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h0) (mem_lo_le (WkIv_mem s))
  have hW1 : 0 < Wfun (s + 1) u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h1) (mem_lo_le (WkIv_mem (s + 1)))
  rw [secondPartial_sub (hasFDerivAt_fderiv_UvecC0 s h0 h1)
    (hasFDerivAt_fderiv_of_eq_clm hub1xF_eq)
    (eventually_diff_UvecC0 s h0 h1) (eventually_diff_of_eq_clm hub1xF_eq)]
  rw [secondPartial_Uvec_coord s 0 i j (hasFDerivAt_fderiv_ringC0 s hW0)
    (hasFDerivAt_fderiv_ringC0 (s + 1) hW1) (hasFDerivAt_fderiv_arcC s 0)
    (eventually_diff_ringC0 s hW0) (eventually_diff_ringC0 (s + 1) hW1)
    (eventually_diff_arcC0 s)]
  rw [secondPartial_hub1_coord0 i j]
  rw [secondPartial_ringC s 0 i j hW0, secondPartial_ringC (s + 1) 0 i j hW1,
    secondPartial_arcF s 0 i j]
  have h0m : (ofRat (0 : ℚ)).Mem (0 : ℝ) := by simpa using ofRat_mem (0 : ℚ)
  exact RatInterval.sub_mem (RatInterval.sub_mem
    (RatInterval.add_mem (ring2_mem s 0 i j h0) (ring2_mem (s + 1) 0 i j h1))
    (mem_arc2 s 0 i j)) h0m

/-- `Δy`（`Uvec` 支，`B = hub0`；两个 hub 的 y 坐标都是常数 0）。 -/
theorem d2yIv_mem_uvec_hub0 (s : Fin 9) (i j : Fin 7)
    (h0 : 0 < (WkIv s).lo) (h1 : 0 < (WkIv (s + 1)).lo) :
    (sub (sub (add (ring2 s 1 i j) (ring2 (s + 1) 1 i j)) (arc2 s 1 i j)) (ofRat 0)).Mem
      (secondPartial (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 1 - (hub0 (pad12 z)).ofLp 1)
        u0 i j) := by
  have hW0 : 0 < Wfun s u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h0) (mem_lo_le (WkIv_mem s))
  have hW1 : 0 < Wfun (s + 1) u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h1) (mem_lo_le (WkIv_mem (s + 1)))
  rw [secondPartial_sub (hasFDerivAt_fderiv_UvecC1 s h0 h1)
    (hasFDerivAt_fderiv_of_eq_const hub0yF_eq)
    (eventually_diff_UvecC1 s h0 h1) (eventually_diff_of_eq_const hub0yF_eq)]
  rw [secondPartial_Uvec_coord s 1 i j (hasFDerivAt_fderiv_ringC1 s hW0)
    (hasFDerivAt_fderiv_ringC1 (s + 1) hW1) (hasFDerivAt_fderiv_arcC s 1)
    (eventually_diff_ringC1 s hW0) (eventually_diff_ringC1 (s + 1) hW1)
    (eventually_diff_arcC1 s)]
  rw [secondPartial_hub0_coord1 i j]
  rw [secondPartial_ringC s 1 i j hW0, secondPartial_ringC (s + 1) 1 i j hW1,
    secondPartial_arcF s 1 i j]
  have h0m : (ofRat (0 : ℚ)).Mem (0 : ℝ) := by simpa using ofRat_mem (0 : ℚ)
  exact RatInterval.sub_mem (RatInterval.sub_mem
    (RatInterval.add_mem (ring2_mem s 1 i j h0) (ring2_mem (s + 1) 1 i j h1))
    (mem_arc2 s 1 i j)) h0m

/-- `Δy`（`Uvec` 支，`B = hub1`）。 -/
theorem d2yIv_mem_uvec_hub1 (s : Fin 9) (i j : Fin 7)
    (h0 : 0 < (WkIv s).lo) (h1 : 0 < (WkIv (s + 1)).lo) :
    (sub (sub (add (ring2 s 1 i j) (ring2 (s + 1) 1 i j)) (arc2 s 1 i j)) (ofRat 0)).Mem
      (secondPartial (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp 1 - (hub1 (pad12 z)).ofLp 1)
        u0 i j) := by
  have hW0 : 0 < Wfun s u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h0) (mem_lo_le (WkIv_mem s))
  have hW1 : 0 < Wfun (s + 1) u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast h1) (mem_lo_le (WkIv_mem (s + 1)))
  rw [secondPartial_sub (hasFDerivAt_fderiv_UvecC1 s h0 h1)
    (hasFDerivAt_fderiv_of_eq_const hub1yF_eq)
    (eventually_diff_UvecC1 s h0 h1) (eventually_diff_of_eq_const hub1yF_eq)]
  rw [secondPartial_Uvec_coord s 1 i j (hasFDerivAt_fderiv_ringC1 s hW0)
    (hasFDerivAt_fderiv_ringC1 (s + 1) hW1) (hasFDerivAt_fderiv_arcC s 1)
    (eventually_diff_ringC1 s hW0) (eventually_diff_ringC1 (s + 1) hW1)
    (eventually_diff_arcC1 s)]
  rw [secondPartial_hub1_coord1 i j]
  rw [secondPartial_ringC s 1 i j hW0, secondPartial_ringC (s + 1) 1 i j hW1,
    secondPartial_arcF s 1 i j]
  have h0m : (ofRat (0 : ℚ)).Mem (0 : ℝ) := by simpa using ofRat_mem (0 : ℚ)
  exact RatInterval.sub_mem (RatInterval.sub_mem
    (RatInterval.add_mem (ring2_mem s 1 i j h0) (ring2_mem (s + 1) 1 i j h1))
    (mem_arc2 s 1 i j)) h0m

/-- `Δx`（`wPoint` 支）：`Δx₄ = wPoint.x − C₆.x`，`wPoint.x` 线性 ⇒ 二阶 0。 -/
theorem d2xIv_mem_w (i j : Fin 7) (hW6 : 0 < (WkIv 6).lo) :
    (neg (ring2 6 0 i j)).Mem
      (secondPartial (fun z : Fin 7 → ℝ =>
        (wPoint (pad12 z)).ofLp 0 - (ringCenter (pad12 z) 6).ofLp 0) u0 i j) := by
  have hW : 0 < Wfun 6 u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast hW6) (mem_lo_le (WkIv_mem 6))
  rw [secondPartial_sub hasFDerivAt_fderiv_wxF (hasFDerivAt_fderiv_ringC0 6 hW)
    eventually_diff_wxF (eventually_diff_ringC0 6 hW)]
  rw [secondPartial_wxF i j, secondPartial_ringC 6 0 i j hW]
  simpa using neg_mem (ring2_mem 6 0 i j hW6)

/-- `Δy`（`wPoint` 支）：`Δy₄ = wPoint.y − C₆.y`。 -/
theorem d2yIv_mem_w (i j : Fin 7) (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    (sub (Wy2 i j) (ring2 6 1 i j)).Mem
      (secondPartial (fun z : Fin 7 → ℝ =>
        (wPoint (pad12 z)).ofLp 1 - (ringCenter (pad12 z) 6).ofLp 1) u0 i j) := by
  have hW : 0 < Wfun 6 u0 := by
    rw [Wfun_u0_eq_Wk]
    exact lt_of_lt_of_le (by exact_mod_cast hW6) (mem_lo_le (WkIv_mem 6))
  have hWp' : 0 < Wpf u0 := by
    rw [Wpf_u0]
    exact lt_of_lt_of_le (by exact_mod_cast hWp) (mem_lo_le WpIv_mem)
  rw [secondPartial_sub (hasFDerivAt_fderiv_wyF hWp') (hasFDerivAt_fderiv_ringC1 6 hW)
    (eventually_diff_wyF hWp') (eventually_diff_ringC1 6 hW)]
  rw [secondPartial_wyF i j hWp', secondPartial_ringC 6 1 i j hW]
  exact sub_mem (Wy2_mem i j hWp) (ring2_mem 6 1 i j hW6)

/-- **`d2xIv` 的 `Mem`（全 5×7×7 格，条件 = 4 条有限有理不等式）**。 -/
theorem d2xIv_mem (k : Fin 5) (i j : Fin 7)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    (d2xIv k i j).Mem (secondPartial (DeltaX k) u0 i j) := by
  fin_cases k
  · exact d2xIv_mem_uvec_hub1 1 i j h0 h1
  · exact d2xIv_mem_uvec_hub0 2 i j h0 h1
  · exact d2xIv_mem_uvec_hub0 3 i j h0 h1
  · exact d2xIv_mem_uvec_hub1 8 i j h0 h1
  · exact d2xIv_mem_w i j hW6

/-- **`d2yIv` 的 `Mem`（全 5×7×7 格）**。 -/
theorem d2yIv_mem (k : Fin 5) (i j : Fin 7)
    (h0 : 0 < (WkIv (resSlot k)).lo) (h1 : 0 < (WkIv ((resSlot k) + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    (d2yIv k i j).Mem (secondPartial (DeltaY k) u0 i j) := by
  fin_cases k
  · exact d2yIv_mem_uvec_hub1 1 i j h0 h1
  · exact d2yIv_mem_uvec_hub0 2 i j h0 h1
  · exact d2yIv_mem_uvec_hub0 3 i j h0 h1
  · exact d2yIv_mem_uvec_hub1 8 i j h0 h1
  · exact d2yIv_mem_w i j hW6 hWp

/-! ## 10. 单格判据（Lead 派发的"先做一格"）：`(k,i,j) = (0,0,0)` 与 `(4,0,0)` -/

theorem d2xIv_mem_cell_0_0_0 (h0 : 0 < (WkIv 1).lo) (h1 : 0 < (WkIv (1 + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    (d2xIv 0 0 0).Mem (secondPartial (DeltaX 0) u0 0 0) :=
  d2xIv_mem 0 0 0 h0 h1 hW6 hWp

theorem d2yIv_mem_cell_0_0_0 (h0 : 0 < (WkIv 1).lo) (h1 : 0 < (WkIv (1 + 1)).lo)
    (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    (d2yIv 0 0 0).Mem (secondPartial (DeltaY 0) u0 0 0) :=
  d2yIv_mem 0 0 0 h0 h1 hW6 hWp

theorem d2xIv_mem_cell_4_0_0 (hW6 : 0 < (WkIv 6).lo) :
    (d2xIv 4 0 0).Mem (secondPartial (DeltaX 4) u0 0 0) :=
  d2xIv_mem_w 0 0 hW6

theorem d2yIv_mem_cell_4_0_0 (hW6 : 0 < (WkIv 6).lo) (hWp : 0 < WpIv.lo) :
    (d2yIv 4 0 0).Mem (secondPartial (DeltaY 4) u0 0 0) :=
  d2yIv_mem_w 0 0 hW6 hWp

end N11Formalization
