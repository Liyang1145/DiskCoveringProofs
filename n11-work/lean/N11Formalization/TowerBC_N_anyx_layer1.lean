import N11Formalization.D2Leaves
import N11Formalization.ResidualDerivJT
import N11Formalization.NondegProof

/-!
# tower-bc / 件 N：**一般点二阶层（汇总件 · 第一批）** —— `cos a`、`W`、`√W`、`cos θ`、`sin θ`

## 为什么有这件
盒版二阶叶 6 族（`rho2IvBox`/`ring2Box`/`arc2Box`/`Wy2Box`/`d2xIvBox`/`d2yIvBox`）要求对
**证书球内任意 `x`** 成立（`HessSeam.HHBall Hess = ∀ x ∈ closedBall u0 rhoCertR, ∀ i j mm, (Hess i j mm).Mem (hessEntryAt x i j mm)` ✗ 全称），
而根内二阶事实**全是 `u0` 实例化**（`L2Wfun`/`L2RingC0/1`/`L2CosA` 是**常** CLM；`L2*At`、`secondPartial_*_any` **0 命中**
⇒ 见件 `H2BoxGap_probe.lean`、claim C1322）⇒ 必须补**一般点二阶层** ✓（Lead 裁决 甲）。

## 机制（本层**机械可得**的根据 ✓）
`D2Leaves` 各 `hasFDerivAt_fderiv_*` 的证明**内部已证一般 `y` 的恒等式** —— 因为它们用的是
`hasFDerivAt_angleVec_any k y` / `hasFDerivAt_thetaOf_any k y` / `hasFDerivAt_Wfun k y`（**任意点** ✓).
⇒ 只需把 `u0` 换成自由变量 `x` ⇒ 逐片通过 ✓（件 K `BD589A073C2F818D`、件 L、件 M `C960F9E52E2CDF33` 均一发即过 ✓）。

## 自足性
`evidence/` 不在 `lake` 的 srcDir ⇒ **件之间不能 `import`** ✗ ⇒ 本层**汇入这一份**（K/L/M 是逐片台账，
本件是它们的**合并 + 新增** ✓）。命名空间 `TowerBC` ✓（与根内件不撞名 ✓）。

## 本批含（5 个分量函数）
`cos a_k`（`L2CosAAt`）｜`W_k`（`L2WfunAt`）｜`∂W` 的取值（`dWfun_single_any`）｜`√W_k`（`L2SqrtWAt`）｜`cos θ_k`/`sin θ_k`（`L2CosThetaAt`/`L2SinThetaAt`）
**待补**（后续批次）：`ρ_k`（`L2RhoAt`）｜`ringC0/ringC1`｜`arcEnd`｜`wPoint.y`（`L2Wy`）
-/

noncomputable section

namespace N11Formalization

namespace TowerBC

open RatInterval

set_option maxHeartbeats 800000

/-! ## 1. `cos a_k`（系数 `daCLM`/`dAngle`） -/

/-- 一般点 `x` 处的 `∂²(cos a_k)` 算子。 -/
def L2CosAAt (x : Fin 7 → ℝ) (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ (daCLM k)).comp
    (-(Real.cos (angleVec (pad12 x) k)) • daCLM k)

theorem hasFDerivAt_fderiv_cosA_any (k : Fin 9) (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.cos (angleVec (pad12 z) k)) y) (L2CosAAt x k) x := by
  have h1 : (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.cos (angleVec (pad12 z) k)) y)
      = fun y : Fin 7 → ℝ => (-(Real.sin (angleVec (pad12 y) k))) • daCLM k := by
    funext y
    exact ((hasFDerivAt_angleVec_any k y).cos).fderiv
  rw [h1, L2CosAAt]
  have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (daCLM k))
    (x := -(Real.sin (angleVec (pad12 x) k)))).comp x ((hasFDerivAt_angleVec_any k x).sin.neg)
  have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (daCLM k)) ∘
        (-(fun x : Fin 7 → ℝ => Real.sin (angleVec (pad12 x) k))))
      = fun y : Fin 7 → ℝ => (-(Real.sin (angleVec (pad12 y) k))) • daCLM k := by
    funext y
    rw [Function.comp_apply, Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [he] at h
  rw [← neg_smul] at h
  exact h

theorem cosA2_single_any (k : Fin 9) (i j : Fin 7) (x : Fin 7 → ℝ) :
    ((L2CosAAt x k) (Pi.single j 1)) (Pi.single i 1)
      = -(Real.cos (angleVec (pad12 x) k)) * (dAngle k i : ℝ) * (dAngle k j : ℝ) := by
  rw [L2CosAAt]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, daCLM_apply_single]
  ring

/-! ## 2. `W_k`（系数 `coord 6` + `daCLM`） -/

def L2WfunAt (x : Fin 7 → ℝ) (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.toSpanSingleton ℝ (coord 6)).comp ((2 : ℝ) • coord 6))
    - ((2 * Real.sin (angleVec (pad12 x) k))
        • ((ContinuousLinearMap.toSpanSingleton ℝ (daCLM k)).comp
            ((-(Real.sin (angleVec (pad12 x) k))) • daCLM k))
      + (((2 : ℝ) • ((Real.cos (angleVec (pad12 x) k)) • daCLM k)).smulRight
          ((Real.cos (angleVec (pad12 x) k)) • daCLM k)))

theorem hasFDerivAt_fderiv_Wfun_any (k : Fin 9) (x : Fin 7 → ℝ) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (Wfun k) z) (L2WfunAt x k) x := by
  have he : (fun z : Fin 7 → ℝ => fderiv ℝ (Wfun k) z) = dWfun k := by
    funext z
    exact (hasFDerivAt_Wfun k z).fderiv
  rw [he, L2WfunAt]
  have hA : HasFDerivAt (fun z : Fin 7 → ℝ => (2 * z 6) • coord 6)
      ((ContinuousLinearMap.toSpanSingleton ℝ (coord 6)).comp ((2 : ℝ) • coord 6)) x := by
    have h2 : HasFDerivAt (fun z : Fin 7 → ℝ => 2 * z 6) ((2 : ℝ) • coord 6) x :=
      (ContinuousLinearMap.hasFDerivAt (f := (2 : ℝ) • coord 6) (x := x)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => by rfl)
    exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (coord 6))
      (x := 2 * x 6)).comp x h2
  have hBd : HasFDerivAt
      (fun z : Fin 7 → ℝ => (Real.cos (angleVec (pad12 z) k)) • daCLM k)
      ((ContinuousLinearMap.toSpanSingleton ℝ (daCLM k)).comp
        ((-(Real.sin (angleVec (pad12 x) k))) • daCLM k)) x := by
    have hc : HasFDerivAt (fun z : Fin 7 → ℝ => Real.cos (angleVec (pad12 z) k))
        ((-(Real.sin (angleVec (pad12 x) k))) • daCLM k) x :=
      (hasFDerivAt_angleVec_any k x).cos
    exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (daCLM k))
      (x := Real.cos (angleVec (pad12 x) k))).comp x hc
  have hs : HasFDerivAt (fun z : Fin 7 → ℝ => 2 * Real.sin (angleVec (pad12 z) k))
      ((2 : ℝ) • ((Real.cos (angleVec (pad12 x) k)) • daCLM k)) x :=
    ((hasFDerivAt_angleVec_any k x).sin).const_mul (2 : ℝ)
  have hB : HasFDerivAt
      (fun z : Fin 7 → ℝ => (2 * Real.sin (angleVec (pad12 z) k))
        • ((Real.cos (angleVec (pad12 z) k)) • daCLM k))
      ((2 * Real.sin (angleVec (pad12 x) k))
          • ((ContinuousLinearMap.toSpanSingleton ℝ (daCLM k)).comp
              ((-(Real.sin (angleVec (pad12 x) k))) • daCLM k))
        + (((2 : ℝ) • ((Real.cos (angleVec (pad12 x) k)) • daCLM k)).smulRight
            ((Real.cos (angleVec (pad12 x) k)) • daCLM k))) x :=
    hs.smul hBd
  exact hA.sub hB

/-- `∂²W_k/∂z_i∂z_j` 的**一般点实数形态**（`W2R` 的 `x` 版 ✓；`W2RAt u0 = W2R` 为 `rfl` ✓）。 -/
def W2RAt (x : Fin 7 → ℝ) (k : Fin 9) (i j : Fin 7) : ℝ :=
  2 * (if i = 6 then 1 else 0) * (if j = 6 then 1 else 0)
    - 2 * (Real.cos (angleVec (pad12 x) k) ^ 2 - Real.sin (angleVec (pad12 x) k) ^ 2)
        * (dAngle k i : ℝ) * (dAngle k j : ℝ)

theorem Wfun2_single_any (k : Fin 9) (i j : Fin 7) (x : Fin 7 → ℝ) :
    (L2WfunAt x k (Pi.single j 1)) (Pi.single i 1) = W2RAt x k i j := by
  rw [W2RAt, L2WfunAt]
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, coord_six_apply_single, daCLM_apply_single]
  ring

/-- `x := u0` 时与根内 `W2R` **定义级**相同 ✓（⇒ 真推广）。 -/
theorem W2RAt_u0 (k : Fin 9) (i j : Fin 7) : W2RAt u0 k i j = W2R k i j := rfl

/-- `∂W_k/∂z_i` 的**一般点**取值形态（`dWfun_single` 的 `x` 版 ✓）。 -/
theorem dWfun_single_any (k : Fin 9) (i : Fin 7) (x : Fin 7 → ℝ) :
    (dWfun k x) (Pi.single i 1)
      = 2 * x 6 * (if i = 6 then 1 else 0)
        - 2 * Real.sin (angleVec (pad12 x) k)
            * ((Real.cos (angleVec (pad12 x) k)) * (dAngle k i : ℝ)) := by
  simp only [dWfun, sub_apply, smul_apply, smul_eq_mul, coord_six_apply_single,
    daCLM_apply_single]

/-! ## 2′. **一般点的通用二阶规则**（根内那两条把 `u0` 写进了**语句** ✗ ⇒ 在此重述为 `x` 版 ✓；
    证明**逐字**照抄（其证明本身是点通用的 ✓），只把 `u0` 换成 `x` ✓） -/

theorem hasFDerivAt_fderiv_comp_scalar_any {g : (Fin 7 → ℝ) → ℝ} {g1 : (Fin 7 → ℝ) →L[ℝ] ℝ}
    {g2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} {u : ℝ → ℝ} {u1 : ℝ →L[ℝ] ℝ}
    {x : Fin 7 → ℝ}
    (hg : HasFDerivAt g g1 x) (hg2 : HasFDerivAt (fun z => fderiv ℝ g z) g2 x)
    (hu2 : HasFDerivAt (fun t => deriv u t) u1 (g x))
    (hgd : ∀ᶠ z in nhds x, DifferentiableAt ℝ g z)
    (hud : ∀ᶠ z in nhds x, DifferentiableAt ℝ u (g z)) :
    HasFDerivAt (fun z => fderiv ℝ (fun z => u (g z)) z)
      ((deriv u (g x)) • g2 + (u1.comp g1).smulRight g1) x := by
  have hc : HasFDerivAt (fun z => deriv u (g z)) (u1.comp g1) x :=
    hu2.comp x hg
  have hsmul := hc.smul hg2
  rw [hg.fderiv] at hsmul
  refine hsmul.congr_of_eventuallyEq ?_
  filter_upwards [hgd, hud] with z hz1 hz2
  have hcomp : fderiv ℝ (fun z => u (g z)) z
      = (fderiv ℝ u (g z)).comp (fderiv ℝ g z) :=
    (hz2.hasFDerivAt.comp z hz1.hasFDerivAt).fderiv
  rw [hcomp]
  ext v
  have hmap := map_smul (fderiv ℝ u (g z)) ((fderiv ℝ g z) v) (1 : ℝ)
  rw [smul_eq_mul, mul_one, fderiv_apply_one_eq_deriv] at hmap
  change (fderiv ℝ u (g z)) ((fderiv ℝ g z) v) = deriv u (g z) * ((fderiv ℝ g z) v)
  exact hmap.trans (mul_comm _ _)

theorem hasFDerivAt_fderiv_sub_any {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} {x : Fin 7 → ℝ}
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 x)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 x)
    (hφd : ∀ᶠ z in nhds x, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds x, DifferentiableAt ℝ ψ z) :
    HasFDerivAt (fun z => fderiv ℝ (fun z => φ z - ψ z) z) (φ2 - ψ2) x := by
  have h : HasFDerivAt (fun z => fderiv ℝ φ z - fderiv ℝ ψ z) (φ2 - ψ2) x := hφ.sub hψ
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hφd, hψd] with z hz1 hz2
  change fderiv ℝ (φ - ψ) z = fderiv ℝ φ z - fderiv ℝ ψ z
  exact fderiv_sub hz1 hz2

theorem hasFDerivAt_fderiv_mul_scalar_any {φ ψ : (Fin 7 → ℝ) → ℝ} {φ1 ψ1 : (Fin 7 → ℝ) →L[ℝ] ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} {x : Fin 7 → ℝ}
    (hφ : HasFDerivAt φ φ1 x) (hφ2 : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 x)
    (hψ : HasFDerivAt ψ ψ1 x) (hψ2 : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 x)
    (hφd : ∀ᶠ z in nhds x, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds x, DifferentiableAt ℝ ψ z) :
    HasFDerivAt (fun z => fderiv ℝ (fun y => φ y * ψ y) z)
      ((φ x • ψ2 + φ1.smulRight ψ1) + (ψ x • φ2 + ψ1.smulRight φ1)) x := by
  have hA : HasFDerivAt (fun z : Fin 7 → ℝ => φ z • fderiv ℝ ψ z)
      (φ x • ψ2 + φ1.smulRight ψ1) x := by
    have h := hφ.smul hψ2
    rw [hψ.fderiv] at h
    exact h
  have hB : HasFDerivAt (fun z : Fin 7 → ℝ => ψ z • fderiv ℝ φ z)
      (ψ x • φ2 + ψ1.smulRight φ1) x := by
    have h := hψ.smul hφ2
    rw [hφ.fderiv] at h
    exact h
  have hsum := hA.add hB
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hφd, hψd] with z hz1 hz2
  have hcomp : fderiv ℝ (fun y => φ y * ψ y) z
      = (φ z) • (fderiv ℝ ψ z) + (ψ z) • (fderiv ℝ φ z) :=
    (hz1.hasFDerivAt.mul hz2.hasFDerivAt).fderiv
  rw [hcomp]
  rfl

/-! ## 3. `√W_k`（`comp_scalar` 实例化） -/

def L2SqrtWAt (x : Fin 7 → ℝ) (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (deriv Real.sqrt (Wfun k x)) • (L2WfunAt x k)
    + (((fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (Wfun k x)).comp (dWfun k x)).smulRight
        (dWfun k x))

theorem hasFDerivAt_fderiv_sqrtW_any (k : Fin 9) (x : Fin 7 → ℝ) (hW : 0 < Wfun k x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => Real.sqrt (Wfun k z)) z)
      (L2SqrtWAt x k) x := by
  rw [L2SqrtWAt]
  refine hasFDerivAt_fderiv_comp_scalar_any (g := Wfun k) (u := Real.sqrt)
    (hasFDerivAt_Wfun k x) (hasFDerivAt_fderiv_Wfun_any k x) ?_ ?_ ?_
  · have h0 := (hasDerivAt_deriv_sqrt hW).hasFDerivAt
    have h1 : HasFDerivAt (fun t : ℝ => deriv Real.sqrt t)
        (fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (Wfun k x)) (Wfun k x) := by
      rw [h0.fderiv]
      exact h0
    exact h1
  · exact Filter.Eventually.of_forall fun z => (hasFDerivAt_Wfun k z).differentiableAt
  · filter_upwards [(hasFDerivAt_Wfun k x).continuousAt.eventually
      (eventually_gt_nhds hW)] with z hz
    exact (Real.hasDerivAt_sqrt (ne_of_gt hz)).differentiableAt

/-- **`∂²(√W_k)` 的一般点取值形态**（`sqrtW2_single` 的 `x` 版 ✓）。 -/
theorem sqrtW2_single_any (k : Fin 9) (i j : Fin 7) (x : Fin 7 → ℝ) (hW : 0 < Wfun k x) :
    (L2SqrtWAt x k (Pi.single j 1)) (Pi.single i 1)
      = (1 / (2 * Real.sqrt (Wfun k x))) * (W2RAt x k i j)
        + ((-2) * (1 / (2 * Real.sqrt (Wfun k x))))
            * ((2 * Real.sqrt (Wfun k x)) * (2 * Real.sqrt (Wfun k x)))⁻¹
            * (2 * x 6 * (if j = 6 then 1 else 0)
                - 2 * Real.sin (angleVec (pad12 x) k)
                    * ((Real.cos (angleVec (pad12 x) k)) * (dAngle k j : ℝ)))
            * (2 * x 6 * (if i = 6 then 1 else 0)
                - 2 * Real.sin (angleVec (pad12 x) k)
                    * ((Real.cos (angleVec (pad12 x) k)) * (dAngle k i : ℝ))) := by
  rw [L2SqrtWAt]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [d2_fderivReal_apply_eq_mul_one, fderiv_apply_one_eq_deriv]
  rw [HasDerivAt.deriv (Real.hasDerivAt_sqrt (ne_of_gt hW))]
  rw [HasDerivAt.deriv (hasDerivAt_deriv_sqrt hW)]
  rw [Wfun2_single_any k i j x, dWfun_single_any k j x, dWfun_single_any k i x]
  ring

/-! ## 4. `cos θ_k` / `sin θ_k`（系数 `dthetaCLM`/`dTheta`） -/

def L2CosThetaAt (x : Fin 7 → ℝ) (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k)).comp
    (-(Real.cos (thetaOf (angleVec (pad12 x)) k) • dthetaCLM k))

def L2SinThetaAt (x : Fin 7 → ℝ) (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k)).comp
    ((-(Real.sin (thetaOf (angleVec (pad12 x)) k))) • dthetaCLM k)

theorem hasFDerivAt_fderiv_cosTheta_any (k : Fin 9) (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 z)) k)) y)
      (L2CosThetaAt x k) x := by
  have h1 : (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 z)) k)) y)
      = fun y : Fin 7 → ℝ => (-(Real.sin (thetaOf (angleVec (pad12 y)) k))) • dthetaCLM k := by
    funext y
    exact ((hasFDerivAt_thetaOf_any k y).cos).fderiv
  rw [h1, L2CosThetaAt]
  have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k))
    (x := -(Real.sin (thetaOf (angleVec (pad12 x)) k)))).comp x
    ((hasFDerivAt_thetaOf_any k x).sin.neg)
  have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k)) ∘
        (-(fun x : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 x)) k))))
      = fun y : Fin 7 → ℝ => (-(Real.sin (thetaOf (angleVec (pad12 y)) k))) • dthetaCLM k := by
    funext y
    rw [Function.comp_apply, Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [he] at h
  exact h

theorem hasFDerivAt_fderiv_sinTheta_any (k : Fin 9) (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 z)) k)) y)
      (L2SinThetaAt x k) x := by
  have h1 : (fun y : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 z)) k)) y)
      = fun y : Fin 7 → ℝ => (Real.cos (thetaOf (angleVec (pad12 y)) k)) • dthetaCLM k := by
    funext y
    exact ((hasFDerivAt_thetaOf_any k y).sin).fderiv
  rw [h1, L2SinThetaAt]
  have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k))
    (x := Real.cos (thetaOf (angleVec (pad12 x)) k))).comp x
    ((hasFDerivAt_thetaOf_any k x).cos)
  have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (dthetaCLM k)) ∘
        (fun x : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 x)) k)))
      = fun y : Fin 7 → ℝ => (Real.cos (thetaOf (angleVec (pad12 y)) k)) • dthetaCLM k := by
    funext y
    rw [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [he] at h
  exact h

theorem cosTheta2_single_any (k : Fin 9) (i j : Fin 7) (x : Fin 7 → ℝ) :
    (L2CosThetaAt x k (Pi.single j 1)) (Pi.single i 1)
      = -(Real.cos (thetaOf (angleVec (pad12 x)) k))
          * (dTheta k i : ℝ) * (dTheta k j : ℝ) := by
  rw [L2CosThetaAt]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, neg_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, dthetaCLM_apply_single]
  ring

theorem sinTheta2_single_any (k : Fin 9) (i j : Fin 7) (x : Fin 7 → ℝ) :
    (L2SinThetaAt x k (Pi.single j 1)) (Pi.single i 1)
      = -(Real.sin (thetaOf (angleVec (pad12 x)) k))
          * (dTheta k i : ℝ) * (dTheta k j : ℝ) := by
  rw [L2SinThetaAt]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, dthetaCLM_apply_single]
  ring

/-! ## 4′. `ρ_k = cos a_k − √W_k`（`sub_any` ＋ 上面两片 ✓） -/

/-- 一般点 `x` 处的 `∂²ρ_k` 算子（`L2Rho` 的 `x` 版 ✓）。 -/
def L2RhoAt (x : Fin 7 → ℝ) (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  L2CosAAt x k - L2SqrtWAt x k

theorem hasFDerivAt_fderiv_rhoF_any (k : Fin 9) (x : Fin 7 → ℝ) (hW : 0 < Wfun k x) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) z)
      (L2RhoAt x k) x := by
  have hfun : (fun z : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) z)
      = (fun z : Fin 7 → ℝ => fderiv ℝ
          (fun z : Fin 7 → ℝ => Real.cos (angleVec (pad12 z) k) - Real.sqrt (Wfun k z)) z) := by
    rw [rhoF_eq_cos_sub_sqrt]
  rw [hfun, L2RhoAt]
  refine hasFDerivAt_fderiv_sub_any (hasFDerivAt_fderiv_cosA_any k x)
    (hasFDerivAt_fderiv_sqrtW_any k x hW) ?_ ?_
  · exact Filter.Eventually.of_forall fun z =>
      ((hasFDerivAt_angleVec_any k z).cos).differentiableAt
  · filter_upwards [(hasFDerivAt_Wfun k x).continuousAt.eventually
      (eventually_gt_nhds hW)] with z hz
    exact ((Real.hasDerivAt_sqrt (ne_of_gt hz)).differentiableAt.comp z
      (hasFDerivAt_Wfun k z).differentiableAt)

/-- `∂ρ_k/∂z_i` 的一般点形态（`rho1R` 的 `x` 版 ✓）。 -/
def rho1RAt (x : Fin 7 → ℝ) (k : Fin 9) (i : Fin 7) : ℝ :=
  -(Real.sin (angleVec (pad12 x) k)) * (dAngle k i : ℝ)
    - (1 / (2 * Real.sqrt (Wfun k x))) * ((dWfun k x) (Pi.single i 1))

/-- `∂²ρ_k/∂z_i∂z_j` 的一般点形态（`rho2R` 的 `x` 版 ✓，同样**原始未归一化**）。 -/
def rho2RAt (x : Fin 7 → ℝ) (k : Fin 9) (i j : Fin 7) : ℝ :=
  -(Real.cos (angleVec (pad12 x) k) * (dAngle k i : ℝ) * (dAngle k j : ℝ))
    - (1 / (2 * Real.sqrt (Wfun k x))) * (W2RAt x k i j)
    - ((-2) * (1 / (2 * Real.sqrt (Wfun k x))))
        * ((2 * Real.sqrt (Wfun k x)) * (2 * Real.sqrt (Wfun k x)))⁻¹
        * ((dWfun k x) (Pi.single j 1) * (dWfun k x) (Pi.single i 1))

/-- **`∂²ρ_k` 的一般点取值形态**（`rho2_single` 的 `x` 版 ✓；用 `rhoF_eq_cos_sub_sqrt` 与两片闭式 ✓）。 -/
theorem rho2_single_any (k : Fin 9) (i j : Fin 7) (x : Fin 7 → ℝ) (hW : 0 < Wfun k x) :
    (L2RhoAt x k (Pi.single j 1)) (Pi.single i 1) = rho2RAt x k i j := by
  rw [L2RhoAt, sub_apply, sub_apply, cosA2_single_any k i j x, sqrtW2_single_any k i j x hW]
  unfold rho2RAt W2RAt
  rw [dWfun_single_any k j x, dWfun_single_any k i x]
  ring

/-! ## 4″. `ringC0`／`ringC1`（`ringCenter k` 的两个坐标；用根内 `drhoAt` ✓ 与 `mul_scalar_any` ✓） -/

/-- 根内 `drhoAt k x` 沿 `single i 1` 的取值 = 我层 `rho1RAt` ✓（`drhoAt` 见 `ResidualDerivJT.lean` L652 ✓）。 -/
theorem drhoAt_single_eq_rho1RAt (k : Fin 9) (i : Fin 7) (x : Fin 7 → ℝ) :
    (drhoAt k x) (Pi.single i 1) = rho1RAt x k i := by
  rw [drhoAt, rho1RAt]
  simp only [sub_apply, smul_apply, smul_eq_mul, daCLM_apply_single]

/-- 根内 `Eρ k i x`（`ResidualDerivJT.lean` L687 ✓）与我层 `rho1RAt` **同值** ✓。 -/
theorem Eρ_eq_rho1RAt (k : Fin 9) (i : Fin 7) (x : Fin 7 → ℝ) :
    Eρ k i x = rho1RAt x k i := by
  rw [Eρ]
  exact drhoAt_single_eq_rho1RAt k i x

/-- 一般点 `x` 处的 `∂²(C_{k,x})` 算子（`L2RingC0` 的 `x` 版 ✓）。 -/
def L2RingC0At (x : Fin 7 → ℝ) (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (rhoK (pad12 x) k • L2CosThetaAt x k
      + (drhoAt k x).smulRight ((-(Real.sin (thetaOf (angleVec (pad12 x)) k))) • dthetaCLM k))
    + (Real.cos (thetaOf (angleVec (pad12 x)) k) • L2RhoAt x k
      + ((-(Real.sin (thetaOf (angleVec (pad12 x)) k))) • dthetaCLM k).smulRight (drhoAt k x))

/-- 一般点 `x` 处的 `∂²(C_{k,y})` 算子（`L2RingC1` 的 `x` 版 ✓）。 -/
def L2RingC1At (x : Fin 7 → ℝ) (k : Fin 9) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (rhoK (pad12 x) k • L2SinThetaAt x k
      + (drhoAt k x).smulRight ((Real.cos (thetaOf (angleVec (pad12 x)) k)) • dthetaCLM k))
    + (Real.sin (thetaOf (angleVec (pad12 x)) k) • L2RhoAt x k
      + ((Real.cos (thetaOf (angleVec (pad12 x)) k)) • dthetaCLM k).smulRight (drhoAt k x))

theorem hasFDerivAt_fderiv_ringC0_any (k : Fin 9) (x : Fin 7 → ℝ) (hW : 0 < Wfun k x) :
    HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0) z)
      (L2RingC0At x k) x := by
  have hφ : HasFDerivAt (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) (drhoAt k x) x :=
    hasFDerivAt_rhoK_any k x (ne_of_gt hW)
  have hψ : HasFDerivAt (fun z : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 z)) k))
      ((-(Real.sin (thetaOf (angleVec (pad12 x)) k))) • dthetaCLM k) x :=
    (hasFDerivAt_thetaOf_any k x).cos
  have hφd : ∀ᶠ z in nhds x,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) z := by
    filter_upwards [(hasFDerivAt_Wfun k x).continuousAt.eventually
      (eventually_gt_nhds hW)] with z hz
    exact (hasFDerivAt_rhoK_any k z (ne_of_gt hz)).differentiableAt
  have hψd : ∀ᶠ z in nhds x,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => Real.cos (thetaOf (angleVec (pad12 z)) k)) z :=
    Filter.Eventually.of_forall fun z => ((hasFDerivAt_thetaOf_any k z).cos).differentiableAt
  have h := hasFDerivAt_fderiv_mul_scalar_any hφ (hasFDerivAt_fderiv_rhoF_any k x hW) hψ
    (hasFDerivAt_fderiv_cosTheta_any k x) hφd hψd
  have hfun : (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0)
      = (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.cos (thetaOf (angleVec (pad12 z)) k)) := by
    funext z
    rw [ringCenter_coord0]
  have hfun2 : (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 0) z)
      = (fun z : Fin 7 → ℝ => fderiv ℝ
          (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.cos (thetaOf (angleVec (pad12 z)) k)) z) := by
    rw [hfun]
  rw [hfun2, L2RingC0At]
  exact h

theorem hasFDerivAt_fderiv_ringC1_any (k : Fin 9) (x : Fin 7 → ℝ) (hW : 0 < Wfun k x) :
    HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1) z)
      (L2RingC1At x k) x := by
  have hφ : HasFDerivAt (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) (drhoAt k x) x :=
    hasFDerivAt_rhoK_any k x (ne_of_gt hW)
  have hψ : HasFDerivAt (fun z : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 z)) k))
      ((Real.cos (thetaOf (angleVec (pad12 x)) k)) • dthetaCLM k) x :=
    (hasFDerivAt_thetaOf_any k x).sin
  have hφd : ∀ᶠ z in nhds x,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => rhoK (pad12 z) k) z := by
    filter_upwards [(hasFDerivAt_Wfun k x).continuousAt.eventually
      (eventually_gt_nhds hW)] with z hz
    exact (hasFDerivAt_rhoK_any k z (ne_of_gt hz)).differentiableAt
  have hψd : ∀ᶠ z in nhds x,
      DifferentiableAt ℝ (fun z : Fin 7 → ℝ => Real.sin (thetaOf (angleVec (pad12 z)) k)) z :=
    Filter.Eventually.of_forall fun z => ((hasFDerivAt_thetaOf_any k z).sin).differentiableAt
  have h := hasFDerivAt_fderiv_mul_scalar_any hφ (hasFDerivAt_fderiv_rhoF_any k x hW) hψ
    (hasFDerivAt_fderiv_sinTheta_any k x) hφd hψd
  have hfun : (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1)
      = (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.sin (thetaOf (angleVec (pad12 z)) k)) := by
    funext z
    rw [ringCenter_coord1]
  have hfun2 : (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp 1) z)
      = (fun z : Fin 7 → ℝ => fderiv ℝ
          (fun z : Fin 7 → ℝ => rhoK (pad12 z) k * Real.sin (thetaOf (angleVec (pad12 z)) k)) z) := by
    rw [hfun]
  rw [hfun2, L2RingC1At]
  exact h

theorem ringC0_2_single_any (k : Fin 9) (i j : Fin 7) (x : Fin 7 → ℝ) (hW : 0 < Wfun k x) :
    (L2RingC0At x k (Pi.single j 1)) (Pi.single i 1)
      = rho2RAt x k i j * Real.cos (thetaOf (angleVec (pad12 x)) k)
        - rho1RAt x k i * Real.sin (thetaOf (angleVec (pad12 x)) k) * (dTheta k j : ℝ)
        - rho1RAt x k j * Real.sin (thetaOf (angleVec (pad12 x)) k) * (dTheta k i : ℝ)
        - rhoK (pad12 x) k * Real.cos (thetaOf (angleVec (pad12 x)) k)
            * (dTheta k i : ℝ) * (dTheta k j : ℝ) := by
  rw [L2RingC0At]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    dthetaCLM_apply_single]
  rw [cosTheta2_single_any k i j x, rho2_single_any k i j x hW,
    drhoAt_single_eq_rho1RAt k i x, drhoAt_single_eq_rho1RAt k j x]
  ring

theorem ringC1_2_single_any (k : Fin 9) (i j : Fin 7) (x : Fin 7 → ℝ) (hW : 0 < Wfun k x) :
    (L2RingC1At x k (Pi.single j 1)) (Pi.single i 1)
      = rho2RAt x k i j * Real.sin (thetaOf (angleVec (pad12 x)) k)
        + rho1RAt x k i * Real.cos (thetaOf (angleVec (pad12 x)) k) * (dTheta k j : ℝ)
        + rho1RAt x k j * Real.cos (thetaOf (angleVec (pad12 x)) k) * (dTheta k i : ℝ)
        - rhoK (pad12 x) k * Real.sin (thetaOf (angleVec (pad12 x)) k)
            * (dTheta k i : ℝ) * (dTheta k j : ℝ) := by
  rw [L2RingC1At]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    dthetaCLM_apply_single]
  rw [sinTheta2_single_any k i j x, rho2_single_any k i j x hW,
    drhoAt_single_eq_rho1RAt k i x, drhoAt_single_eq_rho1RAt k j x]
  ring

/-! ## 4‴. `arcEnd`（`ArcC`；**(B) 前置 ①** ✓）—— 根内 `secondPartial_ArcC`（`ResidualDerivJT.lean` L774）的 `x` 版 -/

/-- 一般点 `x` 处的 `∂²(ArcC k c)` 算子（`c=0`/`c=1` 两支合一；逐字照 `secondPartial_ArcC` 的两支 ✓）。 -/
def L2ArcAt (x : Fin 7 → ℝ) (k : Fin 9) (c : Fin 2) :
    (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  if c = 0 then
    (ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)).comp
      (-(Real.cos (phiA k x) • phiCLM k))
  else
    (ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)).comp
      ((-(Real.sin (phiA k x))) • phiCLM k)

theorem hasFDerivAt_fderiv_ArcC_any (k : Fin 9) (c : Fin 2) (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ (ArcC k c) y) (L2ArcAt x k c) x := by
  by_cases hc0 : c = 0
  · subst hc0
    have h1 : (fun y : Fin 7 → ℝ => fderiv ℝ (ArcC k 0) y)
        = fun y : Fin 7 → ℝ => (-(Real.sin (phiA k y))) • phiCLM k := by
      funext y
      exact fderiv_ArcC_zero k y
    rw [h1, L2ArcAt, if_pos rfl]
    have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k))
      (x := -(Real.sin (phiA k x)))).comp x ((hasFDerivAt_phiA k x).sin.neg)
    have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)) ∘
          (-(fun x : Fin 7 → ℝ => Real.sin (phiA k x))))
        = fun y : Fin 7 → ℝ => (-(Real.sin (phiA k y))) • phiCLM k := by
      funext y
      rw [Function.comp_apply, Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply]
    rw [he] at h
    exact h
  · have hc1 : c = 1 := by fin_cases c <;> simp_all
    subst hc1
    have h1 : (fun y : Fin 7 → ℝ => fderiv ℝ (ArcC k 1) y)
        = fun y : Fin 7 → ℝ => (Real.cos (phiA k y)) • phiCLM k := by
      funext y
      exact fderiv_ArcC_one k y
    rw [h1, L2ArcAt, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k))
      (x := Real.cos (phiA k x))).comp x (hasFDerivAt_phiA k x).cos
    have he : (⇑(ContinuousLinearMap.toSpanSingleton ℝ (phiCLM k)) ∘
          (fun x : Fin 7 → ℝ => Real.cos (phiA k x)))
        = fun y : Fin 7 → ℝ => (Real.cos (phiA k y)) • phiCLM k := by
      funext y
      rw [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
    rw [he] at h
    exact h

/-- **`arcEnd` 二阶偏导的一般点形态**（`secondPartial_ArcC` 的 `x` 版 ✓；形状与 `hessEntryAt` 内层同 ✓）。 -/
theorem secondPartial_ArcC_any (k : Fin 9) (c : Fin 2) (i j : Fin 7) (x : Fin 7 → ℝ) :
    ((fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ (ArcC k c) y) x) (Pi.single j 1)) (Pi.single i 1)
      = -(if c = 0 then Real.cos (phiA k x) else Real.sin (phiA k x))
        * ((dTheta k i : ℝ) + (dAngle k i : ℝ)) * ((dTheta k j : ℝ) + (dAngle k j : ℝ)) := by
  by_cases hc0 : c = 0
  · subst hc0
    rw [(hasFDerivAt_fderiv_ArcC_any k 0 x).fderiv]
    rw [L2ArcAt, if_pos rfl]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_apply, smul_eq_mul, neg_apply, phiCLM, add_apply, dthetaCLM_apply_single,
      daCLM_apply_single, if_true]
    ring
  · have hc1 : c = 1 := by fin_cases c <;> simp_all
    subst hc1
    rw [(hasFDerivAt_fderiv_ArcC_any k 1 x).fderiv]
    rw [L2ArcAt, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_apply, smul_eq_mul, phiCLM, add_apply, dthetaCLM_apply_single,
      daCLM_apply_single, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    ring

/-! ## 4⁗. `wPoint.y`（`√Wpf`；**(B) 前置 ②** ✓）—— `L2Wy`（`D2Leaves.lean` L536）的 `x` 版
⚠ 本片**零件特简**：`Wpf z = (z 6)² − ((z 5 − z 4)/2)²` 是**多项式** ⇒ `L2Wpf`（L470）与 `Wp2R`（L514）**与 `u0` 无关** ✓✓
   ⇒ 我**直接用**它们（无需 `_At` 版 ✓），只需把 `Wp1R`（L508）与 `wy2R`（L559）参数化 ✓ -/

theorem hasFDerivAt_fderiv_Wpf_any (x : Fin 7 → ℝ) :
    HasFDerivAt (fun z : Fin 7 → ℝ => fderiv ℝ Wpf z) (L2Wpf) x := by
  have he : (fun z : Fin 7 → ℝ => fderiv ℝ Wpf z) = dWpfAt := by
    funext z
    exact (hasFDerivAt_Wpf_any z).fderiv
  rw [he, L2Wpf]
  have hA : HasFDerivAt (fun z : Fin 7 → ℝ => (2 * z 6) • coord 6)
      ((ContinuousLinearMap.toSpanSingleton ℝ (coord 6)).comp ((2 : ℝ) • coord 6)) x := by
    have h2 : HasFDerivAt (fun z : Fin 7 → ℝ => 2 * z 6) ((2 : ℝ) • coord 6) x :=
      (ContinuousLinearMap.hasFDerivAt (f := (2 : ℝ) • coord 6) (x := x)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => by rfl)
    exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (coord 6))
      (x := 2 * x 6)).comp x h2
  have hm0 : HasFDerivAt (fun z : Fin 7 → ℝ => (z 5 - z 4) / 2)
      ((1 / 2 : ℝ) • (coord 5 - coord 4)) x := by
    have he2 : (fun z : Fin 7 → ℝ => (z 5 - z 4) / 2) = fun z => (1 / 2 : ℝ) * (z 5 - z 4) := by
      funext z
      ring
    rw [he2]
    exact ((ContinuousLinearMap.hasFDerivAt (f := coord 5) (x := x)).sub
      (ContinuousLinearMap.hasFDerivAt (f := coord 4) (x := x))).const_mul (1 / 2)
  have hm : HasFDerivAt (fun z : Fin 7 → ℝ => 2 * ((z 5 - z 4) / 2))
      ((2 : ℝ) • ((1 / 2 : ℝ) • (coord 5 - coord 4))) x := hm0.const_mul 2
  have hB : HasFDerivAt
      (fun z : Fin 7 → ℝ => (2 * ((z 5 - z 4) / 2)) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))
      ((ContinuousLinearMap.toSpanSingleton ℝ ((1 / 2 : ℝ) • (coord 5 - coord 4))).comp
        ((2 : ℝ) • ((1 / 2 : ℝ) • (coord 5 - coord 4)))) x :=
    (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.toSpanSingleton ℝ ((1 / 2 : ℝ) • (coord 5 - coord 4)))
      (x := 2 * ((x 5 - x 4) / 2))).comp x hm
  exact hA.sub hB

/-- `∂Wp/∂z_i` 的一般点形态（`Wp1R` 的 `x` 版 ✓）。 -/
def Wp1RAt (x : Fin 7 → ℝ) (i : Fin 7) : ℝ :=
  2 * x 6 * (if i = 6 then 1 else 0)
    - (2 * ((x 5 - x 4) / 2))
        * ((1 / 2 : ℝ) * ((if i = 5 then 1 else 0) - (if i = 4 then 1 else 0)))

theorem dWpf_single_any (i : Fin 7) (x : Fin 7 → ℝ) :
    (dWpfAt x) (Pi.single i 1) = Wp1RAt x i := by
  rw [dWpfAt, Wp1RAt]
  simp only [sub_apply, smul_apply, smul_eq_mul, coord_apply_single]

def L2WyAt (x : Fin 7 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ) :=
  (deriv Real.sqrt (Wpf x)) • L2Wpf
    + (((fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (Wpf x)).comp (dWpfAt x)).smulRight
        (dWpfAt x))

theorem hasFDerivAt_fderiv_wyF_any (x : Fin 7 → ℝ) (hWp : 0 < Wpf x) :
    HasFDerivAt (fun z : Fin 7 → ℝ =>
        fderiv ℝ (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1) z) (L2WyAt x) x := by
  rw [wpF_eq_sqrt, L2WyAt]
  refine hasFDerivAt_fderiv_comp_scalar_any (g := Wpf) (u := Real.sqrt)
    (hasFDerivAt_Wpf_any x) (hasFDerivAt_fderiv_Wpf_any x) ?_ ?_ ?_
  · have h0 := (hasDerivAt_deriv_sqrt hWp).hasFDerivAt
    have h1 : HasFDerivAt (fun t : ℝ => deriv Real.sqrt t)
        (fderiv ℝ (fun t : ℝ => deriv Real.sqrt t) (Wpf x)) (Wpf x) := by
      rw [h0.fderiv]
      exact h0
    exact h1
  · exact Filter.Eventually.of_forall fun z => (hasFDerivAt_Wpf_any z).differentiableAt
  · filter_upwards [(hasFDerivAt_Wpf_any x).continuousAt.eventually
      (eventually_gt_nhds hWp)] with z hz
    exact (Real.hasDerivAt_sqrt (ne_of_gt hz)).differentiableAt

/-- `∂²(√Wp)` 的一般点实数值形态（`wy2R` 的 `x` 版 ✓；`Wp2R` 与 `u0` 无关 ⇒ 直接用 ✓）。 -/
def wy2RAt (x : Fin 7 → ℝ) (i j : Fin 7) : ℝ :=
  (1 / (2 * Real.sqrt (Wpf x))) * (Wp2R i j)
    + ((-2) * (1 / (2 * Real.sqrt (Wpf x))))
        * ((2 * Real.sqrt (Wpf x)) * (2 * Real.sqrt (Wpf x)))⁻¹
        * (Wp1RAt x j * Wp1RAt x i)

theorem wy2_single_any (i j : Fin 7) (x : Fin 7 → ℝ) (hWp : 0 < Wpf x) :
    (L2WyAt x (Pi.single j 1)) (Pi.single i 1) = wy2RAt x i j := by
  rw [L2WyAt]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [d2_fderivReal_apply_eq_mul_one, fderiv_apply_one_eq_deriv]
  rw [HasDerivAt.deriv (Real.hasDerivAt_sqrt (ne_of_gt hWp))]
  rw [HasDerivAt.deriv (hasDerivAt_deriv_sqrt hWp)]
  rw [Wpf2_single i j, dWpf_single_any j x, dWpf_single_any i x]
  unfold wy2RAt Wp1RAt
  ring

/-! ## 6. **(B) 盒叶层 · 第一片（最小可判）**：基盒提升 `pad12Box` ＋ 逐槽桥 ＋ 首个叶实例

**形状（`hess-seam` 的靶文本 ✓，量词/求值**同空间** ✓）**：
```lean
theorem d2xIvBox_mem (k : Fin 5) (i j : Fin 7) {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) :
    (d2xIvBox Q k i j).Mem
      (secondPartial (fun w : Fin 7 → ℝ => ((Apt k) (pad12 w)).ofLp 0 - ((Bpt k) (pad12 w)).ofLp 0) z i j)
```
⇒ 我按此铺：**族对 `Q : Fin 7 → RatInterval` 泛型** ✓（更可复用 ✓；`Lead` 的 `Q0` 实例 = `pad12Box (u0 ± ρ 盒)` ✓ 二者**同一个盒** ✓）。

**为什么要换基盒** ✗✓（实测）：`pad12` 把 7..11 号坐标置 **0** ✓，而 `ndBox` 在那几位是**证书尺度**盒（中心 ≈ −0.1138、宽 ~ρ ⇒ **不含 0** ✗），
`pad12 u0 ≠ cCertR` ✗ ⇒ `z ↦ pad12 z` 的球提升**为假** ✗；**真正需要的是反向投影** `first7`（1-Lipschitz ✓）—— 那一步归 `hess-seam` ✓。
我这里只做：**盒提升 `pad12Box`（7..11 槽取 `[0,0]` ✓，更紧）+ 逐槽桥** ✓。
-/

/-- **盒提升**：`Fin 7` 盒 ⇒ `Fin 12` 盒（前 7 位照抄 ✓；后 5 位取**单点 `0`** ✓，因 `pad12` 把它们置 0 ✓）。 -/
def pad12Box (Q : Fin 7 → RatInterval) : Fin 12 → RatInterval :=
  fun i => if h : (i : ℕ) < 7 then Q ⟨(i : ℕ), h⟩ else ⟨0, 0⟩

theorem pad12Box_lt (Q : Fin 7 → RatInterval) (i : Fin 12) (h : (i : ℕ) < 7) :
    pad12Box Q i = Q ⟨(i : ℕ), h⟩ := by
  rw [pad12Box, dif_pos h]

theorem pad12Box_ge (Q : Fin 7 → RatInterval) (i : Fin 12) (h : ¬ (i : ℕ) < 7) :
    pad12Box Q i = ⟨0, 0⟩ := by
  rw [pad12Box, dif_neg h]

theorem pad12_apply_lt (z : Fin 7 → ℝ) (i : Fin 12) (h : (i : ℕ) < 7) :
    pad12 z i = z ⟨(i : ℕ), h⟩ := by
  rw [pad12, dif_pos h]

theorem pad12_apply_ge (z : Fin 7 → ℝ) (i : Fin 12) (h : ¬ (i : ℕ) < 7) :
    pad12 z i = 0 := by
  rw [pad12, dif_neg h]

/-- **逐槽桥（= 球提升的替代 ✓）**：`z` 逐坐标落在 `Q` 里 ⇒ `pad12 z` 逐坐标落在 `pad12Box Q` 里 ✓。 -/
theorem pad12Box_mem_pad12 {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) :
    ∀ i : Fin 12, (pad12Box Q i).Mem (pad12 z i) := by
  intro i
  by_cases h : (i : ℕ) < 7
  · rw [pad12Box_lt Q i h, pad12_apply_lt z i h]
    exact hz ⟨(i : ℕ), h⟩
  · rw [pad12Box_ge Q i h, pad12_apply_ge z i h]
    have h0 : (⟨0, 0⟩ : RatInterval) = ofRat (0 : ℚ) := rfl
    rw [h0]
    simpa using ofRat_mem (0 : ℚ)

/-- **首个叶实例**（验证全路线 ✓）：`cos(θ_k + a_k)` 的盒叶在**被求值点 `pad12 z`** 处 ✓
（= 根内 `cosTAIv`（`ResidualDerivD.lean` L79 ✓）的形状，只把 `cCert` 换成 `pad12Box Q`、把 `u0` 换成 `z` ✓）。 -/
theorem cosTotLag_theta_add_angle_mem (k : Fin 9) {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) :
    (cosTotLag (add (thetaInterval (ndAngleBox (pad12Box Q)) k)
        (ndAngleBox (pad12Box Q) k))).Mem
      (Real.cos (thetaOf (angleVec (pad12 z)) k + angleVec (pad12 z) k)) :=
  cosTotLag_mem (add_mem (thetaInterval_mem (ndAngleBox_mem (pad12Box_mem_pad12 hz)) k)
    (ndAngleBox_mem (pad12Box_mem_pad12 hz) k))

/-! ## 7. **(B) 第二片：`W` 族盒叶（`rho2IvBox` 的料 ✓）**

三个叶：`wkBoxQ`（= 根内 `wkBox` 的 `Q` 泛型版 ✓）、`W2RAtBox`（`∂²W/∂z_i∂z_j` ✓ 用我 (A) 层的 `W2RAt` ✓）、
`WkD1AtBox`（`∂W/∂z_i` ✓ 用 `dWfun_single_any` 的闭式 ✓）。全部以 `pad12 z` 为被求值点 ✓。 -/

/-- `W_k` 的盒叶（根内 `F1/BallD35Hrad.wkBox` 的 `Q` 泛型版 ✓）。 -/
def wkBoxQ (Q : Fin 7 → RatInterval) (j : Fin 9) : RatInterval :=
  sub (sq (Q 6)) (sq (sinTotLag (ndAngleBox (pad12Box Q) j)))

theorem wkBoxQ_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (j : Fin 9) :
    (wkBoxQ Q j).Mem (pad12 z 6 * pad12 z 6
      - Real.sin (angleVec (pad12 z) j) * Real.sin (angleVec (pad12 z) j)) := by
  rw [wkBoxQ]
  exact sub_mem (sq_mem (pad12Box_mem_pad12 hz 6)) (sq_mem (sinTotLag_mem (ndAngleBox_mem
    (pad12Box_mem_pad12 hz) j)))

/-- `∂²W_k/∂z_i∂z_j` 的盒叶（用 (A) 层 `W2RAt` 的闭式 ✓；树形与 `W2RAt` 的**解析嵌套**逐字对齐 ✓）。 -/
def W2RAtBox (Q : Fin 7 → RatInterval) (k : Fin 9) (i j : Fin 7) : RatInterval :=
  sub
    (mul (mul (ofRat 2) (ofRat (if i = 6 then 1 else 0))) (ofRat (if j = 6 then 1 else 0)))
    (mul
      (mul (mul (ofRat 2) (sub (sq (cosTotLag (ndAngleBox (pad12Box Q) k)))
        (sq (sinTotLag (ndAngleBox (pad12Box Q) k)))))
        (ofRat (dAngle k i)))
      (ofRat (dAngle k j)))

/-- `ofRat` 的**显式接口**（口径：定义 vs 字面量做成显式引理 ✓，避免 `simpa` 在 `ite`/cast 上失败 ✗）。 -/
theorem ofRat_two_mem : (ofRat (2 : ℚ)).Mem (2 : ℝ) := by simpa using ofRat_mem (2 : ℚ)

/-- **一般 `ite` 指标接口** ✓（我原来的 `ofRat_delta_mem` 把 `i = 6` **写死了** ✗ ⇒ 供不了 `i=5`/`i=4` 的格 ✗✓）。 -/
theorem ofRat_ite_mem (i j : Fin 7) :
    (ofRat (if i = j then (1 : ℚ) else 0)).Mem ((if i = j then 1 else 0 : ℝ)) := by
  by_cases h : i = j
  · simp only [h, if_true]
    simpa using ofRat_mem (1 : ℚ)
  · simp only [h, if_false]
    simpa using ofRat_mem (0 : ℚ)

theorem ofRat_delta_mem (i : Fin 7) :
    (ofRat (if i = 6 then (1 : ℚ) else 0)).Mem ((if i = 6 then 1 else 0 : ℝ)) := by
  by_cases hi : i = 6
  · simp only [hi, if_true]
    simpa using ofRat_mem (1 : ℚ)
  · simp only [hi, if_false]
    simpa using ofRat_mem (0 : ℚ)

theorem ofRat_dAngle_mem (k : Fin 9) (i : Fin 7) :
    (ofRat ((dAngle k i : ℤ) : ℚ)).Mem ((dAngle k i : ℝ)) := by
  simpa using ofRat_mem ((dAngle k i : ℤ) : ℚ)

theorem ofRat_dTheta_mem (k : Fin 9) (i : Fin 7) :
    (ofRat ((dTheta k i : ℤ) : ℚ)).Mem ((dTheta k i : ℝ)) := by
  simpa using ofRat_mem ((dTheta k i : ℤ) : ℚ)

theorem W2RAtBox_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (k : Fin 9) (i j : Fin 7) :
    (W2RAtBox Q k i j).Mem (W2RAt z k i j) := by
  rw [W2RAtBox, W2RAt]
  refine sub_mem
    (mul_mem (mul_mem ofRat_two_mem (ofRat_delta_mem i)) (ofRat_delta_mem j)) ?_
  refine mul_mem (mul_mem (mul_mem ofRat_two_mem (sub_mem
    (sq_mem_pow (cosTotLag_mem (ndAngleBox_mem (pad12Box_mem_pad12 hz) k)))
    (sq_mem_pow (sinTotLag_mem (ndAngleBox_mem (pad12Box_mem_pad12 hz) k)))))
    (ofRat_dAngle_mem k i)) (ofRat_dAngle_mem k j)

/-- `∂W_k/∂z_i` 的盒叶（用 `dWfun_single_any` 的闭式 ✓，被求值点 `z` ✓）。 -/
def WkD1AtBox (Q : Fin 7 → RatInterval) (k : Fin 9) (i : Fin 7) : RatInterval :=
  sub
    (mul (mul (ofRat 2) (Q 6)) (ofRat (if i = 6 then 1 else 0)))
    (mul (mul (ofRat 2) (sinTotLag (ndAngleBox (pad12Box Q) k)))
      (mul (cosTotLag (ndAngleBox (pad12Box Q) k)) (ofRat (dAngle k i))))

theorem WkD1AtBox_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (k : Fin 9) (i : Fin 7) :
    (WkD1AtBox Q k i).Mem ((dWfun k z) (Pi.single i 1)) := by
  rw [WkD1AtBox, dWfun_single_any]
  refine sub_mem (mul_mem (mul_mem ofRat_two_mem (hz 6)) (ofRat_delta_mem i)) ?_
  exact mul_mem (mul_mem ofRat_two_mem
    (sinTotLag_mem (ndAngleBox_mem (pad12Box_mem_pad12 hz) k)))
    (mul_mem (cosTotLag_mem (ndAngleBox_mem (pad12Box_mem_pad12 hz) k))
      (ofRat_dAngle_mem k i))

/-! ## 8. **(B) 第三片：`rho2IvBox`（`∂²ρ_k/∂z_i∂z_j` 的盒叶）**

**形状**：照根内 `D2Leaves.rho2Iv`（L674 ✓）逐字搬，u0 叶全换成 `Q` 泛型盒叶 ✓；
`Mem` 目标 = 我 (A) 层的 **`rho2RAt z k i j`** ✓（缝处由 `ringC0_2_single_any` 一族接到 `secondPartial` ✓）。

**§8 修法（Lead 批准 ✓，与根内 `rho2Iv_mem` 同法）**：`hw`/`h3` 的 RHS 与 `rho2RAt` **同形**（用 `Real.sqrt (Wfun k z)` ✓，
   不写展开形 ✗ —— `Wfun k x := (x 6)^2 − (sin (angleVec (pad12 x) k))^2`（`ResidualDerivJT.lean` L607 ✓））；
   叶的目标走**显式桥** `WkBoxQ_value`（`^2` 形 ⇄ `*` 形 ⇒ defeq 不同形 ✗ ⇒ 做接口 ✓，口径 (d)/§51(3) 同族）。
**具名假设**：`hz : ∀ i, (Q i).Mem (z i)`（见证点 ✓）＋ `hW : 0 < (wkBoxQ Q k).lo`（泛型 `Q` 无全局正性 ✗ ⇒ 当假设 ✓）。
**本片对一般 `k,i,j` 成立** ✓（证明与格无关 ⇒ **不逐格** ✓）。 -/

theorem wkBoxQ_valid {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (j : Fin 9) : Valid (wkBoxQ Q j) :=
  valid_of_mem (wkBoxQ_mem hz j)

/-- **`Wfun` 展开桥**（`^2` 形 ⇄ `*` 形，`rfl` 级不同形 ⇒ 显式接口 ✓）。 -/
theorem WkBoxQ_value (k : Fin 9) (z : Fin 7 → ℝ) :
    pad12 z 6 * pad12 z 6
        - Real.sin (angleVec (pad12 z) k) * Real.sin (angleVec (pad12 z) k)
      = Wfun k z := by
  rw [Wfun, pad12_six]
  ring

def twoSqrtWkIvBoxQ (Q : Fin 7 → RatInterval) (j : Fin 9) : RatInterval :=
  mul (ofRat 2) ((wkBoxQ Q j).sqrt)

theorem twoSqrtWkIvBoxQ_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (j : Fin 9) :
    (twoSqrtWkIvBoxQ Q j).Mem (2 * Real.sqrt (Wfun j z)) := by
  rw [twoSqrtWkIvBoxQ]
  have h := mul_mem ofRat_two_mem (sqrt_mem (wkBoxQ_mem hz j))
  simpa only [WkBoxQ_value j z] using h

theorem twoSqrtWkIvBoxQ_pos (Q : Fin 7 → RatInterval) (k : Fin 9)
    (hW : 0 < (wkBoxQ Q k).lo) (kV : Valid (wkBoxQ Q k)) :
    0 < (twoSqrtWkIvBoxQ Q k).lo :=
  twoMulIv_pos (wkBoxQ Q k).sqrt (sqrtLo_pos hW) (RatInterval.sqrt_valid kV)

def invSq2SqrtWkIvQ (Q : Fin 7 → RatInterval) (k : Fin 9) : RatInterval :=
  invPos (sq (twoSqrtWkIvBoxQ Q k))

theorem invSq2SqrtWkIvQ_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (k : Fin 9) (hW : 0 < (wkBoxQ Q k).lo) :
    (invSq2SqrtWkIvQ Q k).Mem
      (((2 * Real.sqrt (Wfun k z)) * (2 * Real.sqrt (Wfun k z)))⁻¹) := by
  rw [invSq2SqrtWkIvQ]
  exact invPos_mem (sq_mem (twoSqrtWkIvBoxQ_mem hz k))
    (sq_pos (twoSqrtWkIvBoxQ Q k)
      (twoSqrtWkIvBoxQ_pos Q k hW (wkBoxQ_valid hz k)))

/-- **`∂²ρ_k/∂z_i∂z_j` 的盒叶**（= 根内 `rho2Iv` 的 `Q` 泛型版 ✓；一般 `k,i,j` ✓）。 -/
def rho2IvBox (Q : Fin 7 → RatInterval) (k : Fin 9) (i j : Fin 7) : RatInterval :=
  sub
    (sub (neg (mul (mul (cosTotLag (ndAngleBox (pad12Box Q) k)) (ofRat (dAngle k i)))
        (ofRat (dAngle k j))))
      (mul (invPos (twoSqrtWkIvBoxQ Q k)) (W2RAtBox Q k i j)))
    (mul (mul (mul (ofRat (-2)) (invPos (twoSqrtWkIvBoxQ Q k))) (invSq2SqrtWkIvQ Q k))
      (mul (WkD1AtBox Q k j) (WkD1AtBox Q k i)))

theorem rho2IvBox_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (k : Fin 9) (i j : Fin 7) (hW : 0 < (wkBoxQ Q k).lo) :
    (rho2IvBox Q k i j).Mem (rho2RAt z k i j) := by
  have h2 : 0 < (twoSqrtWkIvBoxQ Q k).lo :=
    twoSqrtWkIvBoxQ_pos Q k hW (wkBoxQ_valid hz k)
  have hc : (cosTotLag (ndAngleBox (pad12Box Q) k)).Mem (Real.cos (angleVec (pad12 z) k)) :=
    cosTotLag_mem (ndAngleBox_mem (pad12Box_mem_pad12 hz) k)
  have hnk : (neg (mul (mul (cosTotLag (ndAngleBox (pad12Box Q) k)) (ofRat (dAngle k i)))
      (ofRat (dAngle k j)))).Mem
      (-(Real.cos (angleVec (pad12 z) k) * (dAngle k i : ℝ) * (dAngle k j : ℝ))) := by
    refine neg_mem ?_
    have h := mul_mem (mul_mem hc (ofRat_dAngle_mem k i)) (ofRat_dAngle_mem k j)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hw : (mul (invPos (twoSqrtWkIvBoxQ Q k)) (W2RAtBox Q k i j)).Mem
      ((1 / (2 * Real.sqrt (Wfun k z))) * (W2RAt z k i j)) :=
    mul_mem (invPos_mem_div (twoSqrtWkIvBoxQ_mem hz k) h2) (W2RAtBox_mem hz k i j)
  have h3 : (mul (mul (mul (ofRat (-2)) (invPos (twoSqrtWkIvBoxQ Q k))) (invSq2SqrtWkIvQ Q k))
      (mul (WkD1AtBox Q k j) (WkD1AtBox Q k i))).Mem
      (((-2) * (1 / (2 * Real.sqrt (Wfun k z))))
        * ((2 * Real.sqrt (Wfun k z)) * (2 * Real.sqrt (Wfun k z)))⁻¹
        * ((dWfun k z) (Pi.single j 1) * (dWfun k z) (Pi.single i 1))) := by
    refine mul_mem (mul_mem (mul_mem (by simpa using ofRat_mem ((-2 : ℤ) : ℚ))
      (invPos_mem_div (twoSqrtWkIvBoxQ_mem hz k) h2))
      (invSq2SqrtWkIvQ_mem hz k hW)) ?_
    exact mul_mem (WkD1AtBox_mem hz k j) (WkD1AtBox_mem hz k i)
  rw [rho2IvBox, rho2RAt]
  refine sub_mem (sub_mem ?_ ?_) ?_
  · simpa [mul_comm, mul_left_comm, mul_assoc] using hnk
  · simpa [mul_comm, mul_left_comm, mul_assoc] using hw
  · simpa [mul_comm, mul_left_comm, mul_assoc] using h3

/-! ## 9. **(B) 第四片：`arc2Box`（`∂²(arcEnd)/∂z_i∂z_j` 的盒叶）**

照根内 `ResidualDerivJT.mem_arc2`（L834 ✓）逐字搬：u0 叶 `cosTAIv`/`sinTAIv` 换成**盒版** `ndArcBox (pad12Box Q) k c` ✓
（已核 ✓：`ndArcBox Q k 0 = cosTotLag (add (thetaInterval (ndAngleBox Q) k) (ndAngleBox Q k))` ✓ = `cosTAIv` 的盒版 ✓，`NondegProof` L171 ✓）；
`Mem` 目标 = 我 (A) 层 `secondPartial_ArcC_any` 的右端 ✓。 -/

/-- `∂²(arcEnd k c)/∂z_i∂z_j` 的盒叶（= 根内 `arc2` 的 `Q` 泛型版 ✓；一般 `k,c,i,j` ✓）。 -/
def arc2Box (Q : Fin 7 → RatInterval) (k : Fin 9) (c : Fin 2) (i j : Fin 7) : RatInterval :=
  neg (mul (mul (ofRat (((dTheta k i + dAngle k i : ℤ) : ℚ)))
      (ofRat (((dTheta k j + dAngle k j : ℤ) : ℚ))))
    (ndArcBox (pad12Box Q) k c))

theorem arc2Box_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (k : Fin 9) (c : Fin 2) (i j : Fin 7) :
    (arc2Box Q k c i j).Mem
      (-(if c = 0 then Real.cos (phiA k z) else Real.sin (phiA k z))
        * ((dTheta k i : ℝ) + (dAngle k i : ℝ))
        * ((dTheta k j : ℝ) + (dAngle k j : ℝ))) := by
  by_cases hc0 : c = 0
  · subst hc0
    have h := neg_mem (mul_mem (mul_mem
      (ofRat_mem (((dTheta k i + dAngle k i : ℤ) : ℚ)))
      (ofRat_mem (((dTheta k j + dAngle k j : ℤ) : ℚ))))
      (ndArcBox_mem (pad12Box_mem_pad12 hz) k 0))
    simpa [arc2Box, if_true, phiA, arcEnd_coord0, RatInterval.ofRat, push_cast, mul_comm,
      mul_left_comm, mul_assoc] using h
  · have hc1 : c = 1 := by fin_cases c <;> simp_all
    subst hc1
    have h := neg_mem (mul_mem (mul_mem
      (ofRat_mem (((dTheta k i + dAngle k i : ℤ) : ℚ)))
      (ofRat_mem (((dTheta k j + dAngle k j : ℤ) : ℚ))))
      (ndArcBox_mem (pad12Box_mem_pad12 hz) k 1))
    simpa [arc2Box, if_neg (by decide : ¬ ((1 : Fin 2) = 0)), phiA, arcEnd_coord1,
      RatInterval.ofRat, push_cast, mul_comm, mul_left_comm, mul_assoc] using h

/-! ## 10. **(B) 第五片：`Wy2Box`（`∂²√Wp/∂z_i∂z_j` 的盒叶；`wPoint` 系 ✓）**

照根内 `D2Leaves` 的 `WpiIv` L806／`WpijIv` L812／`invSq2SqrtWpIv` L818／`Wy2` L869 ✓ 逐字搬，u0 叶换 `Q` 泛型 ✓；
`Mem` 目标 = 我 (A) 层的 **`wy2RAt z i j`** ✓。⚠ `Wpf z = (z 6)² − ((z 5 − z 4)/2)²`（`D2Leaves.lean` L440 ✓）⇒ **`/2` ⇄ `*(1/2)` 形式桥** ✓（与上族同坑 ✓）。
**具名假设** ✓：`hz`；`hWp : 0 < (WpIvBoxQ Q).lo`；`kV : Valid (WpIvBoxQ Q)`（泛型 `Q` 无全局正性/有效性 ✗ ⇒ 当假设 ✓）。 -/

/-- `Wp` 的盒叶（= `Wpf z` ✓；`/2` 用 `*(1/2)` 表 ✓）。 -/
def WpIvBoxQ (Q : Fin 7 → RatInterval) : RatInterval :=
  sub (sq (Q 6)) (sq (mul (sub (Q 5) (Q 4)) (ofRat (1 / 2))))

theorem WpIvBoxQ_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) : (WpIvBoxQ Q).Mem (Wpf z) := by
  rw [WpIvBoxQ, Wpf]
  refine sub_mem (sq_mem_pow (hz 6)) ?_
  refine sq_mem_pow ?_
  have hhalf : (ofRat (1 / 2 : ℚ)).Mem ((1 / 2 : ℝ)) := by
    simpa using ofRat_mem (1 / 2 : ℚ)
  have h := mul_mem (sub_mem (hz 5) (hz 4)) hhalf
  simpa [div_eq_mul_inv, mul_comm] using h

/-- `∂Wp/∂z_i` 的盒叶（= 根内 `WpiIv`（L806 ✓）的 `Q` 泛型版 ✓）。 -/
def WpiIvBox (Q : Fin 7 → RatInterval) (i : Fin 7) : RatInterval :=
  sub
    (mul (mul (ofRat 2) (Q 6)) (ofRat (if i = 6 then 1 else 0)))
    (mul (mul (mul (ofRat 2) (sub (Q 5) (Q 4))) (ofRat (1 / 2)))
      (mul (ofRat (1 / 2)) (sub (ofRat (if i = 5 then 1 else 0))
        (ofRat (if i = 4 then 1 else 0)))))

theorem WpiIvBox_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (i : Fin 7) :
    (WpiIvBox Q i).Mem (Wp1RAt z i) := by
  have hhalf : (ofRat (1 / 2 : ℚ)).Mem ((1 / 2 : ℝ)) := by
    simpa using ofRat_mem (1 / 2 : ℚ)
  rw [WpiIvBox, Wp1RAt]
  refine sub_mem ?_ ?_
  · have h := mul_mem (mul_mem ofRat_two_mem (hz 6)) (ofRat_delta_mem i)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  · have h := mul_mem (mul_mem (mul_mem ofRat_two_mem (sub_mem (hz 5) (hz 4))) hhalf)
      (mul_mem hhalf (sub_mem (ofRat_ite_mem i 5) (ofRat_ite_mem i 4)))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- `∂²Wp/∂z_i∂z_j` 的盒叶（= 根内 `WpijIv`（L812 ✓）的版本 ✓；`Wp2R` 与 `u0` 无关 ✓）。 -/
def WpijIvBox (i j : Fin 7) : RatInterval :=
  sub
    (mul (mul (ofRat 2) (ofRat (if i = 6 then 1 else 0)))
      (ofRat (if j = 6 then 1 else 0)))
    (mul (mul (mul (ofRat 2) (mul (ofRat (1 / 2)) (sub (ofRat (if i = 5 then 1 else 0))
        (ofRat (if i = 4 then 1 else 0))))) (ofRat (1 / 2)))
      (sub (ofRat (if j = 5 then 1 else 0)) (ofRat (if j = 4 then 1 else 0))))

theorem WpijIvBox_mem (i j : Fin 7) : (WpijIvBox i j).Mem (Wp2R i j) := by
  have hhalf : (ofRat (1 / 2 : ℚ)).Mem ((1 / 2 : ℝ)) := by
    simpa using ofRat_mem (1 / 2 : ℚ)
  rw [WpijIvBox, Wp2R]
  refine sub_mem ?_ ?_
  · have h := mul_mem (mul_mem ofRat_two_mem (ofRat_delta_mem i)) (ofRat_delta_mem j)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  · have h := mul_mem (mul_mem (mul_mem ofRat_two_mem (mul_mem hhalf
      (sub_mem (ofRat_ite_mem i 5) (ofRat_ite_mem i 4)))) hhalf)
      (sub_mem (ofRat_ite_mem j 5) (ofRat_ite_mem j 4))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

def twoSqrtWpIvBoxQ (Q : Fin 7 → RatInterval) : RatInterval :=
  mul (ofRat 2) ((WpIvBoxQ Q).sqrt)

theorem twoSqrtWpIvBoxQ_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) :
    (twoSqrtWpIvBoxQ Q).Mem (2 * Real.sqrt (Wpf z)) := by
  rw [twoSqrtWpIvBoxQ]
  have h := mul_mem ofRat_two_mem (sqrt_mem (WpIvBoxQ_mem hz))
  simpa using h

theorem twoSqrtWpIvBoxQ_pos (Q : Fin 7 → RatInterval)
    (hWp : 0 < (WpIvBoxQ Q).lo) (kV : Valid (WpIvBoxQ Q)) :
    0 < (twoSqrtWpIvBoxQ Q).lo :=
  twoMulIv_pos (WpIvBoxQ Q).sqrt (sqrtLo_pos hWp) (RatInterval.sqrt_valid kV)

def invSq2SqrtWpIvBoxQ (Q : Fin 7 → RatInterval) : RatInterval :=
  invPos (sq (twoSqrtWpIvBoxQ Q))

theorem invSq2SqrtWpIvBoxQ_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (hWp : 0 < (WpIvBoxQ Q).lo)
    (kV : Valid (WpIvBoxQ Q)) :
    (invSq2SqrtWpIvBoxQ Q).Mem
      (((2 * Real.sqrt (Wpf z)) * (2 * Real.sqrt (Wpf z)))⁻¹) := by
  rw [invSq2SqrtWpIvBoxQ]
  exact invPos_mem (sq_mem (twoSqrtWpIvBoxQ_mem hz))
    (sq_pos (twoSqrtWpIvBoxQ Q) (twoSqrtWpIvBoxQ_pos Q hWp kV))

/-- **`∂²(√Wp)/∂z_i∂z_j` 的盒叶**（= 根内 `Wy2`（L869 ✓）的 `Q` 泛型版 ✓；一般 `i,j` ✓）。 -/
def Wy2Box (Q : Fin 7 → RatInterval) (i j : Fin 7) : RatInterval :=
  add (mul (invPos (twoSqrtWpIvBoxQ Q)) (WpijIvBox i j))
    (mul (mul (mul (ofRat (-2)) (invPos (twoSqrtWpIvBoxQ Q))) (invSq2SqrtWpIvBoxQ Q))
      (mul (WpiIvBox Q j) (WpiIvBox Q i)))

theorem Wy2Box_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (i j : Fin 7) (hWp : 0 < (WpIvBoxQ Q).lo)
    (kV : Valid (WpIvBoxQ Q)) :
    (Wy2Box Q i j).Mem (wy2RAt z i j) := by
  have h2 : 0 < (twoSqrtWpIvBoxQ Q).lo := twoSqrtWpIvBoxQ_pos Q hWp kV
  have hp := twoSqrtWpIvBoxQ_mem hz
  have h1 : (mul (invPos (twoSqrtWpIvBoxQ Q)) (WpijIvBox i j)).Mem
      ((1 / (2 * Real.sqrt (Wpf z))) * (Wp2R i j)) :=
    mul_mem (invPos_mem_div hp h2) (WpijIvBox_mem i j)
  have h3 : (mul (mul (mul (ofRat (-2)) (invPos (twoSqrtWpIvBoxQ Q))) (invSq2SqrtWpIvBoxQ Q))
      (mul (WpiIvBox Q j) (WpiIvBox Q i))).Mem
      (((-2) * (1 / (2 * Real.sqrt (Wpf z))))
        * ((2 * Real.sqrt (Wpf z)) * (2 * Real.sqrt (Wpf z)))⁻¹
        * (Wp1RAt z j * Wp1RAt z i)) := by
    refine mul_mem (mul_mem (mul_mem (by simpa using ofRat_mem ((-2 : ℤ) : ℚ))
      (invPos_mem_div hp h2)) (invSq2SqrtWpIvBoxQ_mem hz hWp kV)) ?_
    exact mul_mem (WpiIvBox_mem hz j) (WpiIvBox_mem hz i)
  rw [Wy2Box, wy2RAt]
  refine add_mem ?_ ?_
  · simpa [mul_comm, mul_left_comm, mul_assoc] using h1
  · simpa [mul_comm, mul_left_comm, mul_assoc] using h3

/-! ## 11. **(B) 第六片：`ring2Box`**（6 族最后一族；照 NOTES §17.2 ✓）

照根内 `D2Leaves.ring2`（L752 ✓）逐字搬；u0 叶换 `Q` 泛型：`rho2Iv`→`rho2IvBox` ✓｜`rhoIv`→`ndRhoBox (pad12Box Q) k` ✓｜
`cosTIv`/`sinTIv`→`cosTotLag`/`sinTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)` ✓
（⚠ **已核** ✓：`thetaInterval_mem` 给的是**单形** `thetaOf (angleVec ·) k` ✓ —— 因 `ndArcBox` 是 `add (thetaInterval …) (ndAngleBox …)` ✓
 ⇒ 我的靶用**单形** ✓，**无需**迁靶 ✓）｜`drhoIv`→新叶 `rho1AtBox` ✓。
`Mem` 目标 = `ringC2RAt`（`ringC2R` L708 的 `u0 → z` 版 ✓）。
**§17.1(ii) 修法** ✓：`dTheta k i * dTheta k j` 的乘积格加 `push_cast` 进 `simpa` 集 ✓，且**不带 `only`** ✓。 -/

/-- `∂ρ_k/∂z_i` 的盒叶（= `rho1RAt z k i` ✓）。 -/
def rho1AtBox (Q : Fin 7 → RatInterval) (k : Fin 9) (i : Fin 7) : RatInterval :=
  sub
    (neg (mul (sinTotLag (ndAngleBox (pad12Box Q) k)) (ofRat (dAngle k i))))
    (mul (invPos (twoSqrtWkIvBoxQ Q k)) (WkD1AtBox Q k i))

theorem rho1AtBox_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (k : Fin 9) (i : Fin 7) (hW : 0 < (wkBoxQ Q k).lo) :
    (rho1AtBox Q k i).Mem (rho1RAt z k i) := by
  have h2 : 0 < (twoSqrtWkIvBoxQ Q k).lo :=
    twoSqrtWkIvBoxQ_pos Q k hW (wkBoxQ_valid hz k)
  have hs : (sinTotLag (ndAngleBox (pad12Box Q) k)).Mem (Real.sin (angleVec (pad12 z) k)) :=
    sinTotLag_mem (ndAngleBox_mem (pad12Box_mem_pad12 hz) k)
  rw [rho1AtBox, rho1RAt]
  refine sub_mem ?_ ?_
  · have h := neg_mem (mul_mem hs (ofRat_dAngle_mem k i))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  · have h := mul_mem (invPos_mem_div (twoSqrtWkIvBoxQ_mem hz k) h2) (WkD1AtBox_mem hz k i)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- `ringC2R` 的一般点版（`u0 → z` ✓）。 -/
def ringC2RAt (z : Fin 7 → ℝ) (k : Fin 9) (c : Fin 2) (i j : Fin 7) : ℝ :=
  if c = 0 then
    rho2RAt z k i j * Real.cos (thetaOf (angleVec (pad12 z)) k)
      - rho1RAt z k i * Real.sin (thetaOf (angleVec (pad12 z)) k) * (dTheta k j : ℝ)
      - rho1RAt z k j * Real.sin (thetaOf (angleVec (pad12 z)) k) * (dTheta k i : ℝ)
      - rhoK (pad12 z) k * Real.cos (thetaOf (angleVec (pad12 z)) k)
          * (dTheta k i : ℝ) * (dTheta k j : ℝ)
  else
    rho2RAt z k i j * Real.sin (thetaOf (angleVec (pad12 z)) k)
      + rho1RAt z k i * Real.cos (thetaOf (angleVec (pad12 z)) k) * (dTheta k j : ℝ)
      + rho1RAt z k j * Real.cos (thetaOf (angleVec (pad12 z)) k) * (dTheta k i : ℝ)
      - rhoK (pad12 z) k * Real.sin (thetaOf (angleVec (pad12 z)) k)
          * (dTheta k i : ℝ) * (dTheta k j : ℝ)

/-- **`∂²(ringCenter k c)/∂z_i∂z_j` 的盒叶**（= 根内 `ring2`（L752 ✓）的 `Q` 泛型版 ✓；一般 `k,c,i,j` ✓）。 -/
def ring2Box (Q : Fin 7 → RatInterval) (k : Fin 9) (c : Fin 2) (i j : Fin 7) : RatInterval :=
  if c = 0 then
    sub (sub (sub (mul (rho2IvBox Q k i j)
              (cosTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)))
              (mul (mul (rho1AtBox Q k i)
                (sinTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)))
                (ofRat (dTheta k j))))
            (mul (mul (rho1AtBox Q k j)
              (sinTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)))
              (ofRat (dTheta k i))))
      (mul (mul (ndRhoBox (pad12Box Q) k)
        (cosTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)))
        (ofRat (dTheta k i * dTheta k j)))
  else
    sub (add (add (mul (rho2IvBox Q k i j)
              (sinTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)))
              (mul (mul (rho1AtBox Q k i)
                (cosTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)))
                (ofRat (dTheta k j))))
            (mul (mul (rho1AtBox Q k j)
              (cosTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)))
              (ofRat (dTheta k i))))
      (mul (mul (ndRhoBox (pad12Box Q) k)
        (sinTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)))
        (ofRat (dTheta k i * dTheta k j)))

theorem ring2Box_mem {Q : Fin 7 → RatInterval} {z : Fin 7 → ℝ}
    (hz : ∀ i, (Q i).Mem (z i)) (k : Fin 9) (c : Fin 2) (i j : Fin 7)
    (hW : 0 < (wkBoxQ Q k).lo) :
    (ring2Box Q k c i j).Mem (ringC2RAt z k c i j) := by
  have hc0 : (cosTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)).Mem
      (Real.cos (thetaOf (angleVec (pad12 z)) k)) :=
    cosTotLag_mem (thetaInterval_mem (ndAngleBox_mem (pad12Box_mem_pad12 hz)) k)
  have hs0 : (sinTotLag (thetaInterval (ndAngleBox (pad12Box Q)) k)).Mem
      (Real.sin (thetaOf (angleVec (pad12 z)) k)) :=
    sinTotLag_mem (thetaInterval_mem (ndAngleBox_mem (pad12Box_mem_pad12 hz)) k)
  have hr : (ndRhoBox (pad12Box Q) k).Mem (rhoK (pad12 z) k) :=
    ndRhoBox_mem (pad12Box_mem_pad12 hz) k
  have h2 := rho2IvBox_mem hz k i j hW
  have h1i := rho1AtBox_mem hz k i hW
  have h1j := rho1AtBox_mem hz k j hW
  have hdd : (ofRat (((dTheta k i * dTheta k j : ℤ) : ℚ))).Mem
      ((dTheta k i : ℝ) * (dTheta k j : ℝ)) := by
    have h := ofRat_mem (((dTheta k i * dTheta k j : ℤ) : ℚ))
    simpa [push_cast] using h
  by_cases hc : c = 0
  · subst hc
    rw [ring2Box, if_pos rfl, ringC2RAt]
    simp only [if_true]
    refine sub_mem (sub_mem (sub_mem ?_ ?_) ?_) ?_
    · have h := mul_mem h2 hc0
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    · have h := mul_mem (mul_mem h1i hs0) (ofRat_dTheta_mem k j)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    · have h := mul_mem (mul_mem h1j hs0) (ofRat_dTheta_mem k i)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    · have h := mul_mem (mul_mem hr hc0) hdd
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
  · have hc1 : c = 1 := by fin_cases c <;> simp_all
    subst hc1
    rw [ring2Box, if_neg (by decide : ¬ ((1 : Fin 2) = 0)), ringC2RAt]
    simp only [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    refine sub_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · have h := mul_mem h2 hs0
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    · have h := mul_mem (mul_mem h1i hc0) (ofRat_dTheta_mem k j)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    · have h := mul_mem (mul_mem h1j hc0) (ofRat_dTheta_mem k i)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    · have h := mul_mem (mul_mem hr hs0) hdd
      simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-! ## 12. **段 1（甲′）· 首批**：`secondPartial_*` 的 `_any` 重述（**`hub` 零项 ＋ `arcEnd` 桥** ✓）

**核名册已做** ✓（口径第 20 条，根内 `ResidualDerivJTHess.lean`）：
`secondPartial_eq_of_hasFDerivAt`（L86 ✓ **带 `x` ⇒ 一般点 ✓**）｜`secondPartial_const`（L105 ✓ 一般点 ✓）｜`secondPartial_coord`（L115 ✓ 一般点 ✓）
⇒ 故 `hub*` 的 `_any` 版**近乎免费** ✓（逐字 `u0 → x` ✓，照根内 L388–394 的写法 ✓）。
用到的**点恒等式**（u0-无关 ✓）：`hub0_coord0`／`hub0_coord1`（`SourceIdentity` ✓）＋ `pad12_four` ✓。 -/

theorem secondPartial_hub0_coord0_any (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0) x i j = 0 := by
  have hfun : (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 0) = fun z => coord 4 z := by
    funext z
    exact (hub0_coord0 (pad12 z)).trans (pad12_four z)
  rw [hfun]
  exact secondPartial_coord 4 x i j

theorem secondPartial_hub0_coord1_any (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1) x i j = 0 := by
  have hfun : (fun z : Fin 7 → ℝ => (hub0 (pad12 z)).ofLp 1) = fun _ => (0 : ℝ) := by
    funext z
    rw [hub0_coord1]
  rw [hfun]
  exact secondPartial_const 0 x i j

/-- `arcEnd` 分量二阶的 `secondPartial` 版（一般点 ✓；由 L86 的桥 ＋ (A) 层 `secondPartial_ArcC_any` ✓）。 -/
theorem secondPartial_arcEnd_any (k : Fin 9) (c : Fin 2) (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (ArcC k c) x i j
      = -(if c = 0 then Real.cos (phiA k x) else Real.sin (phiA k x))
        * ((dTheta k i : ℝ) + (dAngle k i : ℝ))
        * ((dTheta k j : ℝ) + (dAngle k j : ℝ)) := by
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_ArcC_any k c x) i j]
  simpa [(hasFDerivAt_fderiv_ArcC_any k c x).fderiv] using secondPartial_ArcC_any k c i j x

/-! ## 12′. **段 1 · 第二批**：(A) `hub1` 两条 ＋ (B) `add` 的 `_any` ＋ (C) `secondPartial_{add,sub}_any` ＋ (D) `Uvec_coord_any`

全部**逐字 `u0 → x`** ✓（模板已在根内逐行核过 ✓）：
(A) 点恒等式 `hub1_coord0 → coord 5`（`pad12_five` ✓）／`hub1_coord1 → 0` ✓（根内 L404–418 ✓）
(B) `hasFDerivAt_fderiv_add`（根内 L215–226 ✓，证明**点通用** ✓）
(C) `secondPartial_{add,sub}`（根内 L314–336 ✓）
(D) `secondPartial_Uvec_coord`（根内 L346–377 ✓；尾两步 = L376–377 的两次 `rw` ✓；`Uvec_coord0/1` 是**点恒等式** ⇒ u0-无关 ✓）
⇒ **全程不用 `simpa only`** ✓（§55）。 -/

theorem secondPartial_hub1_coord0_any (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0) x i j = 0 := by
  have hfun : (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 0) = fun z => coord 5 z := by
    funext z
    exact (hub1_coord0 (pad12 z)).trans (pad12_five z)
  rw [hfun]
  exact secondPartial_coord 5 x i j

theorem secondPartial_hub1_coord1_any (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1) x i j = 0 := by
  have hfun : (fun z : Fin 7 → ℝ => (hub1 (pad12 z)).ofLp 1) = fun _ => (0 : ℝ) := by
    funext z
    rw [hub1_coord1]
  rw [hfun]
  exact secondPartial_const 0 x i j

theorem hasFDerivAt_fderiv_add_any {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 x)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 x)
    (hφd : ∀ᶠ z in nhds x, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds x, DifferentiableAt ℝ ψ z) :
    HasFDerivAt (fun z => fderiv ℝ (fun z => φ z + ψ z) z) (φ2 + ψ2) x := by
  have h : HasFDerivAt (fun z => fderiv ℝ φ z + fderiv ℝ ψ z) (φ2 + ψ2) x := hφ.add hψ
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hφd, hψd] with z hz1 hz2
  change fderiv ℝ (φ + ψ) z = fderiv ℝ φ z + fderiv ℝ ψ z
  exact fderiv_add hz1 hz2

theorem secondPartial_add_any {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 x)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 x)
    (hφd : ∀ᶠ z in nhds x, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds x, DifferentiableAt ℝ ψ z) (i j : Fin 7) :
    secondPartial (fun z => φ z + ψ z) x i j
      = secondPartial φ x i j + secondPartial ψ x i j := by
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_add_any hφ hψ hφd hψd),
    secondPartial_eq_of_hasFDerivAt hφ, secondPartial_eq_of_hasFDerivAt hψ]
  exact add_apply _ _ _

theorem secondPartial_sub_any {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 x)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 x)
    (hφd : ∀ᶠ z in nhds x, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds x, DifferentiableAt ℝ ψ z) (i j : Fin 7) :
    secondPartial (fun z => φ z - ψ z) x i j
      = secondPartial φ x i j - secondPartial ψ x i j := by
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_sub_any hφ hψ hφd hψd),
    secondPartial_eq_of_hasFDerivAt hφ, secondPartial_eq_of_hasFDerivAt hψ]
  exact sub_apply _ _ _

theorem secondPartial_Uvec_coord_any (s : Fin 9) (c : Fin 2) (x : Fin 7 → ℝ) (i j : Fin 7)
    {C2 C2' A2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)}
    (hC : HasFDerivAt (fun z => fderiv ℝ (fun z => (ringCenter (pad12 z) s).ofLp c) z) C2 x)
    (hC' : HasFDerivAt (fun z => fderiv ℝ (fun z => (ringCenter (pad12 z) (s + 1)).ofLp c) z) C2' x)
    (hA : HasFDerivAt (fun z => fderiv ℝ (fun z => (arcEnd (pad12 z) s).ofLp c) z) A2 x)
    (hCd : ∀ᶠ z in nhds x, DifferentiableAt ℝ (fun z => (ringCenter (pad12 z) s).ofLp c) z)
    (hC'd : ∀ᶠ z in nhds x, DifferentiableAt ℝ (fun z => (ringCenter (pad12 z) (s + 1)).ofLp c) z)
    (hAd : ∀ᶠ z in nhds x, DifferentiableAt ℝ (fun z => (arcEnd (pad12 z) s).ofLp c) z) :
    secondPartial (fun z => (Uvec (pad12 z) s).ofLp c) x i j
      = secondPartial (fun z => (ringCenter (pad12 z) s).ofLp c) x i j
        + secondPartial (fun z => (ringCenter (pad12 z) (s + 1)).ofLp c) x i j
        - secondPartial (fun z => (arcEnd (pad12 z) s).ofLp c) x i j := by
  have hcmp : ∀ z : Fin 7 → ℝ, (Uvec (pad12 z) s).ofLp c
      = (ringCenter (pad12 z) s).ofLp c + (ringCenter (pad12 z) (s + 1)).ofLp c
        - (arcEnd (pad12 z) s).ofLp c := by
    intro z
    fin_cases c
    · exact Uvec_coord0 (pad12 z) s
    · exact Uvec_coord1 (pad12 z) s
  have e1 : (fun z : Fin 7 → ℝ => (Uvec (pad12 z) s).ofLp c)
      = fun z : Fin 7 → ℝ => ((ringCenter (pad12 z) s).ofLp c
          + (ringCenter (pad12 z) (s + 1)).ofLp c) - (arcEnd (pad12 z) s).ofLp c :=
    funext hcmp
  rw [e1]
  have hsum2 : HasFDerivAt (fun z => fderiv ℝ (fun z : Fin 7 → ℝ =>
        (ringCenter (pad12 z) s).ofLp c + (ringCenter (pad12 z) (s + 1)).ofLp c) z)
      (C2 + C2') x :=
    hasFDerivAt_fderiv_add_any hC hC' hCd hC'd
  have hsumd : ∀ᶠ z in nhds x, DifferentiableAt ℝ (fun z : Fin 7 → ℝ =>
        (ringCenter (pad12 z) s).ofLp c + (ringCenter (pad12 z) (s + 1)).ofLp c) z :=
    (hCd.and hC'd).mono fun z hz => hz.1.add hz.2
  rw [secondPartial_sub_any hsum2 hA hsumd hAd]
  rw [secondPartial_add_any hC hC' hCd hC'd]

/-! ## 12″. **段 1 · 第三批 (E)**：`secondPartial_ringC_any`（两分支 ✓，照 `D2Leaves.secondPartial_ringC` L723 ✓）

用**同一条桥** ✓（`secondPartial_eq_of_hasFDerivAt`（L86 ✓，带 `x` ✓）＋ `simpa [(…).fderiv]`（**不带 `only`** ✓））＋ 我 (A) 层的
`ringC0_2_single_any`／`ringC1_2_single_any`（均带 `hW : 0 < Wfun k x` ✓）。 -/

theorem secondPartial_ringC_any (k : Fin 9) (c : Fin 2) (x : Fin 7 → ℝ)
    (hW : 0 < Wfun k x) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (ringCenter (pad12 z) k).ofLp c) x i j
      = ringC2RAt x k c i j := by
  by_cases hc : c = 0
  · subst hc
    rw [ringC2RAt, if_pos rfl]
    rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_ringC0_any k x hW) i j]
    simpa [(hasFDerivAt_fderiv_ringC0_any k x hW).fderiv] using ringC0_2_single_any k i j x hW
  · have hc1 : c = 1 := by fin_cases c <;> simp_all
    subst hc1
    rw [ringC2RAt, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
    rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_ringC1_any k x hW) i j]
    simpa [(hasFDerivAt_fderiv_ringC1_any k x hW).fderiv] using ringC1_2_single_any k i j x hW

/-! ## 13. **段 2 · 第一步（零风险）**：`d2xIvBox`／`d2yIvBox` 的**定义**（把区间表达式形状钉死 ✓）

照根内 `D2Leaves.d2xIv`（L1280 ✓）／`d2yIv`（L1286 ✓）**逐字搬** ✓：`k = 4` 走 `wPoint`/`ringCenter 6` 支 ✓；
`k = 0..3` 走 `Uvec`/`hub` 支（`hub` 二阶为 0 ⇒ 尾项 `ofRat 0` ✓）；`resSlot : Fin 5 → Fin 9`（`ResidualDerivD.lean` L266 ✓）。
⇒ 本步**只落定义**（照根内自己的做法 ✓："把区间表达式形状钉死" ✓）；`_mem` 见下一批 ✓。 -/

/-- **`Δ` 的二阶 x 分量（盒级、`Q` 泛型 ✓）**。 -/
def d2xIvBox (Q : Fin 7 → RatInterval) (k : Fin 5) (i j : Fin 7) : RatInterval :=
  if k = 4 then neg (ring2Box Q 6 0 i j)
  else sub (sub (add (ring2Box Q (resSlot k) 0 i j) (ring2Box Q ((resSlot k) + 1) 0 i j))
      (arc2Box Q (resSlot k) 0 i j)) (ofRat 0)

/-- **`Δ` 的二阶 y 分量（盒级、`Q` 泛型 ✓）**。 -/
def d2yIvBox (Q : Fin 7 → RatInterval) (k : Fin 5) (i j : Fin 7) : RatInterval :=
  if k = 4 then sub (Wy2Box Q i j) (ring2Box Q 6 1 i j)
  else sub (sub (add (ring2Box Q (resSlot k) 1 i j) (ring2Box Q ((resSlot k) + 1) 1 i j))
      (arc2Box Q (resSlot k) 1 i j)) (ofRat 0)

/-! ## 14. **批 1**：`secondPartial_wx_any`／`wy_any`（`wPoint` 两坐标的二阶；`k = 4` 支要用的最后两片 ✓）

逐字 `u0 → x` ✓（根内 `secondPartial_wxF` L578–591 ✓ ／ `secondPartial_wyF` L746–749 ✓）：
`wPoint` 的 x 坐标 = `(1/2) • (coord 4 + coord 5)`（仿射 ✓ ⇒ 二阶 0 ✓，用 `wPoint_coord0` ＋ `pad12_four/five` ＋ `ring` ✓ 得 _fun 等式，再 `← hclm` ＋ `secondPartial_clm` ✓）；
而 `secondPartial_clm`（`ResidualDerivJTHess` L422 ✓）**本就是一般点** ✓ ⇒ x 片**零新料** ✓；
y 坐标走**那条桥** ✓（L86 ＋ `simpa [(…).fderiv]`，**不带 `only`** ✓）＋ 我 (A) 层 `wy2RAt`／`wy2_single_any`／`hasFDerivAt_fderiv_wyF_any` ✓（= **前置 ②** ✓）。 -/

/-- `wPoint` 的 **x** 坐标二阶（一般点 ✓；恒 0 —— 它是仿射的 ✓）。 -/
theorem secondPartial_wx_any (x : Fin 7 → ℝ) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 0) x i j = 0 := by
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
  exact secondPartial_clm ((1 / 2 : ℝ) • (coord 4 + coord 5)) x i j

/-- `wPoint` 的 **y** 坐标二阶（一般点 ✓；= `wy2RAt x i j` ✓）。 -/
theorem secondPartial_wy_any (x : Fin 7 → ℝ) (hWp : 0 < Wpf x) (i j : Fin 7) :
    secondPartial (fun z : Fin 7 → ℝ => (wPoint (pad12 z)).ofLp 1) x i j = wy2RAt x i j := by
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_wyF_any x hWp) i j]
  simpa [(hasFDerivAt_fderiv_wyF_any x hWp).fderiv] using wy2_single_any i j x hWp

/-! ## 15. **层 1**（甲⁗ ✓）：**正确入口** = `hasFDerivAt_fderiv_of_eq_clm_any`

**再根化** ✓（我上一批入口选错 ✓，如实报的 ✓）：先做**更原始**的两条（`D2Leaves` L949–957 ✓ ／ L970–976 ✓ **逐字** `u0 → x` ✓）：
**(1)** `hasFDerivAt_fderiv_clm_any` ✓（CLM 函数的 `fderiv` 恒 = `L`（`ContinuousLinearMap.hasFDerivAt … .fderiv` ✓）⇒ 导数 0（**`hasFDerivAt_const L x`** ✓））；
**(2)** `hasFDerivAt_fderiv_of_eq_clm_any` ✓（`φ = fun z => L z` ⇒ 同上 ✓：`rw [h]` ＋ (1) ✓）。
★ **正解口径** ✓（我上一批撞墙处的真解 ✓）：**别手写 `fun _ => (L : 内层类型)`** ✗ —— 用 **`hasFDerivAt_const L`**，让 Lean 推外层类型 ✓。
之后 `hub*_coord*_any`（`hub0xF_eq`／`hub1xF_eq` 是**点恒等式** ✓ u0-无关 ✓）与 `UvecC0/C1_any` 都由这两条导出 ✓。 -/

/-- CLM 函数的 `fderiv` 的导数（一般点 ✓；`D2Leaves` L950 的逐字 `u0 → x` ✓）。 -/
theorem hasFDerivAt_fderiv_clm_any (L : (Fin 7 → ℝ) →L[ℝ] ℝ) (x : Fin 7 → ℝ) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => L z) y)
      (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) x := by
  have hfun : (fun y : Fin 7 → ℝ => fderiv ℝ (fun z : Fin 7 → ℝ => L z) y) = fun _ => L := by
    funext y
    exact (ContinuousLinearMap.hasFDerivAt (f := L) (x := y)).fderiv
  rw [hfun]
  exact hasFDerivAt_const L x

/-- 与 CLM 相同的函数：`fderiv` 的导数为 0（一般点 ✓；`D2Leaves` L971 的逐字 `u0 → x` ✓）。 -/
theorem hasFDerivAt_fderiv_of_eq_clm_any {φ : (Fin 7 → ℝ) → ℝ} {L : (Fin 7 → ℝ) →L[ℝ] ℝ}
    (x : Fin 7 → ℝ) (h : φ = fun z => L z) :
    HasFDerivAt (fun y : Fin 7 → ℝ => fderiv ℝ φ y)
      (0 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)) x := by
  rw [h]
  exact hasFDerivAt_fderiv_clm_any L x

/-! ## 5. `x := u0` 的**一致性对拍**（⇒ 本层是根内那批的**真推广** ✓） -/

theorem cosA2_single_any_at_u0 (k : Fin 9) (i j : Fin 7) :
    ((L2CosAAt u0 k) (Pi.single j 1)) (Pi.single i 1)
      = -(Real.cos (angleVec (pad12 u0) k)) * (dAngle k i : ℝ) * (dAngle k j : ℝ) :=
  cosA2_single_any k i j u0

theorem Wfun2_single_any_at_u0 (k : Fin 9) (i j : Fin 7) :
    (L2WfunAt u0 k (Pi.single j 1)) (Pi.single i 1) = W2R k i j := by
  rw [Wfun2_single_any, W2RAt_u0]

theorem cosTheta2_single_any_at_u0 (k : Fin 9) (i j : Fin 7) :
    (L2CosThetaAt u0 k (Pi.single j 1)) (Pi.single i 1)
      = -(Real.cos (thetaOf (angleVec (pad12 u0)) k))
          * (dTheta k i : ℝ) * (dTheta k j : ℝ) :=
  cosTheta2_single_any k i j u0

theorem sinTheta2_single_any_at_u0 (k : Fin 9) (i j : Fin 7) :
    (L2SinThetaAt u0 k (Pi.single j 1)) (Pi.single i 1)
      = -(Real.sin (thetaOf (angleVec (pad12 u0)) k))
          * (dTheta k i : ℝ) * (dTheta k j : ℝ) :=
  sinTheta2_single_any k i j u0

end TowerBC

end N11Formalization
