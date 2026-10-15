/-
  evidence/f1-step2/F1-BallD35-C11.lean
  =====================================

  **F1 第 2 步 · 步骤 (2) 后段**：`hJ` 的 12×12 里 **(c) KKT 行 × λ 列**的**球级镜像**（一般 `x : Fin 12 → ℝ`）。

  **写法**（与 C10 的 (a) 不同，故意的）：**全程一般 `x : Fin 12 → ℝ` + `first7 x`，不用 `pad12`** ——
  `fderiv_adjointBlock_val` 的右端含 `last5 x mm`，而 `last5 (pad12 z) mm = 0` ✗。

  **T1→T4 逐字镜像根内盒心版**（`ResidualDerivJT` L349 / L397 / L433 / L492）✓，两处形状坑按**根内惯用法**处理：
  * `.comp` 产出**合成式** ⇒ 用 **`rw [he, ← (…).fderiv] at h`**（**不用 `simpa`**：`simpa` 会重解析出
    不同的类型类实例路径 ⇒ 报 `Pi.normedAddCommGroup` vs `Pi.addCommGroup` 的 Type mismatch ✗✓）；
  * `hprod` 用 **`show … = (f * g) from rfl`** 再把 `((h5.mul hb).fderiv)` 接上 ✓；
  * 坐标投影用 mathlib **`ContinuousLinearMap.proj (up5 mm)`**（根内 `coord` 只到 `Fin 7` ✗）。

  **真实等级**：kernel-proved，零 `sorry` / 零自定义 `axiom` / 零 `native_decide`；未接根。
-/
import N11Formalization.F1.BallD35C10
import N11Formalization.ResidualDerivJTHess

/-! ## 0. 外部名自查前言（Lead R238 过程口径；**每条都实测存在**） -/
#check @N11Formalization.hasFDerivAt_gFun
#check @N11Formalization.gFun
#check @N11Formalization.evCLM
#check @N11Formalization.evCLM_apply
#check @N11Formalization.fderiv_adjointBlock_val
#check @N11Formalization.fderiv_adjointBlock_up5
#check @N11Formalization.fderiv_TCSystem_kkt_lam
#check @N11Formalization.fderiv_apply_val
#check @N11Formalization.TCSystem_row_eq_adjointBlock
#check @N11Formalization.hasFDerivAt_first7
#check @N11Formalization.proj7CLM_single_up5
#check @N11Formalization.up5_inj
#check @N11Formalization.kkt12
#check @N11Formalization.up5
#check @N11Formalization.differentiableAt_fderiv_residualFun_of_ball
#check @N11Formalization.differentiableAt_TCSystem_of_conditions

noncomputable section

namespace N11Formalization

/-! ## T1. `gFun` 在任意点的导数 -/

theorem hasFDerivAt_gFun_any (z : Fin 7 → ℝ)
    (hadj : DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) z)
    (i : Fin 7) (mm : Fin 5) :
    HasFDerivAt (gFun i mm)
      ((evCLM i mm).comp (fderiv ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) z)) z := by
  have h := (ContinuousLinearMap.hasFDerivAt (evCLM i mm)
    (x := fderiv ℝ residualFun z)).comp z hadj.hasFDerivAt
  have he : (⇑(evCLM i mm) ∘ fderiv ℝ residualFun) = gFun i mm := by
    funext y
    rw [Function.comp_apply, evCLM_apply]
    rfl
  rwa [he] at h

/-! ## T2. `adjointBlock` 行的 `fderiv` 取值（任意点 `x`） -/

theorem fderiv_adjointBlock_val_any (x : Fin 12 → ℝ)
    (hadj : DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) (first7 x))
    (i : Fin 7) (v : Fin 12 → ℝ) :
    (fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) x) v
      = ∑ mm : Fin 5, ((last5 x mm) * ((fderiv ℝ (gFun i mm) (first7 x)) (proj7CLM v))
          + (gFun i mm (first7 x)) * (v (up5 mm))) := by
  have hsum : (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i)
      = fun u => ∑ mm : Fin 5, last5 u mm * gFun i mm (first7 u) := rfl
  rw [hsum]
  have hdiff : ∀ mm : Fin 5, DifferentiableAt ℝ
      (fun u : Fin 12 → ℝ => last5 u mm * gFun i mm (first7 u)) x := fun mm => by
    have h5 : HasFDerivAt (fun u : Fin 12 → ℝ => last5 u mm)
        (ContinuousLinearMap.proj (up5 mm) : (Fin 12 → ℝ) →L[ℝ] ℝ) x :=
      ContinuousLinearMap.hasFDerivAt
        (f := (ContinuousLinearMap.proj (up5 mm) : (Fin 12 → ℝ) →L[ℝ] ℝ)) (x := x)
    have hb : HasFDerivAt (fun u : Fin 12 → ℝ => gFun i mm (first7 u))
        ((fderiv ℝ (gFun i mm) (first7 x)).comp proj7CLM) x := by
      have h := (hasFDerivAt_gFun_any (first7 x) hadj i mm).comp x (hasFDerivAt_first7 x)
      have he : (gFun i mm ∘ first7) = (fun u : Fin 12 → ℝ => gFun i mm (first7 u)) := rfl
      rw [he, ← (hasFDerivAt_gFun_any (first7 x) hadj i mm).fderiv] at h
      exact h
    exact (h5.mul hb).differentiableAt
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun mm (u : Fin 12 → ℝ) => last5 u mm * gFun i mm (first7 u)) (fun mm _ => hdiff mm)]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun mm _ => ?_
  have h5 : HasFDerivAt (fun u : Fin 12 → ℝ => last5 u mm)
      (ContinuousLinearMap.proj (up5 mm) : (Fin 12 → ℝ) →L[ℝ] ℝ) x :=
    ContinuousLinearMap.hasFDerivAt
      (f := (ContinuousLinearMap.proj (up5 mm) : (Fin 12 → ℝ) →L[ℝ] ℝ)) (x := x)
  have hb : HasFDerivAt (fun u : Fin 12 → ℝ => gFun i mm (first7 u))
      ((fderiv ℝ (gFun i mm) (first7 x)).comp proj7CLM) x := by
    have h := (hasFDerivAt_gFun_any (first7 x) hadj i mm).comp x (hasFDerivAt_first7 x)
    have he : (gFun i mm ∘ first7) = (fun u : Fin 12 → ℝ => gFun i mm (first7 u)) := rfl
    rw [he, ← (hasFDerivAt_gFun_any (first7 x) hadj i mm).fderiv] at h
    exact h
  have hprod : fderiv ℝ (fun u : Fin 12 → ℝ => last5 u mm * gFun i mm (first7 u)) x
      = (last5 x mm) • ((fderiv ℝ (gFun i mm) (first7 x)).comp proj7CLM)
        + (gFun i mm (first7 x)) • ((ContinuousLinearMap.proj (up5 mm)) :
            (Fin 12 → ℝ) →L[ℝ] ℝ) := by
    rw [show (fun u : Fin 12 → ℝ => last5 u mm * gFun i mm (first7 u))
        = ((fun u : Fin 12 → ℝ => last5 u mm)
          * (fun u : Fin 12 → ℝ => gFun i mm (first7 u))) from rfl]
    exact ((h5.mul hb).fderiv)
  rw [hprod]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-! ## T3. `adjointBlock` 行沿 `λ_m` 的方向导数（**任意点**） -/

theorem fderiv_adjointBlock_up5_any (x : Fin 12 → ℝ)
    (hadj : DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) (first7 x))
    (i : Fin 7) (m : Fin 5) :
    (fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) x)
      (Pi.single (up5 m) (1 : ℝ)) = (fderiv ℝ residualFun (first7 x) (Pi.single i (1 : ℝ))) m := by
  rw [fderiv_adjointBlock_val_any x hadj i]
  have h0 : ∀ mm : Fin 5,
      (fderiv ℝ (gFun i mm) (first7 x)) (proj7CLM (Pi.single (up5 m) (1 : ℝ))) = 0 := fun mm => by
    rw [proj7CLM_single_up5, ContinuousLinearMap.map_zero]
  have h1 : ∀ mm : Fin 5,
      (Pi.single (up5 m) (1 : ℝ) : Fin 12 → ℝ) (up5 mm) = if mm = m then 1 else 0 := by
    intro mm
    by_cases h : mm = m
    · subst h
      rw [Pi.single_eq_same, if_pos rfl]
    · rw [Pi.single_eq_of_ne (i := up5 m) (i' := up5 mm) (fun hh => h (up5_inj hh)),
        if_neg h]
  rw [Finset.sum_eq_single m]
  · rw [h0 m, h1 m, if_pos rfl, mul_zero, mul_one, zero_add]
    rfl
  · intro mm _ hmm
    rw [h0 mm, h1 mm, if_neg hmm]
    simp only [mul_zero, add_zero]
  · intro h
    exact absurd (Finset.mem_univ m) h

/-! ## T4. `adjointBlock` 行在任意点可微 -/

theorem differentiableAt_adjointBlockRow_any (x : Fin 12 → ℝ)
    (hadj : DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) (first7 x))
    (i : Fin 7) :
    DifferentiableAt ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) x := by
  have hsum : (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i)
      = fun u => ∑ mm : Fin 5, last5 u mm * gFun i mm (first7 u) := rfl
  rw [hsum]
  refine DifferentiableAt.sum (𝕜 := ℝ) (u := Finset.univ)
    (A := fun mm : Fin 5 => fun u : Fin 12 → ℝ => last5 u mm * gFun i mm (first7 u)) ?_
  intro mm _
  have h5 : HasFDerivAt (fun u : Fin 12 → ℝ => last5 u mm)
      (ContinuousLinearMap.proj (up5 mm) : (Fin 12 → ℝ) →L[ℝ] ℝ) x :=
    ContinuousLinearMap.hasFDerivAt
      (f := (ContinuousLinearMap.proj (up5 mm) : (Fin 12 → ℝ) →L[ℝ] ℝ)) (x := x)
  have hb : HasFDerivAt (fun u : Fin 12 → ℝ => gFun i mm (first7 u))
      ((fderiv ℝ (gFun i mm) (first7 x)).comp proj7CLM) x := by
    have h := (hasFDerivAt_gFun_any (first7 x) hadj i mm).comp x (hasFDerivAt_first7 x)
    have he : (gFun i mm ∘ first7) = (fun u : Fin 12 → ℝ => gFun i mm (first7 u)) := rfl
    rw [he, ← (hasFDerivAt_gFun_any (first7 x) hadj i mm).fderiv] at h
    exact h
  exact (h5.mul hb).differentiableAt

/-! ## T5. `(c)`：KKT 行 × `λ` 列（任意点 `x`） -/

theorem fderiv_TCSystem_kkt_lam_any (x : Fin 12 → ℝ)
    (hdT : DifferentiableAt ℝ TCSystem x)
    (hadj : DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) (first7 x))
    (i : Fin 7) (m : Fin 5) :
    (fderiv ℝ TCSystem x (Pi.single (up5 m) (1 : ℝ))) (kkt12 i)
      = -((fderiv ℝ residualFun (first7 x) (Pi.single i (1 : ℝ))) m) := by
  rw [fderiv_apply_val hdT (kkt12 i) (Pi.single (up5 m) (1 : ℝ)),
    TCSystem_row_eq_adjointBlock i]
  have hA : HasFDerivAt (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i)
      (fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) x) x :=
    (differentiableAt_adjointBlockRow_any x hadj i).hasFDerivAt
  have hc : HasFDerivAt
      (fun _ : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0))
      (0 : (Fin 12 → ℝ) →L[ℝ] ℝ) x :=
    hasFDerivAt_const _ _
  have hsub : fderiv ℝ (fun u : Fin 12 → ℝ =>
        (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0)
          - adjointBlock (first7 u) (last5 u) i) x
      = 0 - fderiv ℝ (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) x := by
    rw [show (fun u : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0)
          - adjointBlock (first7 u) (last5 u) i)
        = (fun _ : Fin 12 → ℝ => (if ((kkt12 i : Fin 12) : ℕ) = 11 then (1 : ℝ) else 0))
          - (fun u : Fin 12 → ℝ => adjointBlock (first7 u) (last5 u) i) from rfl]
    exact (hc.sub hA).fderiv
  rw [hsub, sub_apply]
  simp only [zero_apply, zero_sub]
  rw [fderiv_adjointBlock_up5_any x hadj i m]

/-! ## T6. 合取（`∀ i m`） -/

theorem JT_kkt_lam_all (x : Fin 12 → ℝ) (hdT : DifferentiableAt ℝ TCSystem x)
    (hadj : DifferentiableAt ℝ (fun y : Fin 7 → ℝ => fderiv ℝ residualFun y) (first7 x)) :
    ∀ i : Fin 7, ∀ m : Fin 5,
      (fderiv ℝ TCSystem x (Pi.single (up5 m) (1 : ℝ))) (kkt12 i)
        = -((fderiv ℝ residualFun (first7 x) (Pi.single i (1 : ℝ))) m) :=
  fun i m => fderiv_TCSystem_kkt_lam_any x hdT hadj i m

end N11Formalization

#print axioms N11Formalization.hasFDerivAt_gFun_any
#print axioms N11Formalization.fderiv_adjointBlock_val_any
#print axioms N11Formalization.fderiv_adjointBlock_up5_any
#print axioms N11Formalization.differentiableAt_adjointBlockRow_any
#print axioms N11Formalization.fderiv_TCSystem_kkt_lam_any
#print axioms N11Formalization.JT_kkt_lam_all
