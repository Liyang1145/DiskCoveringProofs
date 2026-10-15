import N11Formalization.HessSeamHL7

/-!
# hess-seam / `_any` 规则族（**点一般化**的通用二阶规则）

根内 `ResidualDerivJTHess` 的通用规则（`hasFDerivAt_fderiv_{add,sub,mul_scalar,comp_scalar}`、
`secondPartial_{add,sub}`）**全部把 `u0` 写死在语句里** ✗（`#check` 实测：`secondPartial_sub : … u0 → … u0 → …` ✓），
而**证明本身与点无关** ✓ ⇒ 本件把它们**逐字升格**为点一般形式（`u0 → x` ✓），供 z-一般 L7 链复用 ✓。

**依赖状态**：本件**不依赖** `tower-bc` ✓（只用根内 `ResidualDerivJTHess` 的 `fderiv_add/sub` 与 `HasFDerivAt.sub/add` ✓）。
⚠ 实测：`hasFDerivAt_fderiv_*_any` 与叶节点 `*_any`（`hasFDerivAt_fderiv_UvecC0_any` 等）**均不在根** ✗（探针 `logs/probe10.txt` ✓）
⇒ z-一般 L7 链的**叶层**仍待 `tower-bc` 的 (A) 层重述落根（或我按其模板自写 ✓）。
-/

noncomputable section

namespace N11Formalization

namespace HessSeam

open RatInterval

/-- 点一般化的 `fderiv (φ + ψ)` 二阶规则 ✓（`hasFDerivAt_fderiv_add` 的逐字升格）。 -/
theorem hasFDerivAt_fderiv_add_any {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} (x : Fin 7 → ℝ)
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

/-- 点一般化的 `fderiv (φ − ψ)` 二阶规则 ✓。 -/
theorem hasFDerivAt_fderiv_sub_any {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} (x : Fin 7 → ℝ)
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

/-- 点一般化的 `secondPartial (φ + ψ)` 分解 ✓。 -/
theorem secondPartial_add_any {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} (x : Fin 7 → ℝ)
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 x)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 x)
    (hφd : ∀ᶠ z in nhds x, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds x, DifferentiableAt ℝ ψ z) (i j : Fin 7) :
    secondPartial (fun z => φ z + ψ z) x i j
      = secondPartial φ x i j + secondPartial ψ x i j := by
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_add_any x hφ hψ hφd hψd),
    secondPartial_eq_of_hasFDerivAt hφ, secondPartial_eq_of_hasFDerivAt hψ]
  exact add_apply _ _ _

/-- 点一般化的 `secondPartial (φ − ψ)` 分解 ✓。 -/
theorem secondPartial_sub_any {φ ψ : (Fin 7 → ℝ) → ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} (x : Fin 7 → ℝ)
    (hφ : HasFDerivAt (fun z => fderiv ℝ φ z) φ2 x)
    (hψ : HasFDerivAt (fun z => fderiv ℝ ψ z) ψ2 x)
    (hφd : ∀ᶠ z in nhds x, DifferentiableAt ℝ φ z)
    (hψd : ∀ᶠ z in nhds x, DifferentiableAt ℝ ψ z) (i j : Fin 7) :
    secondPartial (fun z => φ z - ψ z) x i j
      = secondPartial φ x i j - secondPartial ψ x i j := by
  rw [secondPartial_eq_of_hasFDerivAt (hasFDerivAt_fderiv_sub_any x hφ hψ hφd hψd),
    secondPartial_eq_of_hasFDerivAt hφ, secondPartial_eq_of_hasFDerivAt hψ]
  exact sub_apply _ _ _

/-- 点一般化的 `fderiv (φ · ψ)` 二阶规则（T3 ✓）—— `hasFDerivAt_fderiv_mul_scalar` 的逐字升格。 -/
theorem hasFDerivAt_fderiv_mul_scalar_any
    {φ ψ : (Fin 7 → ℝ) → ℝ} {φ1 ψ1 : (Fin 7 → ℝ) →L[ℝ] ℝ}
    {φ2 ψ2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} (x : Fin 7 → ℝ)
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

/-- 点一般化的 `fderiv (u ∘ g)` 二阶规则（T2 ✓）—— `hasFDerivAt_fderiv_comp_scalar` 的逐字升格。 -/
theorem hasFDerivAt_fderiv_comp_scalar_any {g : (Fin 7 → ℝ) → ℝ} {g1 : (Fin 7 → ℝ) →L[ℝ] ℝ}
    {g2 : (Fin 7 → ℝ) →L[ℝ] ((Fin 7 → ℝ) →L[ℝ] ℝ)} {u : ℝ → ℝ} {u1 : ℝ →L[ℝ] ℝ}
    (x : Fin 7 → ℝ)
    (hg : HasFDerivAt g g1 x) (hg2 : HasFDerivAt (fun z => fderiv ℝ g z) g2 x)
    (hu2 : HasFDerivAt (fun t => deriv u t) u1 (g x))
    (hgd : ∀ᶠ z in nhds x, DifferentiableAt ℝ g z)
    (hud : ∀ᶠ z in nhds x, DifferentiableAt ℝ u (g z)) :
    HasFDerivAt (fun z => fderiv ℝ (fun z => u (g z)) z)
      ((deriv u (g x)) • g2 + (u1.comp g1).smulRight g1) x := by
  have hc : HasFDerivAt (fun z => deriv u (g z)) (u1.comp g1) x := hu2.comp x hg
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

end HessSeam

end N11Formalization
