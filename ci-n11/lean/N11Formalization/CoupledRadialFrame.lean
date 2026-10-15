import Mathlib
import N11Formalization.SourceWidthNondegenerate
import N11Formalization.BoundaryChartSource
set_option autoImplicit false
namespace N11Formalization.CoupledRadialFrame
open N11Formalization WidthRadialDerivative BoundaryChartSource
noncomputable section
abbrev Frame := Fin 12 → ℝ

/-- Widths x0..4 replaced by their inner radial roots; directions/hubs/R unchanged. -/
def radialFrame (x : Frame) : Frame := fun i =>
  if (i : ℕ) < 5 then rhoMinus (x 11) (x i) else x i

def radiusSlope (R a : ℝ) : ℝ := -R / Real.sqrt (R^2-Real.sin a^2)

def triangular (A B : Fin 5 → ℝ) (v : Frame) : Frame := fun i =>
  if h : (i : ℕ)<5 then A ⟨i,h⟩ * v i + B ⟨i,h⟩ * v 11 else v i

def triangularInv (A B : Fin 5 → ℝ) (v : Frame) : Frame := fun i =>
  if h : (i : ℕ)<5 then (v i-B ⟨i,h⟩*v 11)/A ⟨i,h⟩ else v i

/-- Exact triangular derivative, including radius-column cross terms. -/
def triangularLinear (A B : Fin 5 → ℝ) : Frame →ₗ[ℝ] Frame where
  toFun := triangular A B
  map_add' := by
    intro v w
    funext i
    by_cases h : (i : ℕ)<5
    · simp only [triangular, h, dite_true, Pi.add_apply]
      ring
    · simp only [triangular, h, dite_false, Pi.add_apply]
  map_smul' := by
    intro r v
    funext i
    by_cases h : (i : ℕ)<5
    · simp only [triangular, h, dite_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp only [triangular, h, dite_false, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

def triangularCLM (A B : Fin 5 → ℝ) : Frame →L[ℝ] Frame :=
  (triangularLinear A B).toContinuousLinearMap

/-- Inverse is explicitly upper-triangular; scalar diagonal nonzero suffices. -/
def triangularEquiv (A B : Fin 5 → ℝ) (hA : ∀ i, A i ≠ 0) : Frame ≃ₗ[ℝ] Frame where
  toFun := triangular A B
  invFun := triangularInv A B
  left_inv := by
    intro v
    funext i
    unfold triangularInv triangular
    simp only [show ¬ ((11 : Fin 12) : ℕ)<5 from by decide, dite_false]
    split_ifs with h
    · field_simp [hA ⟨i,h⟩]
      <;> ring
    · rfl
  right_inv := by
    intro v
    funext i
    unfold triangular triangularInv
    simp only [show ¬ ((11 : Fin 12) : ℕ)<5 from by decide, dite_false]
    split_ifs with h
    · field_simp [hA ⟨i,h⟩]
      <;> ring
    · rfl
  map_add' := by
    intro v w
    exact (triangularLinear A B).map_add v w
  map_smul' := by
    intro r v
    exact (triangularLinear A B).map_smul r v

def triangularCLE (A B : Fin 5 → ℝ) (hA : ∀ i, A i ≠ 0) : Frame ≃L[ℝ] Frame :=
  (triangularEquiv A B hA).toContinuousLinearEquiv

@[simp] theorem triangularCLE_apply (A B : Fin 5 → ℝ) (hA : ∀ i, A i ≠ 0) (v : Frame) :
    triangularCLE A B hA v = triangular A B v := rfl

/-- Both derivative representations use the same linear map, not just matching dimensions. -/
theorem triangularCLE_clm (A B : Fin 5 → ℝ) (hA : ∀ i, A i ≠ 0) :
    (triangularCLE A B hA : Frame →L[ℝ] Frame) = triangularCLM A B := by
  ext v i
  rfl

private def coord (i : Fin 12) : Frame →L[ℝ] ℝ := ContinuousLinearMap.proj i

def slopeA (x : Frame) (j : Fin 5) : ℝ := widthSlope (x 11) (x ⟨j,by omega⟩)
def slopeB (x : Frame) (j : Fin 5) : ℝ := radiusSlope (x 11) (x ⟨j,by omega⟩)

/-- True joint derivative of rhoMinus(x11,xi). The radius is NOT held fixed. -/
theorem hasFDerivAt_component (x : Frame) (i : Fin 12)
    (hrad : 0 < (x 11)^2-Real.sin (x i)^2) :
    HasFDerivAt (fun y : Frame => rhoMinus (y 11) (y i))
      (widthSlope (x 11) (x i) • coord i + radiusSlope (x 11) (x i) • coord 11) x := by
  have hi := (coord i).hasFDerivAt (x := x)
  have hR := (coord 11).hasFDerivAt (x := x)
  have hd := hi.cos.sub (((hR.pow 2).sub (hi.sin.pow 2)).sqrt (ne_of_gt hrad))
  have heq : widthSlope (x 11) (x i) • coord i + radiusSlope (x 11) (x i) • coord 11 =
      -Real.sin ((coord i) x) • coord i -
      (1/(2*Real.sqrt ((x 11)^2-Real.sin (x i)^2))) •
        ((2 • ((coord 11) x)^(2-1)) • coord 11 -
          (2 • Real.sin ((coord i) x)^(2-1)) • (Real.cos ((coord i) x) • coord i)) := by
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, coord,
      ContinuousLinearMap.proj_apply, pow_one, show (2-1:ℕ)=1 from rfl]
    unfold widthSlope rhoMinus radiusSlope
    have hn := ne_of_gt (Real.sqrt_pos.mpr hrad)
    field_simp
    <;> ring
  rw [heq]
  exact hd

/-- Actual Frechet derivative of the coupled 12D width/rho map. -/
theorem hasFDerivAt_radialFrame (x : Frame)
    (hrad : ∀ j : Fin 5, 0 < (x 11)^2-Real.sin (x ⟨j,by omega⟩)^2) :
    HasFDerivAt radialFrame (triangularCLM (slopeA x) (slopeB x)) x := by
  have hpi : HasFDerivAt radialFrame
      (ContinuousLinearMap.pi (fun i : Fin 12 =>
        if h : (i : ℕ)<5 then
          slopeA x ⟨i,h⟩ • coord i + slopeB x ⟨i,h⟩ • coord 11 else coord i)) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    by_cases h : (i : ℕ)<5
    · simp only [radialFrame, h, dite_true, ite_true]
      exact hasFDerivAt_component x i (hrad ⟨i,h⟩)
    · simp only [radialFrame, h, dite_false, ite_false]
      exact (coord i).hasFDerivAt
  have heq : triangularCLM (slopeA x) (slopeB x) =
      ContinuousLinearMap.pi (fun i : Fin 12 =>
        if h : (i : ℕ)<5 then
          slopeA x ⟨i,h⟩ • coord i + slopeB x ⟨i,h⟩ • coord 11 else coord i) := by
    apply ContinuousLinearMap.ext
    intro v
    funext i
    change triangular (slopeA x) (slopeB x) v i = _
    by_cases h : (i : ℕ)<5
    · simp [triangular, h, coord, smul_eq_mul]
    · simp [triangular, h, coord]
  rw [heq]
  exact hpi

/-- The coupled radial map is C1 whenever all five square-root radicands are nonzero. -/
theorem radialFrame_contDiffAt (x : Frame)
    (hrad : ∀ j : Fin 5, (x 11)^2 - Real.sin (x ⟨j,by omega⟩)^2 ≠ 0) :
    ContDiffAt ℝ 1 radialFrame x := by
  rw [contDiffAt_pi]
  intro i
  by_cases h : (i : ℕ) < 5
  · simp only [radialFrame, h]
    have hi : ContDiffAt ℝ 1 (fun y : Frame => y i) x := contDiffAt_coord i x
    have hR : ContDiffAt ℝ 1 (fun y : Frame => y 11) x := contDiffAt_coord 11 x
    have hs : ContDiffAt ℝ 1 (fun y : Frame => Real.sin (y i)) x :=
      contDiffAt_sin_comp hi
    have harg : ContDiffAt ℝ 1
        (fun y : Frame => (y 11)^2 - Real.sin (y i)^2) x :=
      (hR.pow 2).sub (hs.pow 2)
    have hne : (x 11)^2 - Real.sin (x i)^2 ≠ 0 := by
      exact hrad ⟨i, h⟩
    exact (contDiffAt_cos_comp hi).sub (harg.sqrt hne)
  · simp only [radialFrame, h]
    exact contDiffAt_coord i x

/-- The coupled map has the strict derivative given by its triangular continuous
linear equivalence whenever the five radicands are positive. -/
theorem radialFrame_hasStrictFDerivAt (x : Frame)
    (hrad : ∀ j : Fin 5, 0 < (x 11)^2 - Real.sin (x ⟨j,by omega⟩)^2)
    (hA : ∀ j : Fin 5, slopeA x j ≠ 0) :
    HasStrictFDerivAt radialFrame
      ((triangularCLE (slopeA x) (slopeB x) hA : Frame →L[ℝ] Frame)) x := by
  have hc := radialFrame_contDiffAt x (fun j => ne_of_gt (hrad j))
  have hd := hasFDerivAt_radialFrame x hrad
  have hs := hc.hasStrictFDerivAt' hd (by norm_num)
  rw [triangularCLE_clm]
  exact hs

/-- Binding the five independent widths to the actual source angles. -/
theorem sourceFrame_width_coord (u : Fin 12 → ℝ) (j : Fin 5) :
    sourceFrame u (⟨j,by omega⟩ : Fin 12) = angleVec u (⟨j,by omega⟩ : Fin 9) := by
  fin_cases j <;> simp [sourceFrame]

def sourcePoint : Frame := sourceFrame SourceExactRoot.sourceRoot

theorem source_radicands :
    ∀ j : Fin 5, 0 < (sourcePoint 11)^2 - Real.sin (sourcePoint ⟨j,by omega⟩)^2 := by
  intro j
  change 0 < (SourceExactRoot.sourceRoot 6)^2 -
    Real.sin (sourceFrame SourceExactRoot.sourceRoot (⟨j,by omega⟩ : Fin 12))^2
  rw [sourceFrame_width_coord]
  exact SourceWidthNondegenerate.source_radicand_pos ⟨j,by omega⟩

theorem source_slopeA_pos (j : Fin 5) : 0 < slopeA sourcePoint j := by
  change 0 < widthSlope (SourceExactRoot.sourceRoot 6)
    (sourceFrame SourceExactRoot.sourceRoot (⟨j,by omega⟩ : Fin 12))
  rw [sourceFrame_width_coord]
  exact SourceWidthNondegenerate.source_widthSlope_pos ⟨j,by omega⟩

def sourceJacobian : Frame ≃L[ℝ] Frame :=
  triangularCLE (slopeA sourcePoint) (slopeB sourcePoint)
    (fun j => ne_of_gt (source_slopeA_pos j))

theorem source_strict_derivative :
    HasStrictFDerivAt radialFrame (sourceJacobian : Frame →L[ℝ] Frame) sourcePoint :=
  radialFrame_hasStrictFDerivAt sourcePoint source_radicands
    (fun j => ne_of_gt (source_slopeA_pos j))

/-- A local inverse for the true 12D map: radius is a variable, not a parameter. -/
def sourceInverse : Frame → Frame :=
  HasStrictFDerivAt.localInverse radialFrame sourceJacobian sourcePoint source_strict_derivative

theorem sourceInverse_apply_image :
    sourceInverse (radialFrame sourcePoint) = sourcePoint :=
  source_strict_derivative.localInverse_apply_image

theorem sourceJacobian_symm_apply (v : Frame) :
    sourceJacobian.symm v = triangularInv (slopeA sourcePoint) (slopeB sourcePoint) v := rfl

theorem sourceInverse_left :
    ∀ᶠ x in nhds sourcePoint, sourceInverse (radialFrame x) = x :=
  source_strict_derivative.eventually_left_inverse

theorem sourceInverse_right :
    ∀ᶠ y in nhds (radialFrame sourcePoint), radialFrame (sourceInverse y) = y :=
  source_strict_derivative.eventually_right_inverse

theorem sourceInverse_strict_derivative :
    HasStrictFDerivAt sourceInverse (sourceJacobian.symm : Frame →L[ℝ] Frame)
      (radialFrame sourcePoint) := source_strict_derivative.to_localInverse

end
end N11Formalization.CoupledRadialFrame
#check @N11Formalization.CoupledRadialFrame.hasFDerivAt_radialFrame
#check @N11Formalization.CoupledRadialFrame.source_strict_derivative
#check @N11Formalization.CoupledRadialFrame.sourceInverse_left
#check @N11Formalization.CoupledRadialFrame.sourceInverse_right
#check @N11Formalization.CoupledRadialFrame.sourceInverse_strict_derivative
#print axioms N11Formalization.CoupledRadialFrame.hasFDerivAt_radialFrame
#print axioms N11Formalization.CoupledRadialFrame.triangularCLE_clm
#print axioms N11Formalization.CoupledRadialFrame.sourceInverse_strict_derivative
