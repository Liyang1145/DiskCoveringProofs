import N11Formalization.TruePinChartConsumer

/-!
Unconditional actual-source velocity equations in five INDEPENDENT Cartesian
coordinates (P.x,P.y,Q.x,Q.y,R). These are not the constrained TC-chart equations.
Both genuine circle equations and source branch are supplied by the construction.
-/
set_option autoImplicit false
namespace N11Formalization.TruePinCartesianDifferential
open N11Formalization TrueCirclePinSmooth PinCircleDifferential PinTangentGeometry
noncomputable section

def leftLinear : Data →ₗ[ℝ] Point where
  toFun := left
  map_add' := by intro a b; ext i; fin_cases i <;> rfl
  map_smul' := by intro r a; ext i; fin_cases i <;> rfl

def rightLinear : Data →ₗ[ℝ] Point where
  toFun := right
  map_add' := by intro a b; ext i; fin_cases i <;> rfl
  map_smul' := by intro r a; ext i; fin_cases i <;> rfl

def leftCLM : Data →L[ℝ] Point := leftLinear.toContinuousLinearMap
def rightCLM : Data →L[ℝ] Point := rightLinear.toContinuousLinearMap

@[simp] theorem leftCLM_apply (z : Data) : leftCLM z = left z := rfl
@[simp] theorem rightCLM_apply (z : Data) : rightCLM z = right z := rfl

theorem left_hasFDerivAt (z : Data) : HasFDerivAt left leftCLM z := leftCLM.hasFDerivAt
theorem right_hasFDerivAt (z : Data) : HasFDerivAt right rightCLM z := rightCLM.hasFDerivAt

def sourceVelocity (k : Fin 9) (dz : Data) : Point :=
  fderiv ℝ (pinData (sourceSeed k)) (sourceData k) dz

/-- All source geometric and differentiability premises are discharged, including the
variable-radius column R*dR. The Cartesian perturbation dz is completely arbitrary. -/
theorem source_cartesian_normal_rows (k : Fin 9)
    (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) (dz : Data) :
    inner ℝ (Uvec SourceExactRoot.sourceRoot k - ringCenter SourceExactRoot.sourceRoot k)
      (sourceVelocity k dz - left dz) = SourceExactRoot.sourceRoot 6 * dz 4 ∧
    inner ℝ (Uvec SourceExactRoot.sourceRoot k -
      ringCenter SourceExactRoot.sourceRoot (k+1))
      (sourceVelocity k dz - right dz) = SourceExactRoot.sourceRoot 6 * dz 4 := by
  let z : ℝ → Data := fun s => sourceData k + s • dz
  have hz : HasDerivAt z dz 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const dz |>.const_add (sourceData k)
    change HasDerivAt (fun s : ℝ => sourceData k + s • dz) (1 • dz) 0 at h
    rw [one_smul] at h
    exact h
  have hz0 : z 0 = sourceData k := by simp [z]
  have hv := ((source_pinData_smooth k hk).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hz hz0.symm
  have hp := (left_hasFDerivAt (z 0)).comp_hasDerivAt 0 hz
  have hq := (right_hasFDerivAt (z 0)).comp_hasDerivAt 0 hz
  have hr := (ContinuousLinearMap.proj (4 : Fin 5) :
    Data →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hz
  have he : ∀ᶠ s in nhds (0 : ℝ),
      ‖pinData (sourceSeed k) (z s)-left (z s)‖^2 = (z s 4)^2 ∧
      ‖pinData (sourceSeed k) (z s)-right (z s)‖^2 = (z s 4)^2 := by
    have h := source_pinData_equations_eventually k hk
    rw [← hz0] at h
    exact hz.continuousAt.eventually h
  have hP := circle_velocity_row hv hp hr (he.mono fun s hs => hs.1)
  have hQ := circle_velocity_row hv hq hr (he.mono fun s hs => hs.2)
  constructor
  · simpa only [Function.comp_def, hz0, source_pinData_eq k hk, left_source,
      radius_source, leftCLM_apply, ContinuousLinearMap.proj_apply, sourceVelocity] using hP
  · simpa only [Function.comp_def, hz0, source_pinData_eq k hk, right_source,
      radius_source, rightCLM_apply, ContinuousLinearMap.proj_apply, sourceVelocity] using hQ

/-- Explicit elimination of the pin velocity in any covector spanned by the two
source circle normals. The coefficients are algebraic inputs, not positivity claims. -/
theorem source_cartesian_covector_elimination (k : Fin 9)
    (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) (dz : Data) (a b : ℝ) :
    inner ℝ
      (a • (Uvec SourceExactRoot.sourceRoot k - ringCenter SourceExactRoot.sourceRoot k) +
       b • (Uvec SourceExactRoot.sourceRoot k - ringCenter SourceExactRoot.sourceRoot (k+1)))
      (sourceVelocity k dz) =
      a * inner ℝ (Uvec SourceExactRoot.sourceRoot k - ringCenter SourceExactRoot.sourceRoot k)
        (left dz) +
      b * inner ℝ (Uvec SourceExactRoot.sourceRoot k -
        ringCenter SourceExactRoot.sourceRoot (k+1)) (right dz) +
      (a+b) * SourceExactRoot.sourceRoot 6 * dz 4 := by
  obtain ⟨hP,hQ⟩ := source_cartesian_normal_rows k hk dz
  rw [inner_sub_right] at hP hQ
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  linear_combination a * hP + b * hQ

end
end N11Formalization.TruePinCartesianDifferential
#check @N11Formalization.TruePinCartesianDifferential.source_cartesian_normal_rows
#check @N11Formalization.TruePinCartesianDifferential.source_cartesian_covector_elimination
#print axioms N11Formalization.TruePinCartesianDifferential.source_cartesian_covector_elimination
