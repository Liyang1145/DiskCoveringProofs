import N11Formalization.SourceFanCircumradius
import N11Formalization.CircumradiusDifferential

/-! Genuine circumradius derivative on all independent Cartesian23 directions,
and positive LENGTH-to-radius gradient conversion at the actual frozen root.
No source circumcentre/radius/curve equations or derivative premise remains.
Beta positivity and physical boundary/stress interfaces remain separate. -/
set_option autoImplicit false
namespace N11Formalization.SourceFanRadiusDerivative
open N11Formalization CartesianReflectionSpace SourceFanLengthCovector
open SourceFanConversion SourceFanCircumradius TrueCirclePinSmooth
open TruePinCartesianDifferential
noncomputable section

@[simp] theorem left_ringData (k : Fin 9) (x : Full) :
    left (FullCartesianResidual.ringData k x) = FullCartesianResidual.ring x k := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem right_ringData (k : Fin 9) (x : Full) :
    right (FullCartesianResidual.ringData k x) = FullCartesianResidual.ring x (k+1) := by
  ext i
  fin_cases i <;> rfl

theorem left_ring_derivative (k : Fin 9) (x : Full) :
    HasFDerivAt (fun y : Full => FullCartesianResidual.ring y k)
      (leftCLM.comp (dataCLM k)) x := by
  have h := (left_hasFDerivAt (FullCartesianResidual.ringData k x)).comp x
    (dataCLM k).hasFDerivAt
  simpa only [Function.comp_def, dataCLM_apply, left_ringData] using h

theorem right_ring_derivative (k : Fin 9) (x : Full) :
    HasFDerivAt (fun y : Full => FullCartesianResidual.ring y (k+1))
      (rightCLM.comp (dataCLM k)) x := by
  have h := (right_hasFDerivAt (FullCartesianResidual.ringData k x)).comp x
    (dataCLM k).hasFDerivAt
  simpa only [Function.comp_def, dataCLM_apply, right_ringData] using h

/-- Constructed radius, not a named algebraic covector: differentiating the
three genuine circumcircle equations kills moving centre velocity by the
proved source affine-centre identity. -/
theorem fanRadius_source_fderiv (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8)
    (v : Full) :
    fderiv ℝ (fanRadius k) FullCartesianResidual.sourcePoint v =
      -(betaP k * inner ℝ (normalP k)
          (left (FullCartesianResidual.ringData k v)) +
        betaQ k * inner ℝ (normalQ k)
          (right (FullCartesianResidual.ringData k v)) +
        betaH k * inner ℝ (normalH k) (fullHub k v)) / SourceExactRoot.sourceRoot 6 := by
  let root := FullCartesianResidual.sourcePoint
  let u : ℝ → Full := fun s => root + s • v
  have hu : HasDerivAt u v 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add root
    change HasDerivAt (fun s : ℝ => root+s • v) (1 • v) 0 at h
    rw [one_smul] at h
    exact h
  have hu0 : u 0 = FullCartesianResidual.sourcePoint := by simp [u, root]
  have hz := ((center_source_smooth k hk).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hu hu0.symm
  have hP := (left_ring_derivative k (u 0)).comp_hasDerivAt 0 hu
  have hQ := (right_ring_derivative k (u 0)).comp_hasDerivAt 0 hu
  have hH := (fullHubCLM k).hasFDerivAt.comp_hasDerivAt 0 hu
  have hR := ((fanRadius_source_smooth k hk).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hu hu0.symm
  have he : ∀ᶠ s in nhds (0 : ℝ),
      ‖center k (u s)-FullCartesianResidual.ring (u s) k‖^2 = (fanRadius k (u s))^2 ∧
      ‖center k (u s)-FullCartesianResidual.ring (u s) (k+1)‖^2 = (fanRadius k (u s))^2 ∧
      ‖center k (u s)-fullHub k (u s)‖^2 = (fanRadius k (u s))^2 := by
    have he' := source_circle_equations_eventually k hk
    rw [← hu0] at he'
    exact hu.continuousAt.eventually he'
  have hC : (center k ∘ u) 0 =
      betaP k • (fun s => FullCartesianResidual.ring (u s) k) 0 +
      betaQ k • (fun s => FullCartesianResidual.ring (u s) (k+1)) 0 +
      betaH k • (fullHubCLM k ∘ u) 0 := by
    simp only [Function.comp_def, hu0, fullHubCLM_apply]
    rw [center_source k hk, fullHub_source]
    simp only [FullCartesianResidual.sourcePoint, FullCartesianResidual.ring_pack]
    exact beta_center_identity k hk
  have h := CircumradiusDifferential.weighted_radius_velocity
    (betaP k) (betaQ k) (betaH k) hz hP hQ hH hR (beta_sum_one k hk) hC
    (he.mono fun s hs => hs.1) (he.mono fun s hs => hs.2.1) (he.mono fun s hs => hs.2.2)
  have h' : SourceExactRoot.sourceRoot 6 *
      fderiv ℝ (fanRadius k) FullCartesianResidual.sourcePoint v =
      -(betaP k * inner ℝ (normalP k) (left (FullCartesianResidual.ringData k v)) +
        betaQ k * inner ℝ (normalQ k) (right (FullCartesianResidual.ringData k v)) +
        betaH k * inner ℝ (normalH k) (fullHub k v)) := by
    have hring (j : Fin 9) : FullCartesianResidual.ring FullCartesianResidual.sourcePoint j =
        ringCenter SourceExactRoot.sourceRoot j := FullCartesianResidual.ring_pack _ j
    simpa only [Function.comp_def, hu0, fanRadius_source k hk, center_source k hk,
      hring,
      fullHubCLM_apply, fullHub_source, ContinuousLinearMap.comp_apply,
      dataCLM_apply, leftCLM_apply, rightCLM_apply, normalP, normalQ, normalH] using h
  have hR0 : SourceExactRoot.sourceRoot 6 ≠ 0 := ne_of_gt SourceExactRoot.sourceRadius_pos
  apply (eq_div_iff hR0).mpr
  simpa only [mul_comm] using h'

def radiusExcess (k : Fin 9) (x : Full) : ℝ := fanRadius k x-x 22

theorem radiusExcess_source_fderiv (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8)
    (v : Full) :
    fderiv ℝ (radiusExcess k) FullCartesianResidual.sourcePoint v =
      fderiv ℝ (fanRadius k) FullCartesianResidual.sourcePoint v-v 22 := by
  have h := ((fanRadius_source_smooth k hk).differentiableAt
    (by norm_num)).hasFDerivAt.sub
      (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ).hasFDerivAt
  have hd := congrArg (fun d : Full →L[ℝ] ℝ => d v) h.fderiv
  exact hd

/-- SAME-root positive gradient conversion to the ACTUAL independently-moving
circumradius branch, for every full Cartesian23 direction. No hgradient
or source circumcircle premises remain. -/
theorem length_to_circumradius (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8)
    (v : Full) :
    fderiv ℝ (fanLength k) FullCartesianResidual.sourcePoint v =
      sourceConversion k * fderiv ℝ (radiusExcess k) FullCartesianResidual.sourcePoint v := by
  rw [normalized_fan_length k hk, radiusExcess_source_fderiv k hk,
    fanRadius_source_fderiv k hk]

end
end N11Formalization.SourceFanRadiusDerivative
#check @N11Formalization.SourceFanRadiusDerivative.fanRadius_source_fderiv
#check @N11Formalization.SourceFanRadiusDerivative.length_to_circumradius
#print axioms N11Formalization.SourceFanRadiusDerivative.length_to_circumradius
