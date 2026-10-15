import N11Formalization.FullCartesianResidual
import N11Formalization.TruePinCartesianDifferential

/-!
Actual fan LENGTH covector, eliminating the true intersection velocity using
the two independent source circle normals. All root normal-rank and source
contact distance premises are discharged. Coefficients are exact determinant
ratios; this file does not yet claim positive stress, barycentrics or a
circumradius-gradient conversion.
-/
set_option autoImplicit false
namespace N11Formalization.SourceFanLengthCovector
open N11Formalization PinTangentGeometry TrueCirclePinSmooth
open TruePinCartesianDifferential CartesianReflectionSpace
noncomputable section

def coefficientA (p q h : Point) : ℝ := det h q / det p q
def coefficientB (p q h : Point) : ℝ := det p h / det p q

theorem normal_expansion (p q h : Point) (hpq : det p q ≠ 0) :
    h = coefficientA p q h • p + coefficientB p q h • q := by
  ext i
  fin_cases i
  · change h 0 = coefficientA p q h * p 0 + coefficientB p q h * q 0
    unfold coefficientA coefficientB
    field_simp [hpq]
    unfold det
    ring
  · change h 1 = coefficientA p q h * p 1 + coefficientB p q h * q 1
    unfold coefficientA coefficientB
    field_simp [hpq]
    unfold det
    ring

def sourceHub (k : Fin 9) : Point :=
  if k=1 ∨ k=8 then hub1 SourceExactRoot.sourceRoot else hub0 SourceExactRoot.sourceRoot
def normalP (k : Fin 9) : Point :=
  Uvec SourceExactRoot.sourceRoot k - ringCenter SourceExactRoot.sourceRoot k
def normalQ (k : Fin 9) : Point :=
  Uvec SourceExactRoot.sourceRoot k - ringCenter SourceExactRoot.sourceRoot (k+1)
def normalH (k : Fin 9) : Point := Uvec SourceExactRoot.sourceRoot k - sourceHub k
def sourceA (k : Fin 9) : ℝ := coefficientA (normalP k) (normalQ k) (normalH k)
def sourceB (k : Fin 9) : ℝ := coefficientB (normalP k) (normalQ k) (normalH k)

theorem source_normalH_expansion (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    normalH k = sourceA k • normalP k + sourceB k • normalQ k :=
  normal_expansion _ _ _ (RootPinNormalConsumer.source_contact_normals_independent k hk)

theorem source_normalH_norm (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ‖normalH k‖ = SourceExactRoot.sourceRoot 6 := by
  rcases hk with rfl | rfl | rfl | rfl
  · simpa [normalH, sourceHub, dist_eq_norm, norm_sub_rev] using
      RootFanBranchConsumer.contact_dist_1
  · simpa [normalH, sourceHub, dist_eq_norm, norm_sub_rev] using
      RootFanBranchConsumer.contact_dist_2
  · simpa [normalH, sourceHub, dist_eq_norm, norm_sub_rev] using
      RootFanBranchConsumer.contact_dist_3
  · simpa [normalH, sourceHub, dist_eq_norm, norm_sub_rev] using
      RootFanBranchConsumer.contact_dist_8

/-- Genuine independent-Cartesian pin and independently moving hub.
The exact LENGTH covector contains -hub velocity and the (a+b-1)*dR term. -/
theorem source_length_covector_formula (k : Fin 9)
    (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) (dz : Data) (dh : Point) :
    inner ℝ (normalH k) (sourceVelocity k dz-dh) / SourceExactRoot.sourceRoot 6 - dz 4 =
      sourceA k * inner ℝ (normalP k) (left dz) / SourceExactRoot.sourceRoot 6 +
      sourceB k * inner ℝ (normalQ k) (right dz) / SourceExactRoot.sourceRoot 6 -
      inner ℝ (normalH k) dh / SourceExactRoot.sourceRoot 6 +
      (sourceA k+sourceB k-1) * dz 4 := by
  have he := source_cartesian_covector_elimination k hk dz (sourceA k) (sourceB k)
  change inner ℝ (sourceA k • normalP k + sourceB k • normalQ k)
      (sourceVelocity k dz) = _ at he
  rw [← source_normalH_expansion k hk] at he
  rw [inner_sub_right, he]
  have hr : SourceExactRoot.sourceRoot 6 ≠ 0 := ne_of_gt SourceExactRoot.sourceRadius_pos
  unfold normalP normalQ
  field_simp [hr]
  ring

/-- Generic norm differential in length units, specialized at a prescribed
positive source norm; useful for binding the algebraic force formula to fderiv. -/
theorem norm_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Point} {df : E →L[ℝ] Point} {x : E} {R : ℝ}
    (hf : HasFDerivAt f df x) (hnorm : ‖f x‖ = R) (hR : 0 < R) (v : E) :
    fderiv ℝ (fun y => ‖f y‖) x v = inner ℝ (f x) (df v) / R := by
  have hne : ‖f x‖^2 ≠ 0 := by rw [hnorm]; exact pow_ne_zero 2 (ne_of_gt hR)
  have hd := hf.norm_sq.sqrt hne
  have he : (fun y : E => Real.sqrt (‖f y‖^2)) = (fun y : E => ‖f y‖) := by
    funext y
    exact Real.sqrt_sq (norm_nonneg _)
  rw [he] at hd
  rw [hd.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    two_smul, smul_eq_mul]
  simp only [add_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [hnorm, Real.sqrt_sq hR.le]
  field_simp [ne_of_gt hR]
  ring

def fullHub (k : Fin 9) (x : Full) : Point :=
  if k=1 ∨ k=8 then FullCartesianResidual.hubB x else FullCartesianResidual.hubA x

def fullHubLinear (k : Fin 9) : Full →ₗ[ℝ] Point where
  toFun := fullHub k
  map_add' := by
    intro x y
    unfold fullHub
    split_ifs <;> ext i <;> fin_cases i <;>
      simp [FullCartesianResidual.hubA, FullCartesianResidual.hubB]
  map_smul' := by
    intro r x
    unfold fullHub
    split_ifs <;> ext i <;> fin_cases i <;>
      simp [FullCartesianResidual.hubA, FullCartesianResidual.hubB, smul_eq_mul]

def fullHubCLM (k : Fin 9) : Full →L[ℝ] Point := (fullHubLinear k).toContinuousLinearMap

def dataLinear (k : Fin 9) : Full →ₗ[ℝ] Data where
  toFun := FullCartesianResidual.ringData k
  map_add' := by
    intro x y
    funext i
    fin_cases i <;>
      simp [FullCartesianResidual.ringData, FullCartesianResidual.ring, FullCartesianResidual.radius]
  map_smul' := by
    intro r x
    funext i
    fin_cases i <;>
      simp [FullCartesianResidual.ringData, FullCartesianResidual.ring,
        FullCartesianResidual.radius, smul_eq_mul]

def dataCLM (k : Fin 9) : Full →L[ℝ] Data := (dataLinear k).toContinuousLinearMap

@[simp] theorem dataCLM_apply (k : Fin 9) (v : Full) :
    dataCLM k v = FullCartesianResidual.ringData k v := rfl
@[simp] theorem fullHubCLM_apply (k : Fin 9) (v : Full) :
    fullHubCLM k v = fullHub k v := rfl

theorem fullHub_source (k : Fin 9) :
    fullHub k FullCartesianResidual.sourcePoint = sourceHub k := by
  simp only [fullHub, sourceHub, FullCartesianResidual.sourcePoint,
    FullCartesianResidual.hubA_pack, FullCartesianResidual.hubB_pack]

def fanLength (k : Fin 9) (x : Full) : ℝ :=
  dist (FullCartesianResidual.ringPin k x) (fullHub k x) - FullCartesianResidual.radius x

/-- Actual Frechet derivative of the full-coordinate LENGTH contact residual.
Every center/radius direction v is arbitrary; no curve, normal-rank, source
distance or differentiability premise remains. -/
theorem fanLength_source_fderiv (k : Fin 9)
    (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) (v : Full) :
    fderiv ℝ (fanLength k) FullCartesianResidual.sourcePoint v =
      sourceA k * inner ℝ (normalP k) (TrueCirclePinSmooth.left (FullCartesianResidual.ringData k v)) /
        SourceExactRoot.sourceRoot 6 +
      sourceB k * inner ℝ (normalQ k) (TrueCirclePinSmooth.right (FullCartesianResidual.ringData k v)) /
        SourceExactRoot.sourceRoot 6 -
      inner ℝ (normalH k) (fullHub k v) / SourceExactRoot.sourceRoot 6 +
      (sourceA k+sourceB k-1) * v 22 := by
  let root := FullCartesianResidual.sourcePoint
  let dp : Full →L[ℝ] Point :=
    (fderiv ℝ (pinData (sourceSeed k)) (sourceData k)).comp (dataCLM k)
  have hp' : HasFDerivAt (pinData (sourceSeed k))
      (fderiv ℝ (pinData (sourceSeed k)) (sourceData k))
      (FullCartesianResidual.ringData k root) := by
    rw [FullCartesianResidual.ringData_source]
    exact (source_pinData_smooth k hk).differentiableAt (by norm_num) |>.hasFDerivAt
  have hp : HasFDerivAt (FullCartesianResidual.ringPin k) dp root :=
    hp'.comp root (dataCLM k).hasFDerivAt
  have hh : HasFDerivAt (fullHub k) (fullHubCLM k) root := (fullHubCLM k).hasFDerivAt
  have hd := hp.sub hh
  have hn : ‖(FullCartesianResidual.ringPin k - fullHub k) root‖ =
      SourceExactRoot.sourceRoot 6 := by
    change ‖FullCartesianResidual.ringPin k root - fullHub k root‖ = _
    rw [FullCartesianResidual.ringPin_source k hk, fullHub_source]
    exact source_normalH_norm k hk
  have he := norm_fderiv_apply hd hn SourceExactRoot.sourceRadius_pos v
  have hne : (FullCartesianResidual.ringPin k - fullHub k) root ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    have hpos : 0 < SourceExactRoot.sourceRoot 6 := SourceExactRoot.sourceRadius_pos
    linarith
  have hdiff := hd.differentiableAt.norm ℝ hne
  have hr : DifferentiableAt ℝ FullCartesianResidual.radius root :=
    (FullCartesianResidual.radius_smooth root).differentiableAt (by norm_num)
  change fderiv ℝ ((fun x : Full => ‖(FullCartesianResidual.ringPin k - fullHub k) x‖) -
    FullCartesianResidual.radius) root v = _
  rw [fderiv_sub hdiff hr]
  simp only [sub_apply]
  rw [he]
  have hR : fderiv ℝ FullCartesianResidual.radius root =
      (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ) :=
    (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ).hasFDerivAt.fderiv
  rw [hR]
  simp only [root, Pi.sub_apply, sub_apply, FullCartesianResidual.ringPin_source k hk,
    fullHub_source, dp, ContinuousLinearMap.comp_apply, dataCLM_apply, fullHubCLM_apply,
    ContinuousLinearMap.proj_apply]
  change inner ℝ (normalH k)
      (sourceVelocity k (FullCartesianResidual.ringData k v) - fullHub k v) /
        SourceExactRoot.sourceRoot 6 - v 22 = _
  exact source_length_covector_formula k hk (FullCartesianResidual.ringData k v) (fullHub k v)

end
end N11Formalization.SourceFanLengthCovector
#check @N11Formalization.SourceFanLengthCovector.source_length_covector_formula
#check @N11Formalization.SourceFanLengthCovector.norm_fderiv_apply
#check @N11Formalization.SourceFanLengthCovector.fanLength_source_fderiv
#print axioms N11Formalization.SourceFanLengthCovector.source_length_covector_formula
#print axioms N11Formalization.SourceFanLengthCovector.fanLength_source_fderiv
