import N11Formalization.SourceCentralGeometry
import N11Formalization.SourceFanRadiusDerivative

/-! Independent central-contact Cartesian23 differential and positive
LENGTH-to-circumradius conversion. The central pin is the genuine two-hub
intersection, not a ring-contact curve or a symmetric-only extension. -/
set_option autoImplicit false
namespace N11Formalization.SourceCentralDerivative
open N11Formalization CartesianReflectionSpace
open SourceCentralGeometry
open TrueCirclePinSmooth TruePinCartesianDifferential
noncomputable section

def centralDataLinear : Full →ₗ[ℝ] Data where
  toFun := FullCartesianResidual.centralData
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp [FullCartesianResidual.centralData]
  map_smul' := by
    intro r x
    funext i
    fin_cases i <;> simp [FullCartesianResidual.centralData, smul_eq_mul]

def centralDataCLM : Full →L[ℝ] Data := centralDataLinear.toContinuousLinearMap
@[simp] theorem centralDataCLM_apply (v : Full) :
    centralDataCLM v=FullCartesianResidual.centralData v := rfl

@[simp] theorem left_centralData (x : Full) :
    left (FullCartesianResidual.centralData x)=FullCartesianResidual.hubA x := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem right_centralData (x : Full) :
    right (FullCartesianResidual.centralData x)=FullCartesianResidual.hubB x := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem radius_centralData (x : Full) :
    FullCartesianResidual.centralData x 4=x 22 := rfl

def hubACLM : Full →L[ℝ] Point := leftCLM.comp centralDataCLM
def hubBCLM : Full →L[ℝ] Point := rightCLM.comp centralDataCLM
def ringCLM : Full →L[ℝ] Point := leftCLM.comp (SourceFanLengthCovector.dataCLM 6)

@[simp] theorem hubACLM_apply (v : Full) : hubACLM v=FullCartesianResidual.hubA v := by
  simp only [hubACLM, ContinuousLinearMap.comp_apply, centralDataCLM_apply,
    leftCLM_apply, left_centralData]
@[simp] theorem hubBCLM_apply (v : Full) : hubBCLM v=FullCartesianResidual.hubB v := by
  simp only [hubBCLM, ContinuousLinearMap.comp_apply, centralDataCLM_apply,
    rightCLM_apply, right_centralData]
@[simp] theorem ringCLM_apply (v : Full) : ringCLM v=FullCartesianResidual.ring v 6 := by
  simp only [ringCLM, ContinuousLinearMap.comp_apply, SourceFanLengthCovector.dataCLM_apply,
    leftCLM_apply, SourceFanRadiusDerivative.left_ringData]

theorem hubA_derivative (x : Full) :
    HasFDerivAt FullCartesianResidual.hubA hubACLM x := by
  have h := (left_hasFDerivAt (FullCartesianResidual.centralData x)).comp x
    centralDataCLM.hasFDerivAt
  simpa only [Function.comp_def, centralDataCLM_apply, left_centralData, hubACLM] using h
theorem hubB_derivative (x : Full) :
    HasFDerivAt FullCartesianResidual.hubB hubBCLM x := by
  have h := (right_hasFDerivAt (FullCartesianResidual.centralData x)).comp x
    centralDataCLM.hasFDerivAt
  simpa only [Function.comp_def, centralDataCLM_apply, right_centralData, hubBCLM] using h
theorem ring_derivative (x : Full) :
    HasFDerivAt (fun y : Full => FullCartesianResidual.ring y 6) ringCLM x :=
  SourceFanRadiusDerivative.left_ring_derivative 6 x

theorem pin_circle_equations_eventually :
    ∀ᶠ x in nhds FullCartesianResidual.sourcePoint,
      ‖FullCartesianResidual.centralPin x-FullCartesianResidual.hubA x‖^2=(x 22)^2 ∧
      ‖FullCartesianResidual.centralPin x-FullCartesianResidual.hubB x‖^2=(x 22)^2 := by
  let z := FullCartesianResidual.centralData
  let W := HorizontalTruePin.up
  let root := FullCartesianResidual.sourcePoint
  have hP : left (z root)≠right (z root) := HorizontalTruePin.source_hubs_distinct
  have hN : TrueCirclePin.normal W (left (z root)) (right (z root)) ≠ 0 := by
    change TrueCirclePin.normal HorizontalTruePin.up
      (HorizontalTruePin.horizontal (SourceExactRoot.sourceRoot 4))
      (HorizontalTruePin.horizontal (SourceExactRoot.sourceRoot 5)) ≠ 0
    rw [HorizontalTruePin.horizontal_normal]
    intro hzero
    have hn := HorizontalTruePin.norm_up
    rw [hzero, norm_zero] at hn
    norm_num at hn
  have hrad : 0 < TrueCirclePin.rad (left (z root)) (right (z root)) (z root 4) := by
    change 0 < TrueCirclePin.rad
      (HorizontalTruePin.horizontal (SourceExactRoot.sourceRoot 4))
      (HorizontalTruePin.horizontal (SourceExactRoot.sourceRoot 5)) (SourceExactRoot.sourceRoot 6)
    rw [HorizontalTruePin.horizontal_rad]
    exact HorizontalTruePin.source_central_radicand_pos
  have hd := (right_smooth (z root)).sub (left_smooth (z root))
  have heD := hd.continuousAt.eventually_ne (sub_ne_zero.mpr hP.symm)
  have heN := (normal_smooth W (z root) hP).continuousAt.eventually_ne hN
  have her := (rad_smooth (z root)).continuousAt.eventually (eventually_gt_nhds hrad)
  have he : ∀ᶠ q in nhds (z root),
      ‖pinData W q-left q‖^2=(q 4)^2 ∧ ‖pinData W q-right q‖^2=(q 4)^2 := by
    filter_upwards [heD,heN,her] with q hqD hqN hqr
    exact TrueCirclePin.pin_circle_equations _ _ _ _ (by
      intro hzero
      apply hqD
      rw [hzero,sub_self]) hqN hqr.le
  have hx := (FullCartesianResidual.centralData_smooth root).continuousAt.eventually he
  simpa only [z, W, root, FullCartesianResidual.centralPin,
    left_centralData, right_centralData, radius_centralData]
    using hx

theorem pin_normal_velocity (v : Full) :
    inner ℝ nP (fderiv ℝ FullCartesianResidual.centralPin FullCartesianResidual.sourcePoint v-
      FullCartesianResidual.hubA v)=R*v 22 ∧
    inner ℝ nQ (fderiv ℝ FullCartesianResidual.centralPin FullCartesianResidual.sourcePoint v-
      FullCartesianResidual.hubB v)=R*v 22 := by
  let root := FullCartesianResidual.sourcePoint
  let u : ℝ → Full := fun s => root+s • v
  have hu : HasDerivAt u v 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add root
    change HasDerivAt (fun s : ℝ => root+s • v) (1 • v) 0 at h
    rw [one_smul] at h
    exact h
  have hu0 : u 0=FullCartesianResidual.sourcePoint := by simp [u,root]
  have hz := (FullCartesianResidual.centralPin_source_smooth.differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hu hu0.symm
  have hP := (hubA_derivative (u 0)).comp_hasDerivAt 0 hu
  have hQ := (hubB_derivative (u 0)).comp_hasDerivAt 0 hu
  have hR := (ContinuousLinearMap.proj (22 : Fin 23) :
    Full →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hu
  have he := pin_circle_equations_eventually
  rw [← hu0] at he
  have hh := hu.continuousAt.eventually he
  have hp := PinCircleDifferential.circle_velocity_row hz hP hR (hh.mono fun s hs => hs.1)
  have hq := PinCircleDifferential.circle_velocity_row hz hQ hR (hh.mono fun s hs => hs.2)
  have hPA : FullCartesianResidual.hubA FullCartesianResidual.sourcePoint=P := rfl
  have hQB : FullCartesianResidual.hubB FullCartesianResidual.sourcePoint=Q := rfl
  have hr0 : FullCartesianResidual.sourcePoint 22=R := rfl
  constructor
  · simpa only [Function.comp_def, hu0, FullCartesianResidual.centralPin_source,
      hPA, hubACLM_apply, ContinuousLinearMap.proj_apply, hr0, nP, U] using hp
  · simpa only [Function.comp_def, hu0, FullCartesianResidual.centralPin_source,
      hQB, hubBCLM_apply, ContinuousLinearMap.proj_apply, hr0, nQ, U] using hq

def centralLength (x : Full) : ℝ :=
  dist (FullCartesianResidual.centralPin x) (FullCartesianResidual.ring x 6)-x 22

theorem centralLength_fderiv (v : Full) :
    fderiv ℝ centralLength FullCartesianResidual.sourcePoint v =
      a*inner ℝ nP (FullCartesianResidual.hubA v)/R +
      b*inner ℝ nQ (FullCartesianResidual.hubB v)/R -
      inner ℝ nH (FullCartesianResidual.ring v 6)/R+(a+b-1)*v 22 := by
  let root := FullCartesianResidual.sourcePoint
  have hp := (FullCartesianResidual.centralPin_source_smooth.differentiableAt
    (by norm_num)).hasFDerivAt
  have hh := ring_derivative root
  have hd := hp.sub hh
  have hU : FullCartesianResidual.centralPin root=U := FullCartesianResidual.centralPin_source
  have hH : FullCartesianResidual.ring root 6=H := FullCartesianResidual.ring_pack _ 6
  have hnorm : ‖(FullCartesianResidual.centralPin -
      fun y : Full => FullCartesianResidual.ring y 6) root‖=R := by
    change ‖FullCartesianResidual.centralPin root-FullCartesianResidual.ring root 6‖=R
    rw [hU,hH]
    exact SourceCentralGeometry.source_distances.2.2
  have hdiff := hd.differentiableAt.norm ℝ (by
    apply norm_ne_zero_iff.mp
    rw [hnorm]
    have hRpos : 0<R := SourceExactRoot.sourceRadius_pos
    exact ne_of_gt hRpos)
  have hRpos : 0<R := SourceExactRoot.sourceRadius_pos
  have he := SourceFanLengthCovector.norm_fderiv_apply hd hnorm hRpos v
  have hr : DifferentiableAt ℝ (fun x : Full => x 22) root := by fun_prop
  change fderiv ℝ ((fun x : Full => ‖(FullCartesianResidual.centralPin-
    fun y : Full => FullCartesianResidual.ring y 6) x‖)-(fun x : Full => x 22)) root v = _
  rw [fderiv_sub hdiff hr]
  simp only [sub_apply]
  rw [he]
  obtain ⟨hvP,hvQ⟩ := pin_normal_velocity v
  rw [inner_sub_right] at hvP hvQ
  have hinner := congrArg (fun n : Point => inner ℝ n
    (fderiv ℝ FullCartesianResidual.centralPin root v)) normalH_expansion
  simp only [inner_add_left, real_inner_smul_left] at hinner
  have hdR := (ContinuousLinearMap.proj (22 : Fin 23) :
    Full →L[ℝ] ℝ).hasFDerivAt (x := root) |>.fderiv
  change fderiv ℝ (fun x : Full => x 22) FullCartesianResidual.sourcePoint =
    (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ) at hdR
  rw [hdR]
  change FullCartesianResidual.centralPin FullCartesianResidual.sourcePoint=U at hU
  change FullCartesianResidual.ring FullCartesianResidual.sourcePoint 6=H at hH
  simp only [Pi.sub_apply, hU, hH, sub_apply, ringCLM_apply,
    ContinuousLinearMap.proj_apply]
  change inner ℝ nH (fderiv ℝ FullCartesianResidual.centralPin root v-
    FullCartesianResidual.ring v 6)/R-v 22=_
  rw [inner_sub_right, hinner]
  have hR0 : R≠0 := ne_of_gt SourceExactRoot.sourceRadius_pos
  field_simp [hR0]
  linear_combination a*hvP+b*hvQ

theorem centralRadius_fderiv (v : Full) :
    fderiv ℝ centralRadius FullCartesianResidual.sourcePoint v =
      -(betaP*inner ℝ nP (FullCartesianResidual.hubA v)+
        betaQ*inner ℝ nQ (FullCartesianResidual.hubB v)+
        betaH*inner ℝ nH (FullCartesianResidual.ring v 6))/R := by
  let root := FullCartesianResidual.sourcePoint
  let u : ℝ → Full := fun s => root+s • v
  have hu : HasDerivAt u v 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add root
    change HasDerivAt (fun s : ℝ => root+s • v) (1 • v) 0 at h
    rw [one_smul] at h
    exact h
  have hu0 : u 0=FullCartesianResidual.sourcePoint := by simp [u,root]
  have hz := (center_source_smooth.differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hu hu0.symm
  have hp := (hubA_derivative (u 0)).comp_hasDerivAt 0 hu
  have hq := (hubB_derivative (u 0)).comp_hasDerivAt 0 hu
  have hh := (ring_derivative (u 0)).comp_hasDerivAt 0 hu
  have hr := (centralRadius_source_smooth.differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hu hu0.symm
  have he := circle_equations_eventually
  rw [← hu0] at he
  have he' := hu.continuousAt.eventually he
  have hp0 : FullCartesianResidual.hubA FullCartesianResidual.sourcePoint=P := rfl
  have hq0 : FullCartesianResidual.hubB FullCartesianResidual.sourcePoint=Q := rfl
  have hh0 : FullCartesianResidual.ring FullCartesianResidual.sourcePoint 6=H :=
    FullCartesianResidual.ring_pack _ 6
  have hc : (center ∘ u) 0 =
      betaP • (FullCartesianResidual.hubA ∘ u) 0+
      betaQ • (FullCartesianResidual.hubB ∘ u) 0+
      betaH • (fun s => FullCartesianResidual.ring (u s) 6) 0 := by
    simp only [Function.comp_def,hu0,center_source,hp0,hq0,hh0]
    exact beta_center_identity
  have h := CircumradiusDifferential.weighted_radius_velocity betaP betaQ betaH
    hz hp hq hh hr beta_sum_one hc (he'.mono fun s hs => hs.1)
      (he'.mono fun s hs => hs.2.1) (he'.mono fun s hs => hs.2.2)
  have hv : R*fderiv ℝ centralRadius FullCartesianResidual.sourcePoint v =
      -(betaP*inner ℝ nP (FullCartesianResidual.hubA v)+
        betaQ*inner ℝ nQ (FullCartesianResidual.hubB v)+
        betaH*inner ℝ nH (FullCartesianResidual.ring v 6)) := by
    simpa only [Function.comp_def,hu0,centralRadius_source,center_source,hp0,hq0,hh0,
      hubACLM_apply,hubBCLM_apply,ringCLM_apply,nP,nQ,nH] using h
  have hR0 : R≠0 := ne_of_gt SourceExactRoot.sourceRadius_pos
  apply (eq_div_iff hR0).mpr
  simpa only [mul_comm] using hv

def radiusExcess (x : Full) : ℝ := centralRadius x-x 22

/-- Independent central contact positive gradient conversion, not borrowed
from the four ring contacts. Every source/curve/differentiability premise paid. -/
theorem length_to_circumradius (v : Full) :
    fderiv ℝ centralLength FullCartesianResidual.sourcePoint v =
      conversion*fderiv ℝ radiusExcess FullCartesianResidual.sourcePoint v := by
  have hd := (centralRadius_source_smooth.differentiableAt
    (by norm_num)).hasFDerivAt.sub
      (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt radiusExcess
    (fderiv ℝ centralRadius FullCartesianResidual.sourcePoint -
      (ContinuousLinearMap.proj (22 : Fin 23) : Full →L[ℝ] ℝ))
    FullCartesianResidual.sourcePoint at hd
  rw [centralLength_fderiv, hd.fderiv]
  simp only [sub_apply, ContinuousLinearMap.proj_apply]
  rw [centralRadius_fderiv]
  have hc : conversion≠0 := ne_of_gt conversion_pos
  have hR0 : R≠0 := ne_of_gt SourceExactRoot.sourceRadius_pos
  unfold betaP betaQ betaH
  field_simp [hc,hR0]
  unfold conversion
  ring

end
end N11Formalization.SourceCentralDerivative
#check @N11Formalization.SourceCentralDerivative.centralRadius_fderiv
#check @N11Formalization.SourceCentralDerivative.length_to_circumradius
#print axioms N11Formalization.SourceCentralDerivative.length_to_circumradius
