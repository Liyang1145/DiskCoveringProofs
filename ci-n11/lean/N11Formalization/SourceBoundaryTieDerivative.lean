import N11Formalization.SourceBoundaryTie

/-! Genuine unit-circle tie radius derivative. The tie tangent is eliminated
using its unit-circle equation and an explicit two-centre normal combination.
Source branch/rank/neighbourhood equations are paid. eta is an exact determinant
ratio; positivity and physical gap-to-radius scaling remain separate. -/
set_option autoImplicit false
namespace N11Formalization.SourceBoundaryTieDerivative
open N11Formalization CartesianReflectionSpace PinTangentGeometry
noncomputable section

def T (k : Fin 9) : Point := arcEnd SourceExactRoot.sourceRoot k
def D (k : Fin 9) : Point := ringCenter SourceExactRoot.sourceRoot (k+1)-ringCenter SourceExactRoot.sourceRoot k
def nP (k : Fin 9) : Point := T k-ringCenter SourceExactRoot.sourceRoot k
def nQ (k : Fin 9) : Point := T k-ringCenter SourceExactRoot.sourceRoot (k+1)

theorem source_tangent_rank (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    det (T k) (D k)≠0 := by
  have ho := TrueBoundaryTie.seed_orthogonal (SourceBoundaryTie.source_chord_ne k hk)
    ((SourceBoundaryTie.source_endpoint_distances k).1.trans
      (SourceBoundaryTie.source_endpoint_distances k).2.symm)
  have hg := det_sq_gram (SourceBoundaryTie.sourceSeed k) (D k)
  change inner ℝ (SourceBoundaryTie.sourceSeed k) (D k)=0 at ho
  rw [ho,zero_pow (by decide : (2 : ℕ)≠0),sub_zero] at hg
  have hn : 0<‖SourceBoundaryTie.sourceSeed k‖ := norm_pos_iff.mpr (SourceBoundaryTie.sourceSeed_ne k hk)
  have hd : 0<‖D k‖ := norm_pos_iff.mpr
    (sub_ne_zero.mpr (SourceBoundaryTie.source_chord_ne k hk).symm)
  have he : det (SourceBoundaryTie.sourceSeed k) (D k)=det (T k) (D k) := by
    unfold SourceBoundaryTie.sourceSeed TrueBoundaryTie.foot T D det
    simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  rw [he] at hg
  intro hz
  rw [hz,zero_pow (by decide : (2 : ℕ)≠0)] at hg
  have hpos := mul_pos (sq_pos_of_pos hn) (sq_pos_of_pos hd)
  linarith

def eta (k : Fin 9) : ℝ := -det (T k) (nQ k)/det (T k) (D k)
def normalCombination (k : Fin 9) : Point := eta k • nP k+(1-eta k) • nQ k
def radialCoefficient (k : Fin 9) : ℝ := inner ℝ (T k) (normalCombination k)

theorem source_radial_combination (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    normalCombination k=radialCoefficient k • T k := by
  have hd : det (T k) (nP k)-det (T k) (nQ k)=det (T k) (D k) := by
    unfold nP nQ D det
    simp only [PiLp.sub_apply]
    ring
  have hz : det (T k) (normalCombination k)=0 := by
    have he : det (T k) (normalCombination k)=
        eta k*(det (T k) (nP k)-det (T k) (nQ k))+det (T k) (nQ k) := by
      unfold normalCombination det
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      ring
    rw [he,hd,eta]
    field_simp [source_tangent_rank k hk] <;> ring
  have he := SourceFanLengthCovector.normal_expansion (T k) (D k) (normalCombination k)
    (source_tangent_rank k hk)
  have hB : SourceFanLengthCovector.coefficientB (T k) (D k) (normalCombination k)=0 := by
    rw [SourceFanLengthCovector.coefficientB,hz,zero_div]
  rw [hB,zero_smul,add_zero] at he
  have hA : radialCoefficient k=
      SourceFanLengthCovector.coefficientA (T k) (D k) (normalCombination k) := by
    have hi := congrArg (fun n : Point => inner ℝ (T k) n) he
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,
      show ‖T k‖=1 from FanFoutPos.norm_arcEnd _ k] at hi
    simpa only [radialCoefficient,one_pow,mul_one] using hi
  rw [hA]
  exact he

private theorem radius_velocity {X P Q : ℝ → Point} {R : ℝ → ℝ}
    {dx dp dq : Point} {dr t : ℝ} (e g : ℝ)
    (hx : HasDerivAt X dx t) (hp : HasDerivAt P dp t) (hq : HasDerivAt Q dq t)
    (hr : HasDerivAt R dr t)
    (hc : e • (X t-P t)+(1-e) • (X t-Q t)=g • X t)
    (hunit : ∀ᶠ s in nhds t, ‖X s‖=1)
    (hP : ∀ᶠ s in nhds t, ‖X s-P s‖^2=(R s)^2)
    (hQ : ∀ᶠ s in nhds t, ‖X s-Q s‖^2=(R s)^2) :
    R t*dr=-(e*inner ℝ (X t-P t) dp+(1-e)*inner ℝ (X t-Q t) dq) := by
  have heU : ∀ᶠ s in nhds t, ‖X s-(0 : Point)‖^2=(1 : ℝ)^2 := by
    filter_upwards [hunit] with s hs
    simpa only [sub_zero,hs]
  have hU := PinCircleDifferential.circle_velocity_row hx
    (hasDerivAt_const t (0 : Point)) (hasDerivAt_const t (1 : ℝ)) heU
  simp only [sub_zero,mul_zero] at hU
  have hA := PinCircleDifferential.circle_velocity_row hx hp hr hP
  have hB := PinCircleDifferential.circle_velocity_row hx hq hr hQ
  have hi := congrArg (fun n : Point => inner ℝ n dx) hc
  rw [inner_add_left,real_inner_smul_left,real_inner_smul_left,real_inner_smul_left,hU,mul_zero] at hi
  rw [inner_sub_right] at hA hB
  linear_combination -e*hA-(1-e)*hB+hi

/-- Actual full Cartesian23 tie-radius derivative; centre velocities only,
no supplied tie curve/rank/normal or source distance hypotheses. -/
theorem radiusFull_source_fderiv (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8)
    (v : Full) :
    fderiv ℝ (SourceBoundaryTie.radiusFull k) FullCartesianResidual.sourcePoint v =
      -(eta k*inner ℝ (nP k) (FullCartesianResidual.ring v k)+
        (1-eta k)*inner ℝ (nQ k) (FullCartesianResidual.ring v (k+1))) /
        SourceExactRoot.sourceRoot 6 := by
  let root := FullCartesianResidual.sourcePoint
  let u : ℝ → Full := fun s => root+s • v
  have hu : HasDerivAt u v 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add root
    change HasDerivAt (fun s : ℝ => root+s • v) (1 • v) 0 at h
    rw [one_smul] at h
    exact h
  have hu0 : u 0=FullCartesianResidual.sourcePoint := by simp [u,root]
  have hx := ((SourceBoundaryTie.tieFull_source_smooth k hk).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hu hu0.symm
  have hp := (SourceFanRadiusDerivative.left_ring_derivative k (u 0)).comp_hasDerivAt 0 hu
  have hq := (SourceFanRadiusDerivative.right_ring_derivative k (u 0)).comp_hasDerivAt 0 hu
  have hr := ((SourceBoundaryTie.radiusFull_source_smooth k hk).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hu hu0.symm
  have he := SourceBoundaryTie.tie_equations_eventually k hk
  rw [← hu0] at he
  have hep := hu.continuousAt.eventually he
  have hroot (j : Fin 9) : FullCartesianResidual.ring FullCartesianResidual.sourcePoint j=
      ringCenter SourceExactRoot.sourceRoot j := FullCartesianResidual.ring_pack _ j
  have hc : eta k • ((SourceBoundaryTie.tieFull k ∘ u) 0-
        (fun s => FullCartesianResidual.ring (u s) k) 0)+
      (1-eta k) • ((SourceBoundaryTie.tieFull k ∘ u) 0-
        (fun s => FullCartesianResidual.ring (u s) (k+1)) 0)=
      radialCoefficient k • (SourceBoundaryTie.tieFull k ∘ u) 0 := by
    simp only [Function.comp_def,hu0,SourceBoundaryTie.tieFull_source k hk,hroot]
    exact source_radial_combination k hk
  have hPA : ∀ᶠ s in nhds (0 : ℝ), ‖SourceBoundaryTie.tieFull k (u s)-
      FullCartesianResidual.ring (u s) k‖^2=(SourceBoundaryTie.radiusFull k (u s))^2 :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have hQA : ∀ᶠ s in nhds (0 : ℝ), ‖SourceBoundaryTie.tieFull k (u s)-
      FullCartesianResidual.ring (u s) (k+1)‖^2=(SourceBoundaryTie.radiusFull k (u s))^2 := by
    filter_upwards [hep] with s hs
    exact congrArg (fun r : ℝ => r^2) hs.2.symm
  have h := radius_velocity (eta k) (radialCoefficient k) hx hp hq hr hc
    (hep.mono fun s hs => hs.1) hPA hQA
  have hv : SourceExactRoot.sourceRoot 6 *
      fderiv ℝ (SourceBoundaryTie.radiusFull k) FullCartesianResidual.sourcePoint v =
      -(eta k*inner ℝ (nP k) (FullCartesianResidual.ring v k)+
        (1-eta k)*inner ℝ (nQ k) (FullCartesianResidual.ring v (k+1))) := by
    simpa only [Function.comp_def,hu0,SourceBoundaryTie.radiusFull_source k hk,
      SourceBoundaryTie.tieFull_source k hk,hroot,ContinuousLinearMap.comp_apply,
      SourceFanLengthCovector.dataCLM_apply,TruePinCartesianDifferential.leftCLM_apply,
      TruePinCartesianDifferential.rightCLM_apply,SourceFanRadiusDerivative.left_ringData,
      SourceFanRadiusDerivative.right_ringData,nP,nQ,T] using h
  have hR : SourceExactRoot.sourceRoot 6≠0 := ne_of_gt SourceExactRoot.sourceRadius_pos
  apply (eq_div_iff hR).mpr
  simpa only [mul_comm] using hv

end
end N11Formalization.SourceBoundaryTieDerivative
#check @N11Formalization.SourceBoundaryTieDerivative.source_tangent_rank
#check @N11Formalization.SourceBoundaryTieDerivative.radiusFull_source_fderiv
#print axioms N11Formalization.SourceBoundaryTieDerivative.radiusFull_source_fderiv
