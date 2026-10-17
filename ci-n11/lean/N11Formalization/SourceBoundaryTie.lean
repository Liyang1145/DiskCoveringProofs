import N11Formalization.TrueBoundaryTie
import N11Formalization.SourceFanRadiusDerivative

/-! Actual source branch and smooth genuine unit-circle tie in all independent
Cartesian23 centre directions, for the five reflection-orbit representatives
k=0,1,2,3,8. Unit-circle/equidistance equations hold on a neighbourhood and
radius is distance to the actual tie. No source normal/radicand premise remains.
Physical boundary-gap/tie-gradient proportionality remains separate. -/
set_option autoImplicit false
namespace N11Formalization.SourceBoundaryTie
open N11Formalization CartesianReflectionSpace
noncomputable section

private theorem chord_read_zero : (1/10 : ℚ) ≤
    (ndRingBox ndBox 0 1).lo-(ndRingBox ndBox 1 1).hi := by nd_eval

theorem source_chord_ne (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ringCenter SourceExactRoot.sourceRoot k≠ringCenter SourceExactRoot.sourceRoot (k+1) := by
  rcases hk with hzero | hfan
  · subst k
    rw [nd_fin_succ_0]
    have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
    exact point_ne_of_coord (i := 1) (a := 1/10) (by norm_num)
      (le_abs_sub_of_lo_sub_hi (ndRingBox_mem hb 0 1) (ndRingBox_mem hb 1 1)
        (by norm_num) chord_read_zero)
  · exact RootPinNormalConsumer.source_contact_chord_ne k hfan

theorem source_centers_inside (k : Fin 9) : ‖ringCenter SourceExactRoot.sourceRoot k‖<1 := by
  rw [ringCenter_eq_smul,norm_smul,circleMap_norm,mul_one,Real.norm_eq_abs,
    abs_of_pos (CartesianPolarFrame.source_rho_pos k)]
  have ha := SourceWidthNondegenerate.source_width_bounds k
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := angleVec SourceExactRoot.sourceRoot k)
    (le_refl 0) (by linarith [ha.2,Real.pi_pos]) ha.1
  rw [Real.cos_zero] at hc
  unfold rhoK
  linarith [Real.sqrt_nonneg ((SourceExactRoot.sourceRoot 6)^2-
    (Real.sin (angleVec SourceExactRoot.sourceRoot k))^2)]

theorem source_endpoint_distances (k : Fin 9) :
    ‖arcEnd SourceExactRoot.sourceRoot k-ringCenter SourceExactRoot.sourceRoot k‖ =
      SourceExactRoot.sourceRoot 6 ∧
    ‖arcEnd SourceExactRoot.sourceRoot k-ringCenter SourceExactRoot.sourceRoot (k+1)‖ =
      SourceExactRoot.sourceRoot 6 := by
  have hs : ∀ j : Fin 9, Real.sin (angleVec SourceExactRoot.sourceRoot j)^2 ≤
      (SourceExactRoot.sourceRoot 6)^2 := fun j =>
    le_of_lt (by linarith [SourceWidthNondegenerate.source_radicand_pos j])
  have hR : 0≤SourceExactRoot.sourceRoot 6 := le_of_lt SourceExactRoot.sourceRadius_pos
  constructor
  · simpa only [dist_eq_norm] using
      FlashRootNetwork.dist_arcEnd_ringCenter_self SourceExactRoot.sourceRoot hs hR k
  · simpa only [dist_eq_norm] using dist_arcEnd_ringCenter_succ SourceExactRoot.sourceRoot hs hR k

def sourceSeed (k : Fin 9) : Point :=
  arcEnd SourceExactRoot.sourceRoot k-TrueBoundaryTie.foot
    (ringCenter SourceExactRoot.sourceRoot k) (ringCenter SourceExactRoot.sourceRoot (k+1))

theorem sourceSeed_ne (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    sourceSeed k≠0 :=
  TrueBoundaryTie.seed_ne_of_inside (source_chord_ne k hk)
    (FanFoutPos.norm_arcEnd _ k)
    ((source_endpoint_distances k).1.trans (source_endpoint_distances k).2.symm)
    (source_centers_inside k) (source_centers_inside (k+1))

theorem source_normal (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    TrueCirclePin.normal (sourceSeed k) (ringCenter SourceExactRoot.sourceRoot k)
      (ringCenter SourceExactRoot.sourceRoot (k+1))=sourceSeed k :=
  TrueBoundaryTie.normal_seed (source_chord_ne k hk)
    ((source_endpoint_distances k).1.trans (source_endpoint_distances k).2.symm)

theorem source_rad_pos (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    0<TrueBoundaryTie.rad (ringCenter SourceExactRoot.sourceRoot k)
      (ringCenter SourceExactRoot.sourceRoot (k+1)) := by
  rw [TrueBoundaryTie.source_rad (source_chord_ne k hk) (FanFoutPos.norm_arcEnd _ k)
    ((source_endpoint_distances k).1.trans (source_endpoint_distances k).2.symm)]
  exact sq_pos_of_pos (norm_pos_iff.mpr (sourceSeed_ne k hk))

theorem source_tieData_value (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    TrueBoundaryTie.tieData (sourceSeed k) (TrueCirclePinSmooth.sourceData k) =
      arcEnd SourceExactRoot.sourceRoot k := by
  unfold TrueBoundaryTie.tieData
  rw [TrueCirclePinSmooth.left_source,TrueCirclePinSmooth.right_source]
  exact TrueBoundaryTie.tie_source (source_chord_ne k hk) (FanFoutPos.norm_arcEnd _ k)
    ((source_endpoint_distances k).1.trans (source_endpoint_distances k).2.symm) (sourceSeed_ne k hk)

theorem source_tieData_smooth (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ContDiffAt ℝ 1 (TrueBoundaryTie.tieData (sourceSeed k)) (TrueCirclePinSmooth.sourceData k) := by
  apply TrueBoundaryTie.tieData_smooth
  · simpa only [TrueCirclePinSmooth.left_source,TrueCirclePinSmooth.right_source] using source_chord_ne k hk
  · simp only [TrueCirclePinSmooth.left_source,TrueCirclePinSmooth.right_source,source_normal k hk]
    exact sourceSeed_ne k hk
  · simpa only [TrueCirclePinSmooth.left_source,TrueCirclePinSmooth.right_source] using
      ne_of_gt (source_rad_pos k hk)

def tieFull (k : Fin 9) (x : Full) : Point :=
  TrueBoundaryTie.tieData (sourceSeed k) (FullCartesianResidual.ringData k x)
def radiusFull (k : Fin 9) (x : Full) : ℝ :=
  ‖tieFull k x-FullCartesianResidual.ring x k‖
def radiusExcess (k : Fin 9) (x : Full) : ℝ := radiusFull k x-x 22

theorem tieFull_source (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    tieFull k FullCartesianResidual.sourcePoint=arcEnd SourceExactRoot.sourceRoot k := by
  rw [tieFull,FullCartesianResidual.ringData_source]
  exact source_tieData_value k hk

theorem radiusFull_source (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    radiusFull k FullCartesianResidual.sourcePoint=SourceExactRoot.sourceRoot 6 := by
  rw [radiusFull,tieFull_source k hk,FullCartesianResidual.sourcePoint,
    FullCartesianResidual.ring_pack]
  exact (source_endpoint_distances k).1

theorem tieFull_source_smooth (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ContDiffAt ℝ 1 (tieFull k) FullCartesianResidual.sourcePoint := by
  have hs := source_tieData_smooth k hk
  rw [← FullCartesianResidual.ringData_source k] at hs
  exact hs.comp FullCartesianResidual.sourcePoint
    (FullCartesianResidual.ringData_smooth k FullCartesianResidual.sourcePoint)

theorem radiusFull_source_smooth (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ContDiffAt ℝ 1 (radiusFull k) FullCartesianResidual.sourcePoint := by
  apply ((tieFull_source_smooth k hk).sub (FullCartesianResidual.ring_smooth k _)).norm ℝ
  apply norm_ne_zero_iff.mp
  change radiusFull k FullCartesianResidual.sourcePoint≠0
  rw [radiusFull_source k hk]
  exact ne_of_gt SourceExactRoot.sourceRadius_pos

theorem tie_equations_eventually (k : Fin 9) (hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ∀ᶠ x in nhds FullCartesianResidual.sourcePoint,
      ‖tieFull k x‖=1 ∧
      ‖tieFull k x-FullCartesianResidual.ring x k‖ =
        ‖tieFull k x-FullCartesianResidual.ring x (k+1)‖ := by
  let z := TrueCirclePinSmooth.sourceData k
  have hP : TrueCirclePinSmooth.left z≠TrueCirclePinSmooth.right z := source_chord_ne k hk
  have hN : TrueCirclePin.normal (sourceSeed k) (TrueCirclePinSmooth.left z) (TrueCirclePinSmooth.right z)≠0 := by
    simp only [z,TrueCirclePinSmooth.left_source,TrueCirclePinSmooth.right_source,source_normal k hk]
    exact sourceSeed_ne k hk
  have hsF := TrueBoundaryTie.foot_smooth z hP
  have hNsm := TrueCirclePinSmooth.normal_smooth (sourceSeed k) z hP
  have hDsm := (TrueCirclePinSmooth.right_smooth z).sub (TrueCirclePinSmooth.left_smooth z)
  have hrad : 0<TrueBoundaryTie.rad (TrueCirclePinSmooth.left z) (TrueCirclePinSmooth.right z) :=
    source_rad_pos k hk
  have hrsm : ContDiffAt ℝ 1 (fun y : TrueBoundaryTie.Data =>
      TrueBoundaryTie.rad (TrueCirclePinSmooth.left y) (TrueCirclePinSmooth.right y)) z :=
    contDiffAt_const.sub (hsF.norm_sq ℝ)
  have he : ∀ᶠ y in nhds z,
      ‖TrueBoundaryTie.tieData (sourceSeed k) y‖=1 ∧
      ‖TrueBoundaryTie.tieData (sourceSeed k) y-TrueCirclePinSmooth.left y‖ =
        ‖TrueBoundaryTie.tieData (sourceSeed k) y-TrueCirclePinSmooth.right y‖ := by
    filter_upwards [hDsm.continuousAt.eventually_ne (sub_ne_zero.mpr hP.symm),
      hNsm.continuousAt.eventually_ne hN,
      hrsm.continuousAt.eventually (eventually_gt_nhds hrad)] with y hyD hyN hyr
    exact TrueBoundaryTie.tie_equations _ _ _ (by
      intro h
      apply hyD
      rw [h,sub_self]) hyN hyr.le
  have hz : FullCartesianResidual.ringData k FullCartesianResidual.sourcePoint=z :=
    FullCartesianResidual.ringData_source k
  rw [← hz] at he
  have hpull := (FullCartesianResidual.ringData_smooth k FullCartesianResidual.sourcePoint).continuousAt.eventually he
  simpa only [tieFull,SourceFanRadiusDerivative.left_ringData,
    SourceFanRadiusDerivative.right_ringData] using hpull

end
end N11Formalization.SourceBoundaryTie
#check @N11Formalization.SourceBoundaryTie.tieFull_source
#check @N11Formalization.SourceBoundaryTie.radiusFull_source_smooth
#check @N11Formalization.SourceBoundaryTie.tie_equations_eventually
#print axioms N11Formalization.SourceBoundaryTie.tieFull_source
#print axioms N11Formalization.SourceBoundaryTie.tie_equations_eventually
