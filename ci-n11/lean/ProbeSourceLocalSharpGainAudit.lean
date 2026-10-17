import N11Formalization

/-! Real root imported localgain/cross consumers. Full-domain goal is not
inferred from pin/ball/canonical witness. All51 primal rows retained. -/
set_option autoImplicit false
open N11Formalization
#check @SourceCrossGeometry.rawCross_coordinates
#check @SourceCrossPacket.CB_mem
#check @SourceCrossPacket.frobenius_certificate
#check @SourceCrossPacket.actual_raw_frobenius
#check @SourceActualCrossBound.actual_pinned_frobenius
#check @SourceActualCrossBound.actual_pinned_operator
#check @SourceActualResponseBound.anchorWeight_two_spokes
#check @SourceActualResponseBound.actual_anchorWeight
#check @SourceActualResponseBound.actual_response_bound
#check @SourceLocalSharpGain.displacedAnchors_circle
#check @SourceLocalSharpGain.carrying_squared_length
#check @SourceLocalSharpGain.actual_directional
#check @SourceLocalSharpGain.actual_local_gain
#check @SourceLocalSharpGain.feasible_radius_lower
#print SourceLocalSharpGain.displacedAnchors
#print SourceRelativeMetric.R
#print SourceRelativeAdaptiveConsumer.power
#print ResumeNetwork.Feasible
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#print axioms SourceCrossGeometry.rawCross_coordinates
#print axioms SourceCrossPacket.CB_mem
#print axioms SourceCrossPacket.actual_raw_frobenius
#print axioms SourceActualCrossBound.actual_pinned_operator
#print axioms SourceActualResponseBound.actual_response_bound
#print axioms SourceLocalSharpGain.actual_directional
#print axioms SourceLocalSharpGain.actual_local_gain
#print axioms SourceLocalSharpGain.feasible_radius_lower

example (x z : Fin 9 → ℝ) (hx : x 6=0) (hz : z 6=0) :
    |∑ i : Fin 9,∑ j : Fin 9,FlashLocal.Cmat SourceResponseFluxIdentity.sourceResponse
      SourceResponseFluxIdentity.sourceAngle i j*x i*z j|≤
      (179/5000 : ℝ)*Real.sqrt (∑ i : Fin 9,x i^2)*Real.sqrt (∑ j : Fin 9,z j^2) :=
  SourceActualCrossBound.actual_pinned_operator x z hx hz

example (x : Fin 9 → ℝ) (hp : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,x j^2)≤(729/50000 : ℝ)) :
    (∑ j : Fin 9,x j^2)/100000≤
      ResumeNetwork.V2 (SourceLocalSharpGain.displacedAnchors x)-SourceExactRoot.sourceRadius^2 :=
  SourceLocalSharpGain.actual_local_gain x hp hr

example (x : Fin 9 → ℝ) (hp : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,x j^2)≤(729/50000 : ℝ))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceLocalSharpGain.displacedAnchors x) C Z r) :
    SourceExactRoot.sourceRadius≤r :=
  SourceLocalSharpGain.feasible_radius_lower x hp hr C Z r hf

example : SourceLocalSharpGain.displacedAnchors (fun _ => 0)=
    SourcePositiveHarmonicConsumer.sourceAnchors := by
  funext j
  rw [SourceLocalSharpGain.displacedAnchors_circle]
  simpa only [add_zero] using (SourceResponseFluxIdentity.sourceAnchors_circle j).symm
example : ResumeNetwork.V2 (SourceLocalSharpGain.displacedAnchors (fun _ => 0))=
    SourceExactRoot.sourceRadius^2 := by
  have he : SourceLocalSharpGain.displacedAnchors (fun _ => 0)=
      SourcePositiveHarmonicConsumer.sourceAnchors := by
    funext j
    rw [SourceLocalSharpGain.displacedAnchors_circle]
    simpa only [add_zero] using (SourceResponseFluxIdentity.sourceAnchors_circle j).symm
  rw [he]
  exact SourceSharpEnergyCalibration.source_oracle_eq

-- Coordinate calibration of tangent/radial sign and NO factor2:
example (θ : ℝ) :
    inner ℝ (FlashLocal.circleTangent θ) (circleMap θ)=0 := by
  rw [PinTangentGeometry.inner_coords]
  simp [FlashLocal.circleTangent,N11Formalization.circleMap]
  ring
example : FlashLocal.Cmat (fun (_ _ : Fin 9) => (3 : ℝ))
    (fun i : Fin 9 => if i=0 then 0 else Real.pi/2) 0 1=3 := by
  unfold FlashLocal.Cmat
  rw [PinTangentGeometry.inner_coords]
  norm_num [FlashLocal.circleTangent,N11Formalization.circleMap]
example : (ResumeLocalIncidence.sourceFaces 0 1).val=9 := by decide
example : (ResumeLocalIncidence.sourceFaces 0 2).val=10 := by decide
example : ResumeLocalIncidence.siteMap 8=(6 : Fin 9) := by decide
example : ResumeLocalIncidence.siteMap 8≠(8 : Fin 9) := by decide
example : SourceExactRoot.sourceRadius=SourceExactRoot.sourceRoot 6 := rfl
example : Covers (centersOfRoot SourceExactRoot.sourceRoot) SourceExactRoot.sourceRadius :=
  SourceExactRoot.source_attainment
-- Zero stress cannot delete these primal slack faces.
example : (ResumeNetwork.face 5 2).val=10 := by decide
example : Fintype.card ResumeNetwork.Edge=51 := by decide
