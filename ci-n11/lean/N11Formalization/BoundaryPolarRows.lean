import N11Formalization.SourceFrameVelocity

/-! Actual tie normal covectors on the actual independent Frame Jacobian.
The formulas keep rho/angle/R terms; these are consumed by gap-to-radius
conversion, not merely identities at the source centre values. -/
set_option autoImplicit false
namespace N11Formalization.BoundaryPolarRows
open N11Formalization PhysicalResidualFrame PinTangentGeometry
open SourceBoundaryTieDerivative SourceBoundaryWeights
open SourceFrameVelocity
noncomputable section

def polarVelocity (r θ dr dθ : ℝ) : Point :=
  !₂[dr*Real.cos θ-r*Real.sin θ*dθ,dr*Real.sin θ+r*Real.cos θ*dθ]

theorem inner_polar_normal (r θ a dr dθ : ℝ) :
    inner ℝ (circleMap (θ+a)-r • circleMap θ) (polarVelocity r θ dr dθ) =
      (Real.cos a-r)*dr+r*Real.sin a*dθ := by
  rw [inner_coords]
  unfold circleMap polarVelocity
  simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Real.cos_add,Real.sin_add]
  linear_combination (Real.cos a*dr-r*dr+r*Real.sin a*dθ)*(Real.sin_sq_add_cos_sq θ)

def sqrtRad (k : Fin 9) : ℝ :=
  Real.sqrt ((SourceExactRoot.sourceRoot 6)^2-Real.sin (angleVec SourceExactRoot.sourceRoot k)^2)

theorem cos_sub_rho (k : Fin 9) :
    Real.cos (angleVec SourceExactRoot.sourceRoot k)-rhoK SourceExactRoot.sourceRoot k=sqrtRad k := by
  unfold rhoK sqrtRad
  ring

theorem sqrtRad_pos (k : Fin 9) : 0<sqrtRad k :=
  Real.sqrt_pos.mpr (SourceWidthNondegenerate.source_radicand_pos k)

theorem left_velocity_row (k : Fin 9) (v : Frame) :
    inner ℝ (nP k) (velocity k v) =
      sqrtRad k*radialVelocity k v+SourceBoundaryWeights.slope k*directions v k := by
  unfold nP T
  rw [arcEnd_eq_circleMap,ringCenter_eq_smul]
  change inner ℝ
    (circleMap (thetaOf (angleVec SourceExactRoot.sourceRoot) k+angleVec SourceExactRoot.sourceRoot k)-
      rhoK SourceExactRoot.sourceRoot k • circleMap (thetaOf (angleVec SourceExactRoot.sourceRoot) k))
    (polarVelocity (rhoK SourceExactRoot.sourceRoot k)
      (thetaOf (angleVec SourceExactRoot.sourceRoot) k) (radialVelocity k v) (directions v k))=_
  rw [inner_polar_normal,cos_sub_rho]
  unfold SourceBoundaryWeights.slope
  ring

theorem right_velocity_row (k : Fin 9) (v : Frame) :
    inner ℝ (nQ k) (velocity (k+1) v) =
      sqrtRad (k+1)*radialVelocity (k+1) v-SourceBoundaryWeights.slope (k+1)*directions v (k+1) := by
  unfold nQ T
  rw [arcEnd_eq_circleMap_arcLo_succ,ringCenter_eq_smul]
  have ha : thetaOf (angleVec SourceExactRoot.sourceRoot) (k+1)-angleVec SourceExactRoot.sourceRoot (k+1)=
      thetaOf (angleVec SourceExactRoot.sourceRoot) (k+1)+(-angleVec SourceExactRoot.sourceRoot (k+1)) := by
    ring
  rw [ha]
  change inner ℝ
    (circleMap (thetaOf (angleVec SourceExactRoot.sourceRoot) (k+1)+(-angleVec SourceExactRoot.sourceRoot (k+1)))-
      rhoK SourceExactRoot.sourceRoot (k+1) • circleMap (thetaOf (angleVec SourceExactRoot.sourceRoot) (k+1)))
    (polarVelocity (rhoK SourceExactRoot.sourceRoot (k+1))
      (thetaOf (angleVec SourceExactRoot.sourceRoot) (k+1)) (radialVelocity (k+1) v) (directions v (k+1)))=_
  rw [inner_polar_normal,Real.cos_neg,Real.sin_neg,cos_sub_rho]
  unfold SourceBoundaryWeights.slope
  ring

/-- Exact coupled-R cancellation; omitting B*dR gives a false identity. -/
theorem coupled_radial_row (k : Fin 9) (v : Frame) :
    sqrtRad k*radialVelocity k v=SourceBoundaryWeights.slope k*widths v k-SourceExactRoot.sourceRoot 6*v 11 := by
  have hn : sqrtRad k≠0 := ne_of_gt (sqrtRad_pos k)
  have hA : sqrtRad k*SourceFrameVelocity.slopeA k=SourceBoundaryWeights.slope k := by
    unfold SourceFrameVelocity.slopeA WidthRadialDerivative.widthSlope
    change sqrtRad k*(Real.sin (angleVec SourceExactRoot.sourceRoot k)*
      rhoK SourceExactRoot.sourceRoot k/sqrtRad k)=_
    field_simp [hn]
    unfold SourceBoundaryWeights.slope
    ring
  have hB : sqrtRad k*SourceFrameVelocity.slopeB k=-SourceExactRoot.sourceRoot 6 := by
    unfold SourceFrameVelocity.slopeB CoupledRadialFrame.radiusSlope
    change sqrtRad k*(-SourceExactRoot.sourceRoot 6/sqrtRad k)=_
    field_simp [hn]
  rw [radialVelocity,mul_add]
  rw [← mul_assoc,hA,← mul_assoc,hB]
  ring

end
end N11Formalization.BoundaryPolarRows
#check @N11Formalization.BoundaryPolarRows.left_velocity_row
#check @N11Formalization.BoundaryPolarRows.right_velocity_row
#check @N11Formalization.BoundaryPolarRows.coupled_radial_row
#print axioms N11Formalization.BoundaryPolarRows.coupled_radial_row
