import N11Formalization.SourcePositiveHarmonicConsumer

/-! Actual all9 source tie-normal combinations are strictly outward radial.
This is the arcEnd boundary branch, not the interior Uvec branch. Positivity
follows analytically from rho<1, eta in(0,1) and the paid actual tie weights.
Canonical flux transport is a separate consumer. -/
set_option autoImplicit false
namespace N11Formalization.SourceRadialFluxGeometry
open N11Formalization PinTangentGeometry SourceBoundaryTieDerivative
noncomputable section

theorem norm_circle (t : ℝ) : ‖circleMap t‖=1 := by
  rw [circleMap,FanFoutPos.norm_two,Real.cos_sq_add_sin_sq,Real.sqrt_one]

theorem source_ring_norm (k : Fin 9) :
    ‖ringCenter SourceExactRoot.sourceRoot k‖=rhoK SourceExactRoot.sourceRoot k := by
  rw [ringCenter_eq_smul,norm_smul,norm_circle,mul_one,Real.norm_eq_abs,
    abs_of_pos (CartesianPolarFrame.source_rho_pos k)]

theorem source_ring_norm_lt_one (k : Fin 9) :
    ‖ringCenter SourceExactRoot.sourceRoot k‖<1 := by
  rw [source_ring_norm]
  have hcos := Real.cos_le_one (angleVec SourceExactRoot.sourceRoot k)
  have hsqrt := Real.sqrt_pos.mpr (SourceWidthNondegenerate.source_radicand_pos k)
  unfold rhoK
  linarith

theorem source_tangent_rank_all (k : Fin 9) :
    det (T k) (SourceBoundaryTieDerivative.D k)≠0 := by
  rw [SourceBoundaryWeights.source_denominator]
  exact ne_of_gt (add_pos (SourceBoundaryWeights.slope_pos k)
    (SourceBoundaryWeights.slope_pos (k+1)))

theorem normalCombination_radial (k : Fin 9) :
    normalCombination k=radialCoefficient k • T k := by
  have hz : det (T k) (normalCombination k)=0 := by
    have he : det (T k) (normalCombination k)=
        eta k*det (T k) (nP k)+(1-eta k)*det (T k) (nQ k) := by
      unfold normalCombination det
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      ring
    rw [he,SourceBoundaryWeights.left_tangent_row,SourceBoundaryWeights.right_tangent_row,
      SourceBoundaryWeights.eta_eq]
    have hd := ne_of_gt (add_pos (SourceBoundaryWeights.slope_pos k)
      (SourceBoundaryWeights.slope_pos (k+1)))
    field_simp [hd]
    ring
  have he := SourceFanLengthCovector.normal_expansion (T k) (SourceBoundaryTieDerivative.D k)
    (normalCombination k) (source_tangent_rank_all k)
  have hB : SourceFanLengthCovector.coefficientB (T k) (SourceBoundaryTieDerivative.D k)
      (normalCombination k)=0 := by
    rw [SourceFanLengthCovector.coefficientB,hz,zero_div]
  rw [hB,zero_smul,add_zero] at he
  have hA : radialCoefficient k=
      SourceFanLengthCovector.coefficientA (T k) (SourceBoundaryTieDerivative.D k)
        (normalCombination k) := by
    have hi := congrArg (fun n : Point => inner ℝ (T k) n) he
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,
      show ‖T k‖=1 from FanFoutPos.norm_arcEnd _ k] at hi
    simpa only [radialCoefficient,one_pow,mul_one] using hi
  rw [hA]
  exact he

theorem normalP_outward (k : Fin 9) : 0 < inner ℝ (T k) (nP k) := by
  have h := real_inner_le_norm (T k) (ringCenter SourceExactRoot.sourceRoot k)
  have hn : ‖T k‖=1 := FanFoutPos.norm_arcEnd _ k
  rw [hn,one_mul] at h
  have hc := source_ring_norm_lt_one k
  rw [nP,inner_sub_right,real_inner_self_eq_norm_sq,hn,one_pow]
  linarith

theorem normalQ_outward (k : Fin 9) : 0 < inner ℝ (T k) (nQ k) := by
  have h := real_inner_le_norm (T k) (ringCenter SourceExactRoot.sourceRoot (k+1))
  have hn : ‖T k‖=1 := FanFoutPos.norm_arcEnd _ k
  rw [hn,one_mul] at h
  have hc := source_ring_norm_lt_one (k+1)
  rw [nQ,inner_sub_right,real_inner_self_eq_norm_sq,hn,one_pow]
  linarith

theorem radialCoefficient_pos (k : Fin 9) : 0<radialCoefficient k := by
  rw [radialCoefficient,normalCombination,inner_add_right,
    real_inner_smul_right,real_inner_smul_right]
  exact add_pos
    (mul_pos (SourceBoundaryWeights.eta_bounds k).1 (normalP_outward k))
    (mul_pos (sub_pos.mpr (SourceBoundaryWeights.eta_bounds k).2) (normalQ_outward k))

def rawLoad (k : Fin 9) : ℝ :=
  SourceSignedStressAssembly.tieWeight k*radialCoefficient k

theorem rawLoad_pos (k : Fin 9) : 0<rawLoad k := by
  have hw : 0<SourceSignedStressAssembly.tieWeight k :=
    div_pos (SourceBoundaryStressPositive.tieWeight_pos (SourceSignedStressAssembly.tieRep k))
      (SourceSignedStressAssembly.tieOrbitSize_pos (SourceSignedStressAssembly.tieRep k))
  exact mul_pos hw (radialCoefficient_pos k)

/-- The actual two source spoke contributions at each of ALL9 boundary ties
have strictly outward radial resultant; no sign/radiality premise remains. -/
theorem raw_spoke_resultant (k : Fin 9) :
    (∑ s : Fin 2,SourceSignedStressAssembly.stress (.inl (k,s)) •
      (arcEnd SourceExactRoot.sourceRoot k-
        centersOfRoot SourceExactRoot.sourceRoot (SourceTieForceTransport.spokeSite k s)))=
      rawLoad k • arcEnd SourceExactRoot.sourceRoot k := by
  rw [Fin.sum_univ_two]
  have h0 : centersOfRoot SourceExactRoot.sourceRoot (SourceTieForceTransport.spokeSite k 0)=
      ringCenter SourceExactRoot.sourceRoot k := centersOfRoot_ring _ k
  have h1 : centersOfRoot SourceExactRoot.sourceRoot (SourceTieForceTransport.spokeSite k 1)=
      ringCenter SourceExactRoot.sourceRoot (k+1) := by
    have hs : (1 : Fin 2)≠0 := by decide
    simpa only [SourceTieForceTransport.spokeSite,hs,if_false] using
      centersOfRoot_ring SourceExactRoot.sourceRoot (k+1)
  rw [h0,h1]
  change (SourceSignedStressAssembly.tieWeight k*eta k) • nP k+
    (SourceSignedStressAssembly.tieWeight k*(1-eta k)) • nQ k=_
  rw [mul_smul,mul_smul,← smul_add,← normalCombination,normalCombination_radial]
  exact (mul_smul _ _ _).symm

end
end N11Formalization.SourceRadialFluxGeometry
#check @N11Formalization.SourceRadialFluxGeometry.normalCombination_radial
#check @N11Formalization.SourceRadialFluxGeometry.raw_spoke_resultant
#check @N11Formalization.SourceRadialFluxGeometry.rawLoad_pos
#print axioms N11Formalization.SourceRadialFluxGeometry.raw_spoke_resultant
#print axioms N11Formalization.SourceRadialFluxGeometry.rawLoad_pos
