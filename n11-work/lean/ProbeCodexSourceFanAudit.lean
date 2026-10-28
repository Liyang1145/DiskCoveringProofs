import N11Formalization
set_option autoImplicit false
open N11Formalization

#print SourceFanLengthCovector.sourceA
#print SourceFanLengthCovector.sourceB
#print SourceFanConversion.sourceConversion
#check @SourceFanLengthCovector.source_normalH_expansion
#check @SourceFanLengthCovector.norm_fderiv_apply
#check @SourceFanLengthCovector.fanLength_source_fderiv
#check @SourceFanConversion.sourceConversion_eq
#check @SourceFanConversion.sourceConversion_pos
#check @SourceFanConversion.sourceConversion_eq_four_y_sq_over_Fout
#check @SourceFanConversion.beta_sum_one
#check @SourceFanConversion.beta_center_identity
#check @SourceFanConversion.betaH_pos
#check @SourceFanConversion.normalized_fan_length

#print axioms SourceFanLengthCovector.norm_fderiv_apply
#print axioms SourceFanLengthCovector.fanLength_source_fderiv
#print axioms SourceFanConversion.sourceConversion_pos
#print axioms SourceFanConversion.sourceConversion_eq_four_y_sq_over_Fout
#print axioms SourceFanConversion.beta_center_identity
#print axioms SourceFanConversion.normalized_fan_length

-- Actual full-coordinate residual component0 consumes the normalized LENGTH formula.
example (v : CartesianReflectionSpace.Full) :
    fderiv ℝ (fun x : CartesianReflectionSpace.Full => FullCartesianResidual.residualFull x 0)
      FullCartesianResidual.sourcePoint v =
      SourceFanConversion.sourceConversion 1 *
        (-(SourceFanConversion.betaP 1 * inner ℝ (SourceFanLengthCovector.normalP 1)
            (TrueCirclePinSmooth.left (FullCartesianResidual.ringData 1 v)) +
           SourceFanConversion.betaQ 1 * inner ℝ (SourceFanLengthCovector.normalQ 1)
            (TrueCirclePinSmooth.right (FullCartesianResidual.ringData 1 v)) +
           SourceFanConversion.betaH 1 * inner ℝ (SourceFanLengthCovector.normalH 1)
            (SourceFanLengthCovector.fullHub 1 v)) / SourceExactRoot.sourceRoot 6 - v 22) :=
  SourceFanConversion.normalized_fan_length 1 (by simp) v

-- Deliberate scope check: no theorem claiming betaP/betaQ positivity or
-- a circumradius fderiv is imported as if paid; source normalization is algebraic.
#check @SourceExactRoot.main_of_lower_bound
