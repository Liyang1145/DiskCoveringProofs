import N11Formalization
set_option autoImplicit false
open N11Formalization

#print SourceFanCircumradius.center
#print SourceFanCircumradius.fanRadius
#print SourceFanRadiusDerivative.radiusExcess
#check @CircumcenterGeometry.circumcenter_eq_of_equidistant
#check @CircumcenterGeometry.circumcenter_equidistant
#check @CircumcenterGeometry.circumcenter_smooth
#check @SourceFanCircumradius.source_triangle_det
#check @SourceFanCircumradius.center_source
#check @SourceFanCircumradius.fanRadius_source
#check @SourceFanCircumradius.fanRadius_source_smooth
#check @SourceFanCircumradius.source_circle_equations_eventually
#check @SourceFanRadiusDerivative.fanRadius_source_fderiv
#check @SourceFanRadiusDerivative.length_to_circumradius
#check @SourceFanConversion.sourceConversion_pos

#print axioms CircumcenterGeometry.circumcenter_eq_of_equidistant
#print axioms SourceFanCircumradius.source_triangle_det
#print axioms SourceFanCircumradius.source_circle_equations_eventually
#print axioms SourceFanRadiusDerivative.fanRadius_source_fderiv
#print axioms SourceFanRadiusDerivative.length_to_circumradius

-- Actual complete LENGTH residual4? The four fan rows only; central remains separate.
example (v : CartesianReflectionSpace.Full) :
    fderiv ℝ (fun x : CartesianReflectionSpace.Full => FullCartesianResidual.residualFull x 3)
      FullCartesianResidual.sourcePoint v =
      SourceFanConversion.sourceConversion 8 *
        fderiv ℝ (SourceFanRadiusDerivative.radiusExcess 8) FullCartesianResidual.sourcePoint v :=
  SourceFanRadiusDerivative.length_to_circumradius 8 (by simp) v

-- Independent radius direction must stay -1 for circumradius excess:
-- the radius function depends on centers, not on coordinate22.
example : SourceFanRadiusDerivative.radiusExcess 1 FullCartesianResidual.sourcePoint = 0 := by
  rw [SourceFanRadiusDerivative.radiusExcess, SourceFanCircumradius.fanRadius_source 1 (by simp)]
  change SourceExactRoot.sourceRoot 6-SourceExactRoot.sourceRoot 6=0
  exact sub_self _

#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
