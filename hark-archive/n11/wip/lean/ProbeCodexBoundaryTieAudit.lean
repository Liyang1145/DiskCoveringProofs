import N11Formalization
set_option autoImplicit false
open N11Formalization

#print TrueBoundaryTie.tie
#print TrueBoundaryTie.foot
#print SourceBoundaryTie.sourceSeed
#print SourceBoundaryTie.radiusFull
#print SourceBoundaryTieDerivative.eta
#print SourceBoundaryWeights.radiusScale
#check @TrueBoundaryTie.seed_ne_of_inside
#check @SourceBoundaryTie.source_centers_inside
#check @SourceBoundaryTie.source_chord_ne
#check @SourceBoundaryTie.tieFull_source
#check @SourceBoundaryTie.radiusFull_source
#check @SourceBoundaryTie.tie_equations_eventually
#check @SourceBoundaryTie.radiusFull_source_smooth
#check @SourceBoundaryTieDerivative.source_tangent_rank
#check @SourceBoundaryTieDerivative.radiusFull_source_fderiv
#check @SourceBoundaryWeights.eta_bounds
#check @SourceBoundaryWeights.radiusScale_pos
#check @SourceBoundaryWeights.inverse_width_radius_slope
#print axioms TrueBoundaryTie.tie_source
#print axioms SourceBoundaryTie.tie_equations_eventually
#print axioms SourceBoundaryTie.radiusFull_source_smooth
#print axioms SourceBoundaryTieDerivative.radiusFull_source_fderiv
#print axioms SourceBoundaryWeights.eta_bounds
#print axioms SourceBoundaryWeights.inverse_width_radius_slope

example (v : CartesianReflectionSpace.Full) :
    fderiv ℝ (SourceBoundaryTie.radiusFull 8) FullCartesianResidual.sourcePoint v =
      -(SourceBoundaryTieDerivative.eta 8 *
          inner ℝ (SourceBoundaryTieDerivative.nP 8) (FullCartesianResidual.ring v 8)+
        (1-SourceBoundaryTieDerivative.eta 8) *
          inner ℝ (SourceBoundaryTieDerivative.nQ 8) (FullCartesianResidual.ring v (8+1))) /
        SourceExactRoot.sourceRoot 6 :=
  SourceBoundaryTieDerivative.radiusFull_source_fderiv 8 (by simp) v

example : ∀ k : Fin 9, 0<SourceBoundaryTieDerivative.eta k ∧
    SourceBoundaryTieDerivative.eta k<1 := SourceBoundaryWeights.eta_bounds

-- Real branch must bind to original source arcEnd, not merely to any equidistant point.
example : SourceBoundaryTie.tieFull 0 FullCartesianResidual.sourcePoint =
    arcEnd SourceExactRoot.sourceRoot 0 := SourceBoundaryTie.tieFull_source 0 (by simp)

example : ‖SourceBoundaryTie.tieFull 8 FullCartesianResidual.sourcePoint‖=1 := by
  rw [SourceBoundaryTie.tieFull_source 8 (by simp)]
  exact FanFoutPos.norm_arcEnd _ _

#check @FullCartesianDual.actual_full_cartesian_dual
#check @SourceExactRoot.main_of_lower_bound
#check @SourceExactRoot.source_attainment
