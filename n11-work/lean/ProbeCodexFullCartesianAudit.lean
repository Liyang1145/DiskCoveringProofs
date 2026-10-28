import N11Formalization
set_option autoImplicit false
open N11Formalization

#print CartesianReflectionSpace.Full
#print CartesianReflectionSpace.reflect
#print CartesianReflectionSpace.embed
#print FullCartesianResidual.residualFull
#print FullCartesianDual.averagedObjective
#print FullCartesianDual.invariantBoundary
#check @CartesianReflectionSpace.fixed_iff_embed
#check @CartesianReflectionSpace.embed_frame_source
#check @HorizontalTruePin.horizontal_pin
#check @HorizontalTruePin.source_central_smooth
#check @FullCartesianResidual.residualFull_frame
#check @FullCartesianResidual.objectiveFull_source_smooth
#check @FullCartesianDual.averagedDerivative_hasFDerivAt
#check @FullCartesianDual.averagedDerivative_invariant
#check @FullCartesianDual.actual_full_cartesian_dual
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound

#print axioms CartesianReflectionSpace.fixed_iff_embed
#print axioms CartesianReflectionSpace.embed_frame_source
#print axioms HorizontalTruePin.source_central_smooth
#print axioms FullCartesianResidual.residualFull_frame
#print axioms FullCartesianDual.averagedDerivative_hasFDerivAt
#print axioms FullCartesianDual.actual_full_cartesian_dual
#print axioms SourceExactRoot.source_attainment

example (v : CartesianReflectionSpace.Full) :
    fderiv ℝ FullCartesianDual.averagedObjective FullCartesianResidual.sourcePoint v =
      ∑ j : Fin 5, BoundaryChartDual.multiplier
        (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
          CoupledRadialFrame.sourcePoint (Pi.single i 1)) j *
        FullCartesianDual.invariantBoundary v j :=
  FullCartesianDual.actual_full_cartesian_dual v

-- The hub's vertical direction is excluded by the fixed-space coordinates,
-- but it is present in Full. Only the AVERAGED covector is known to kill it.
example :
    CartesianReflectionSpace.reflect (Pi.single 19 1) =
      -(Pi.single 19 1 : CartesianReflectionSpace.Full) := by
  funext i
  fin_cases i <;>
    norm_num [CartesianReflectionSpace.reflect, Pi.single_apply, Fin.ext_iff]

example (x : CartesianReflectionSpace.Full)
    (hx : CartesianReflectionSpace.reflect x = -x) :
    FullCartesianDual.averagedDerivative x = 0 := by
  have h := FullCartesianDual.averagedDerivative_invariant x
  rw [hx, map_neg] at h
  linarith
