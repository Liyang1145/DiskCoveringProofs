import N11Formalization
set_option autoImplicit false
open N11Formalization

#print SourceCentralGeometry.center
#print SourceCentralGeometry.conversion
#print PhysicalInteriorObjective.physicalObjective
#print PhysicalInteriorObjective.weight
#check @SourceCentralGeometry.source_distances
#check @SourceCentralGeometry.source_normals_independent
#check @SourceCentralGeometry.source_ring_above
#check @SourceCentralGeometry.conversion_pos
#check @SourceCentralGeometry.centralRadius_source_smooth
#check @SourceCentralDerivative.pin_circle_equations_eventually
#check @SourceCentralDerivative.centralRadius_fderiv
#check @SourceCentralDerivative.length_to_circumradius
#check @PhysicalInteriorObjective.length_row_conversion
#check @PhysicalInteriorObjective.weight_pos
#check @PhysicalInteriorObjective.physicalDerivative_eq_length
#check @PhysicalInteriorObjective.radiusRow_radius_direction
#check @PhysicalInteriorObjective.physical_radius_mass
#check @PhysicalInteriorObjective.actual_physical_interior_dual

#print axioms SourceCentralGeometry.conversion_pos
#print axioms SourceCentralDerivative.length_to_circumradius
#print axioms PhysicalInteriorObjective.weight_pos
#print axioms PhysicalInteriorObjective.length_row_conversion
#print axioms PhysicalInteriorObjective.radiusRow_radius_direction
#print axioms PhysicalInteriorObjective.actual_physical_interior_dual

-- Actual central residual row4 consumes its independently proved conversion.
example (v : CartesianReflectionSpace.Full) :
    fderiv ℝ (fun x : CartesianReflectionSpace.Full => FullCartesianResidual.residualFull x 4)
      FullCartesianResidual.sourcePoint v =
      SourceCentralGeometry.conversion *
        fderiv ℝ SourceCentralDerivative.radiusExcess FullCartesianResidual.sourcePoint v :=
  SourceCentralDerivative.length_to_circumradius v

-- All five physical excess functions have the actual -dR normalization.
example : ∀ j : Fin 5,
    fderiv ℝ (PhysicalInteriorObjective.radiusRow j) FullCartesianResidual.sourcePoint
      (Pi.single 22 1 : CartesianReflectionSpace.Full) = -1 :=
  PhysicalInteriorObjective.radiusRow_radius_direction

example (v : CartesianReflectionSpace.Full) :
    fderiv ℝ PhysicalInteriorObjective.averagedPhysicalObjective FullCartesianResidual.sourcePoint v =
      ∑ j : Fin 5, BoundaryChartDual.multiplier
        (fun i => fderiv ℝ TrueResidualFrame.objectiveTrue
          CoupledRadialFrame.sourcePoint (Pi.single i 1)) j *
        FullCartesianDual.invariantBoundary v j :=
  PhysicalInteriorObjective.actual_physical_interior_dual v

-- No claim that weights sum to1 before physical boundary/tie weights are paid.
#check @SourceExactRoot.main_of_lower_bound
#check @SourceExactRoot.source_attainment
