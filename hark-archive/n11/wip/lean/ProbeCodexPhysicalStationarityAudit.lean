import N11Formalization
set_option autoImplicit false
open N11Formalization

#print PhysicalBoundaryStationarity.stationaryObjective
#print PhysicalBoundaryStationarity.tieWeight
#print BoundaryGapConversion.averagedTieExcess
#check @SourceFrameVelocity.center_source_fderiv
#check @SourceFrameVelocity.ring_frameJac
#check @BoundaryPolarRows.coupled_radial_row
#check @BoundaryGapConversion.gap_frameJac
#check @BoundaryGapConversion.full_gap_to_tie
#check @PhysicalBoundaryStationarity.physical_covector_formula
#check @PhysicalBoundaryStationarity.stationary_source_fderiv
#check @PhysicalBoundaryStationarity.tie_radius_direction
#check @PhysicalBoundaryStationarity.signed_mass_one
#print axioms SourceFrameVelocity.ring_frameJac
#print axioms BoundaryGapConversion.full_gap_to_tie
#print axioms PhysicalBoundaryStationarity.stationary_source_fderiv
#print axioms PhysicalBoundaryStationarity.signed_mass_one

example (v : CartesianReflectionSpace.Full) :
    FullCartesianDual.invariantBoundary v 4 =
      SourceBoundaryWeights.radiusScale 8 *
        fderiv ℝ (BoundaryGapConversion.averagedTieExcess 8)
          FullCartesianResidual.sourcePoint v :=
  BoundaryGapConversion.full_gap_to_tie 4 v

example :
    fderiv ℝ PhysicalBoundaryStationarity.stationaryObjective
      FullCartesianResidual.sourcePoint = 0 :=
  PhysicalBoundaryStationarity.stationary_source_fderiv

example :
    (∑ j : Fin 5, PhysicalInteriorObjective.weight j)+
      (∑ j : Fin 5, PhysicalBoundaryStationarity.tieWeight j)=1 :=
  PhysicalBoundaryStationarity.signed_mass_one

-- The boundary sign convention is explicit and remains unproved.
example (j : Fin 5) :
    PhysicalBoundaryStationarity.tieWeight j =
      -PhysicalBoundaryStationarity.boundaryMultiplier j *
        SourceBoundaryWeights.radiusScale (BoundaryGapConversion.representative j) := rfl

-- Calibrate the independent radius column at the wrap representative.
example :
    BoundaryGapConversion.averagedTieDerivative 8 (Pi.single 22 1 : CartesianReflectionSpace.Full) = -1 :=
  PhysicalBoundaryStationarity.tie_radius_direction 4

#check @SourceExactRoot.main_of_lower_bound
#check @SourceExactRoot.source_attainment
