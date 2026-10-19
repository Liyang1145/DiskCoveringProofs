import N11Formalization
set_option autoImplicit false
open N11Formalization
open SourceRefinedFanCoefficientBounds SourceRefinedBoundaryIntervals

#print SourceExactRoot.sourceRadius
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
#check @SourceRefinedFanCoefficientBounds.refined_membership
#check @SourceRefinedBoundaryIntervals.numeratorBox_mem
#print axioms SourceRefinedFanCoefficientBounds.refined_membership
#print axioms SourceRefinedBoundaryIntervals.numeratorBox_mem

example (i : Fin 4) :
    (ABox i).Mem (SourceFanLengthCovector.sourceA (SourceBoundarySignBounds.contact i)) ∧
    (BBox i).Mem (SourceFanLengthCovector.sourceB (SourceBoundarySignBounds.contact i)) :=
  refined_membership i

example (j : Fin 5) : (numeratorBox j).Mem
    (SourceBoundaryMultiplierFormula.numerator j) :=
  SourceRefinedBoundaryIntervals.numeratorBox_mem j
