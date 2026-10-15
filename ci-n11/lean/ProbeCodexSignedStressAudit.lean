import N11Formalization
set_option autoImplicit false
open N11Formalization
#print SourceSignedStressAssembly.stress
#print SourceSignedStressAssembly.tieRep
#print SourceSignedStressAssembly.tieOrbitSize
#check @SourceAllFaceBalance.actual_aux
#check @SourceAllFaceBalance.coefficient_mass
#check @SourceSignedStressAssembly.stress_mass_one
#check @SourceSignedStressAssembly.stress_positive_iff
#check @SourceSignedStressAssembly.full_auxiliary_B2_rows
#print axioms SourceSignedStressAssembly.stress_mass_one
#print axioms SourceSignedStressAssembly.stress_positive_iff
#print axioms SourceSignedStressAssembly.full_auxiliary_B2_rows
example : ∑ s : ResumeLocalIncidence.SourceEdge, SourceSignedStressAssembly.stress s=1 :=
  SourceSignedStressAssembly.stress_mass_one
example (f : Fin 9) (c : Fin 2) :
    ∑ s : ResumeLocalIncidence.SourceEdge, SourceN2.srcB2 SourceExactRoot.sourceRoot
      (⟨22+2*f.val+c.val,by omega⟩ : Fin 41) (HarmonicSourceTransport.srcFlat s)*
      SourceSignedStressAssembly.stress s=0 :=
  SourceSignedStressAssembly.full_auxiliary_B2_rows f c
-- The exact boundary positivity obligation remains in the FULL type, not hidden.
example :
    (∀ s : ResumeLocalIncidence.SourceEdge, 0<SourceSignedStressAssembly.stress s) ↔
      (∀ j : Fin 5, 0<PhysicalBoundaryStationarity.tieWeight j) :=
  SourceSignedStressAssembly.stress_positive_iff
#check @SourceExactRoot.main_of_lower_bound
#check @SourceExactRoot.source_attainment
