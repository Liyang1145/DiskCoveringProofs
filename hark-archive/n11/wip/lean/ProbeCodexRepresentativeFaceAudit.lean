import N11Formalization
set_option autoImplicit false
open N11Formalization

#print SourceRepresentativeFaceBalance.faceIndex
#print SourceRepresentativeFaceBalance.beta
#print SourceRepresentativeFaceBalance.edgeCoefficient
#check @SourceFanBarycentricSigns.product_bounds
#check @SourceFanBarycentricSigns.source_betas_pos
#check @SourceFanBarycentricSigns.central_betas_pos
#check @SourceRepresentativeFaceBalance.source_vertex
#check @SourceRepresentativeFaceBalance.source_aux
#check @SourceRepresentativeFaceBalance.beta_sum
#check @SourceRepresentativeFaceBalance.edgeCoefficient_pos
#check @SourceRepresentativeFaceBalance.actual_auxiliary_balance
#check @SourceRepresentativeFaceBalance.actual_auxiliary_B2_rows
#print axioms SourceFanBarycentricSigns.source_betas_pos
#print axioms SourceFanBarycentricSigns.central_betas_pos
#print axioms SourceRepresentativeFaceBalance.source_aux
#print axioms SourceRepresentativeFaceBalance.edgeCoefficient_pos
#print axioms SourceRepresentativeFaceBalance.actual_auxiliary_B2_rows

-- Actual central face1 has source site order(ring6,hub0,hub1), not(hub0,hub1,ring6).
example :
    SourceRepresentativeFaceBalance.beta 4 0=SourceCentralGeometry.betaH := rfl
example :
    (ResumeLocalIncidence.sourceFaces (SourceRepresentativeFaceBalance.faceIndex 4) 1).val=9 := rfl
example :
    (ResumeLocalIncidence.sourceFaces (SourceRepresentativeFaceBalance.faceIndex 4) 2).val=10 := rfl

example (j : Fin 5) (c : Fin 2) :
    ∑ t : Fin 3,
      SourceN2.srcB2 SourceExactRoot.sourceRoot
        (⟨22+2*(SourceRepresentativeFaceBalance.faceIndex j).val+c.val,by omega⟩ : Fin 41)
        (SourceN2.faceFlatEdge (SourceRepresentativeFaceBalance.faceIndex j) t) *
        SourceRepresentativeFaceBalance.edgeCoefficient j t=0 :=
  SourceRepresentativeFaceBalance.actual_auxiliary_B2_rows j c

example : ∀ j : Fin 5, ∀ t : Fin 3,
    0<SourceRepresentativeFaceBalance.edgeCoefficient j t :=
  SourceRepresentativeFaceBalance.edgeCoefficient_pos

#check @PhysicalBoundaryStationarity.signed_mass_one
#check @PhysicalBoundaryStationarity.stationary_source_fderiv
#check @SourceExactRoot.main_of_lower_bound
#check @SourceExactRoot.source_attainment
