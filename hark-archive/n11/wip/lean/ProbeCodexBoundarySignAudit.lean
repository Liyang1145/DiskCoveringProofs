import N11Formalization
set_option autoImplicit false
open N11Formalization

#print SourceBoundarySignBounds.compactA
#print SourceBoundarySignBounds.compactB
#check @SourceBoundarySignBounds.denominator_pos
#check @SourceBoundarySignBounds.compact_contains
#check @SourceBoundarySignBounds.compact_membership
#check @SourceBoundarySignReadout.source_ring4_margin
#check @SourceBoundarySignReadout.widthFour_objective_derivative
#check @SourceBoundarySignReadout.boundaryMultiplier_three_neg
#check @SourceBoundarySignReadout.tieWeight_three_pos
#check @SourceBoundarySignReadout.spokes_three_four_pos
#check @SourceBoundarySignReadout.remaining_stress_signs_iff
#print axioms SourceBoundarySignBounds.compact_membership
#print axioms SourceBoundarySignReadout.boundaryMultiplier_three_neg
#print axioms SourceBoundarySignReadout.tieWeight_three_pos
#print axioms SourceBoundarySignReadout.spokes_three_four_pos

example :
    0<SourceSignedStressAssembly.stress (.inl (3,0)) :=
  SourceBoundarySignReadout.spokes_three_four_pos 3 (by simp) 0
example :
    0<SourceSignedStressAssembly.stress (.inl (4,1)) :=
  SourceBoundarySignReadout.spokes_three_four_pos 4 (by simp) 1

-- Actual canonical reindex consumer for a now-proved positive source spoke.
example :
    0<SourceCentreB2Readout.canonicalStress (ResumeLocalIncidence.edgeMap (.inl (3,0))) := by
  rw [SourceCentreB2Readout.canonicalStress,SourceAlphaOf.alphaEdge_edgeMap]
  exact SourceBoundarySignReadout.spokes_three_four_pos 3 (by simp) 0

-- Remaining four inequalities are STILL explicit; not silently paid.
example :
    (∀ e : ResumeLocalIncidence.SourceEdge,0<SourceSignedStressAssembly.stress e) ↔
      (∀ j : Fin 5,j≠3 → 0<PhysicalBoundaryStationarity.tieWeight j) :=
  SourceBoundarySignReadout.remaining_stress_signs_iff

#check @SourceCentreB2Readout.all_B2_rows
#check @SourceCentreB2Readout.canonical_mass_one
#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
