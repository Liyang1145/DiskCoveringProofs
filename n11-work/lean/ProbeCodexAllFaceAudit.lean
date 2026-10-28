import N11Formalization
set_option autoImplicit false
open N11Formalization

#print SourceFaceReflection.siteMirror
#print SourceFaceReflection.faceMirror
#print SourceAllFaceBalance.repIndex
#print SourceAllFaceBalance.vertexPerm
#print SourceAllFaceBalance.orbitSize
#print SourceAllFaceBalance.faceOnlyStress
#check @SourceFaceReflection.actual_site_reflection
#check @SourceFaceReflection.face_vertex_mirror
#check @SourceAllFaceBalance.source_face_indices
#check @SourceAllFaceBalance.actual_aux
#check @SourceAllFaceBalance.beta_pos
#check @SourceAllFaceBalance.coefficient_pos
#check @SourceAllFaceBalance.coefficient_mass
#check @SourceAllFaceBalance.actual_auxiliary_balance
#check @SourceAllFaceBalance.full_auxiliary_B2_rows
#print axioms SourceFaceReflection.actual_site_reflection
#print axioms SourceAllFaceBalance.actual_aux
#print axioms SourceAllFaceBalance.coefficient_pos
#print axioms SourceAllFaceBalance.coefficient_mass
#print axioms SourceAllFaceBalance.full_auxiliary_B2_rows

example (f : Fin 9) (c : Fin 2) :
    ∑ s : ResumeLocalIncidence.SourceEdge,
      SourceN2.srcB2 SourceExactRoot.sourceRoot
        (⟨22+2*f.val+c.val,by omega⟩ : Fin 41)
        (HarmonicSourceTransport.srcFlat s)*SourceAllFaceBalance.faceOnlyStress s=0 :=
  SourceAllFaceBalance.full_auxiliary_B2_rows f c

example : ∀ f : Fin 9, ∀ t : Fin 3, 0<SourceAllFaceBalance.coefficient f t :=
  SourceAllFaceBalance.coefficient_pos

-- The central orbit has size2; the self-reflected fan8 orbit has size1.
example : SourceAllFaceBalance.orbitSize (SourceAllFaceBalance.repIndex 0)=2 := rfl
example : SourceAllFaceBalance.orbitSize (SourceAllFaceBalance.repIndex 8)=1 := rfl
example : SourceAllFaceBalance.vertexPerm 5 0=1 := rfl
example : SourceAllFaceBalance.vertexPerm 5 1=0 := rfl
example : SourceFaceReflection.siteMirror 9=9 ∧ SourceFaceReflection.siteMirror 10=10 := by
  constructor <;> rfl

-- Scope calibration: faceOnlyStress has ZERO spoke coefficients and is not final alpha.
example (k : Fin 9) (t : Fin 2) :
    SourceAllFaceBalance.faceOnlyStress (.inl (k,t))=0 := rfl

#check @PhysicalBoundaryStationarity.stationary_source_fderiv
#check @PhysicalBoundaryStationarity.signed_mass_one
#check @SourceExactRoot.main_of_lower_bound
#check @SourceExactRoot.source_attainment
