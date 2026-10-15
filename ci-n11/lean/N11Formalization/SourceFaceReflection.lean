import N11Formalization.SourceRepresentativeFaceBalance

/-! Source9 reflection transport uses the actual Fin11 site/face table and
the already-proved full Cartesian source symmetry. Point reflection is linear
and isometric. The Cramer circumcentre formula is transported only after
noncollinearity/equidistance are proved, not inferred from numeric agreement. -/
set_option autoImplicit false
namespace N11Formalization.SourceFaceReflection
open N11Formalization CartesianReflectionSpace ResumeLocalIncidence
open PinTangentGeometry CircumcenterGeometry
noncomputable section

def flip (p : Point) : Point := !₂[p 0,-p 1]
def flipLinear : Point →ₗ[ℝ] Point where
  toFun := flip
  map_add' := by
    intro p q
    ext i
    fin_cases i <;> simp [flip] <;> ring
  map_smul' := by
    intro r p
    ext i
    fin_cases i <;> simp [flip,smul_eq_mul]

@[simp] theorem flipLinear_apply (p : Point) : flipLinear p=flip p := rfl
@[simp] theorem flip_flip (p : Point) : flip (flip p)=p := by
  ext i
  fin_cases i <;> simp [flip]

theorem norm_flip (p : Point) : ‖flip p‖=‖p‖ := by
  have h : ‖flip p‖^2=‖p‖^2 := by
    rw [norm_sq_coords,norm_sq_coords]
    simp [flip]
  nlinarith [norm_nonneg (flip p),norm_nonneg p]

theorem flip_sub (p q : Point) : flip (p-q)=flip p-flip q := flipLinear.map_sub p q
theorem norm_flip_sub (p q : Point) : ‖flip p-flip q‖=‖p-q‖ := by
  rw [← flip_sub,norm_flip]
theorem triangleDet_flip (A B C : Point) :
    triangleDet (flip A) (flip B) (flip C)=-triangleDet A B C := by
  unfold triangleDet det
  simp only [PiLp.sub_apply,flip,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring
theorem triangleDet_swap (A B C : Point) : triangleDet B A C=-triangleDet A B C := by
  unfold triangleDet det
  simp only [PiLp.sub_apply]
  ring
theorem triangleDet_cyclic (A B C : Point) : triangleDet C A B=triangleDet A B C := by
  unfold triangleDet det
  simp only [PiLp.sub_apply]
  ring

theorem circumcenter_flip (A B C : Point) (hdet : triangleDet A B C≠0) :
    circumcenter (flip A) (flip B) (flip C)=flip (circumcenter A B C) := by
  obtain ⟨hAB,hAC⟩ := circumcenter_equidistant A B C hdet
  apply circumcenter_eq_of_equidistant
  · rw [triangleDet_flip]
    exact neg_ne_zero.mpr hdet
  · simpa only [norm_flip_sub] using hAB
  · simpa only [norm_flip_sub] using hAC

def siteMirror (i : Fin 11) : Fin 11 := ![8,7,6,5,4,3,2,1,0,9,10] i
def faceMirror (f : Fin 9) : Fin 9 := ![1,0,7,6,5,4,3,2,8] f
def swapVertex (t : Fin 3) : Fin 3 := ![1,0,2] t
def mirrorVertex (f : Fin 9) (t : Fin 3) : Fin 3 :=
  if f.val<2 then t else swapVertex t

theorem siteMirror_involution (i : Fin 11) : siteMirror (siteMirror i)=i := by
  fin_cases i <;> decide
theorem faceMirror_involution (f : Fin 9) : faceMirror (faceMirror f)=f := by
  fin_cases f <;> decide
theorem face_vertex_mirror :
    ∀ f : Fin 9, ∀ t : Fin 3,
      sourceFaces (faceMirror f) (mirrorVertex f t)=siteMirror (sourceFaces f t) := by
  decide

def siteFull (x : Full) (i : Fin 11) : Point :=
  ![FullCartesianResidual.ring x 0,FullCartesianResidual.ring x 1,
    FullCartesianResidual.ring x 2,FullCartesianResidual.ring x 3,
    FullCartesianResidual.ring x 4,FullCartesianResidual.ring x 5,
    FullCartesianResidual.ring x 6,FullCartesianResidual.ring x 7,
    FullCartesianResidual.ring x 8,FullCartesianResidual.hubA x,FullCartesianResidual.hubB x] i

theorem siteFull_pack (u : Fin 12 → ℝ) (i : Fin 11) :
    siteFull (pack u) i=centersOfRoot u i := by
  fin_cases i <;> simp [siteFull,FullCartesianResidual.ring_pack,
    FullCartesianResidual.hubA_pack,FullCartesianResidual.hubB_pack,centersOfRoot]

theorem siteFull_reflect (x : Full) (i : Fin 11) :
    siteFull (reflect x) (siteMirror i)=flip (siteFull x i) := by
  ext q
  fin_cases i <;> fin_cases q <;> simp [siteFull,siteMirror,reflect,flip,
    FullCartesianResidual.ring,FullCartesianResidual.hubA,FullCartesianResidual.hubB]

/-- Actual SAME-root site identity, paid from proved full Cartesian symmetry. -/
theorem actual_site_reflection (i : Fin 11) :
    centersOfRoot SourceExactRoot.sourceRoot (siteMirror i)=
      flip (centersOfRoot SourceExactRoot.sourceRoot i) := by
  have h := siteFull_reflect (pack SourceExactRoot.sourceRoot) i
  rw [source_fixed,siteFull_pack,siteFull_pack] at h
  exact h

private theorem representative_triangle_det (j : Fin 5) :
    triangleDet (SourceRepresentativeFaceBalance.vertices j 0)
      (SourceRepresentativeFaceBalance.vertices j 1)
      (SourceRepresentativeFaceBalance.vertices j 2)≠0 := by
  have h1 := SourceFanCircumradius.source_triangle_det 1 (by simp)
  have h2 := SourceFanCircumradius.source_triangle_det 2 (by simp)
  have h3 := SourceFanCircumradius.source_triangle_det 3 (by simp)
  have h8 := SourceFanCircumradius.source_triangle_det 8 (by simp)
  simp [SourceFanLengthCovector.sourceHub,nd_fin_succ_1,nd_fin_succ_2,nd_fin_succ_3,
    nd_fin_succ_8,Fin.ext_iff] at h1 h2 h3 h8
  fin_cases j
  · exact h1
  · exact h2
  · exact h3
  · exact h8
  · rw [triangleDet_cyclic]
    exact SourceCentralGeometry.source_triangle_det

theorem representative_source_det (j : Fin 5) :
    triangleDet
      (centersOfRoot SourceExactRoot.sourceRoot (sourceFaces (SourceRepresentativeFaceBalance.faceIndex j) 0))
      (centersOfRoot SourceExactRoot.sourceRoot (sourceFaces (SourceRepresentativeFaceBalance.faceIndex j) 1))
      (centersOfRoot SourceExactRoot.sourceRoot (sourceFaces (SourceRepresentativeFaceBalance.faceIndex j) 2))≠0 := by
  simp only [SourceRepresentativeFaceBalance.source_vertex]
  exact representative_triangle_det j

end
end N11Formalization.SourceFaceReflection
#check @N11Formalization.SourceFaceReflection.actual_site_reflection
#check @N11Formalization.SourceFaceReflection.face_vertex_mirror
#check @N11Formalization.SourceFaceReflection.representative_source_det
#print axioms N11Formalization.SourceFaceReflection.actual_site_reflection
