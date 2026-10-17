import N11Formalization.SourceCentreCovector
import N11Formalization.SourceSelfFaceSymmetry

/-! Actual full9 face centre-force functional equals the orbit-averaged real
representative circumradius force functional. The orbit-size1 fan8 uses
independently proved beta/source symmetry, not an assumed averaging identity. -/
set_option autoImplicit false
namespace N11Formalization.SourceFaceForceTransport
open N11Formalization CartesianReflectionSpace SourceFaceReflection SourceCentreCovector
noncomputable section

private theorem mirror_velocity (v : Full) (i : Fin 11) :
    siteFull v (siteMirror i)=SourceFaceReflection.flip (siteFull (reflect v) i) := by
  have h := siteFull_reflect (reflect v) i
  rw [reflect_involution] at h
  exact h

private theorem sum_vertexPerm (f : Fin 9) (g : Fin 3 → ℝ) :
    (∑ t : Fin 3,g (SourceAllFaceBalance.vertexPerm f t))=∑ t : Fin 3,g t := by
  fin_cases f <;> simp [SourceAllFaceBalance.vertexPerm,swapVertex,Fin.sum_univ_succ] <;> ring

def faceForce (f : Fin 9) (v : Full) : ℝ :=
  ∑ t : Fin 3,SourceAllFaceBalance.beta f t*
    inner ℝ (SourceAllFaceBalance.vertex f t-SourceAllFaceBalance.center f)
      (siteFull v (ResumeLocalIncidence.sourceFaces f t))

theorem faceForce_transport (f : Fin 9) (v : Full) :
    faceForce f v=if SourceAllFaceBalance.mirrored f then
      representativeForce (SourceAllFaceBalance.repIndex f) (reflect v)
      else representativeForce (SourceAllFaceBalance.repIndex f) v := by
  have hv (t : Fin 3) :
      siteFull v (ResumeLocalIncidence.sourceFaces f t)=
        if SourceAllFaceBalance.mirrored f then SourceFaceReflection.flip
          (siteFull (reflect v) (ResumeLocalIncidence.sourceFaces
            (SourceRepresentativeFaceBalance.faceIndex (SourceAllFaceBalance.repIndex f))
            (SourceAllFaceBalance.vertexPerm f t)))
        else siteFull v (ResumeLocalIncidence.sourceFaces
          (SourceRepresentativeFaceBalance.faceIndex (SourceAllFaceBalance.repIndex f))
          (SourceAllFaceBalance.vertexPerm f t)) := by
    rw [SourceAllFaceBalance.source_face_indices]
    split_ifs
    · exact mirror_velocity v _
    · rfl
  unfold faceForce SourceAllFaceBalance.beta SourceAllFaceBalance.vertex SourceAllFaceBalance.center
  simp_rw [hv]
  split_ifs with h
  · simp only [← flip_sub,SourceSelfFaceSymmetry.inner_flip]
    change (∑ t : Fin 3,(fun i : Fin 3 =>
      SourceRepresentativeFaceBalance.beta (SourceAllFaceBalance.repIndex f) i*
        inner ℝ (SourceRepresentativeFaceBalance.vertices (SourceAllFaceBalance.repIndex f) i-
          SourceRepresentativeFaceBalance.center (SourceAllFaceBalance.repIndex f))
          (siteFull (reflect v) (ResumeLocalIncidence.sourceFaces
            (SourceRepresentativeFaceBalance.faceIndex (SourceAllFaceBalance.repIndex f)) i)))
      (SourceAllFaceBalance.vertexPerm f t))=_
    exact sum_vertexPerm f (fun i : Fin 3 =>
      SourceRepresentativeFaceBalance.beta (SourceAllFaceBalance.repIndex f) i*
        inner ℝ (SourceRepresentativeFaceBalance.vertices (SourceAllFaceBalance.repIndex f) i-
          SourceRepresentativeFaceBalance.center (SourceAllFaceBalance.repIndex f))
          (siteFull (reflect v) (ResumeLocalIncidence.sourceFaces
            (SourceRepresentativeFaceBalance.faceIndex (SourceAllFaceBalance.repIndex f)) i)))
  · change (∑ t : Fin 3,(fun i : Fin 3 =>
      SourceRepresentativeFaceBalance.beta (SourceAllFaceBalance.repIndex f) i*
        inner ℝ (SourceRepresentativeFaceBalance.vertices (SourceAllFaceBalance.repIndex f) i-
          SourceRepresentativeFaceBalance.center (SourceAllFaceBalance.repIndex f))
          (siteFull v (ResumeLocalIncidence.sourceFaces
            (SourceRepresentativeFaceBalance.faceIndex (SourceAllFaceBalance.repIndex f)) i)))
      (SourceAllFaceBalance.vertexPerm f t))=_
    exact sum_vertexPerm f (fun i : Fin 3 =>
      SourceRepresentativeFaceBalance.beta (SourceAllFaceBalance.repIndex f) i*
        inner ℝ (SourceRepresentativeFaceBalance.vertices (SourceAllFaceBalance.repIndex f) i-
          SourceRepresentativeFaceBalance.center (SourceAllFaceBalance.repIndex f))
          (siteFull v (ResumeLocalIncidence.sourceFaces
            (SourceRepresentativeFaceBalance.faceIndex (SourceAllFaceBalance.repIndex f)) i)))

private theorem self_formula (v : Full) :
    representativeForce 3 v=
      SourceFanConversion.betaP 8*inner ℝ
        (ringCenter SourceExactRoot.sourceRoot 8-Uvec SourceExactRoot.sourceRoot 8)
        (FullCartesianResidual.ring v 8)+
      SourceFanConversion.betaQ 8*inner ℝ
        (ringCenter SourceExactRoot.sourceRoot 0-Uvec SourceExactRoot.sourceRoot 8)
        (FullCartesianResidual.ring v 0)+
      SourceFanConversion.betaH 8*inner ℝ
        (hub1 SourceExactRoot.sourceRoot-Uvec SourceExactRoot.sourceRoot 8)
        (FullCartesianResidual.hubB v) := by
  simp [representativeForce,SourceRepresentativeFaceBalance.beta,
    SourceRepresentativeFaceBalance.vertices,SourceRepresentativeFaceBalance.center,
    SourceRepresentativeFaceBalance.faceIndex,ResumeLocalIncidence.sourceFaces,siteFull,
    Fin.sum_univ_succ,add_assoc]

theorem self_force_invariant (v : Full) : representativeForce 3 (reflect v)=representativeForce 3 v := by
  have hr8 : FullCartesianResidual.ring (reflect v) 8=
      SourceFaceReflection.flip (FullCartesianResidual.ring v 0) := by
    have h := siteFull_reflect v 0
    simpa only [siteFull,siteMirror,Matrix.cons_val_zero,Matrix.cons_val] using h
  have hr0 : FullCartesianResidual.ring (reflect v) 0=
      SourceFaceReflection.flip (FullCartesianResidual.ring v 8) := by
    have h := siteFull_reflect v 8
    simpa [siteFull,siteMirror] using h
  have hh : FullCartesianResidual.hubB (reflect v)=
      SourceFaceReflection.flip (FullCartesianResidual.hubB v) := by
    ext i
    fin_cases i <;> simp [FullCartesianResidual.hubB,reflect,SourceFaceReflection.flip]
  rw [self_formula,self_formula,hr8,hr0,hh]
  simp only [← SourceSelfFaceSymmetry.inner_flip_left,flip_sub,
    SourceSelfFaceSymmetry.ring8_reflection,SourceSelfFaceSymmetry.ring0_reflection,
    SourceSelfFaceSymmetry.hub1_reflection,SourceSelfFaceSymmetry.center8_reflection,
    SourceSelfFaceSymmetry.beta8_symmetry]
  ring

def totalFaceForce (v : Full) : ℝ :=
  ∑ f : Fin 9,SourceAllFaceBalance.faceWeight f*faceForce f v

theorem totalFaceForce_average (v : Full) :
    totalFaceForce v=(2 : ℝ)⁻¹*
      ((∑ j : Fin 5,PhysicalInteriorObjective.weight j*representativeForce j v)+
       (∑ j : Fin 5,PhysicalInteriorObjective.weight j*representativeForce j (reflect v))) := by
  unfold totalFaceForce
  simp_rw [faceForce_transport]
  simp [SourceAllFaceBalance.faceWeight,SourceAllFaceBalance.repIndex,
    SourceAllFaceBalance.orbitSize,SourceAllFaceBalance.mirrored,Fin.sum_univ_succ,self_force_invariant]
  ring

theorem totalFaceForce_actual (v : Full) :
    totalFaceForce v=∑ f : Fin 9,∑ t : Fin 3,SourceAllFaceBalance.coefficient f t*
      inner ℝ
        (centersOfRoot SourceExactRoot.sourceRoot (ResumeLocalIncidence.sourceFaces f t)-
          SourceN2.srcZ2 SourceExactRoot.sourceRoot f)
        (siteFull v (ResumeLocalIncidence.sourceFaces f t)) := by
  simp only [totalFaceForce,faceForce,SourceAllFaceBalance.coefficient,
    SourceAllFaceBalance.actual_aux,SourceAllFaceBalance.actual_vertex,Finset.mul_sum,mul_assoc]

end
end N11Formalization.SourceFaceForceTransport
#check @N11Formalization.SourceFaceForceTransport.totalFaceForce_average
#check @N11Formalization.SourceFaceForceTransport.totalFaceForce_actual
#print axioms N11Formalization.SourceFaceForceTransport.totalFaceForce_average
