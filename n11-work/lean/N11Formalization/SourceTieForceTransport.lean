import N11Formalization.SourceFaceForceTransport

/-! Actual source tie/spoke centre-force covectors and reflection orbit split.
All functions use arcEnd and the signed45 assembly, not a second stress.
Positivity of physical tie weights is not needed for these identities. -/
set_option autoImplicit false
namespace N11Formalization.SourceTieForceTransport
open N11Formalization CartesianReflectionSpace SourceFaceReflection
noncomputable section

def tieMirror (k : Fin 9) : Fin 9 := ![7,6,5,4,3,2,1,0,8] k
def spokeSite (k : Fin 9) (s : Fin 2) : Fin 11 := ⟨(if s=0 then k else k+1).val,by omega⟩
def opposite (s : Fin 2) : Fin 2 := ![1,0] s
private theorem succ_four : (4 : Fin 9)+1=5 := by decide

theorem spoke_site_mirror :
    ∀ k : Fin 9, ∀ s : Fin 2,
      spokeSite (tieMirror k) (opposite s)=siteMirror (spokeSite k s) := by decide

private theorem endpoint_angle_mirror (k : Fin 8) :
    arcHiG SourceExactRoot.sourceRoot (tieMirror ⟨k.val,by omega⟩) =
      -arcHiG SourceExactRoot.sourceRoot ⟨k.val,by omega⟩ := by
  fin_cases k <;> simp [arcHiG,tieMirror,thetaOf,angleVec] <;> ring

theorem endpoint_reflection (k : Fin 9) :
    arcEnd SourceExactRoot.sourceRoot (tieMirror k)=
      SourceFaceReflection.flip (arcEnd SourceExactRoot.sourceRoot k) := by
  by_cases hk : k=8
  · subst k
    exact SourceSelfFaceSymmetry.endpoint8_reflection.symm
  · let k8 : Fin 8 := ⟨k.val,by omega⟩
    have he := endpoint_angle_mirror k8
    change arcHiG SourceExactRoot.sourceRoot (tieMirror k)=-arcHiG SourceExactRoot.sourceRoot k at he
    rw [arcEnd_eq_circleMap,arcEnd_eq_circleMap]
    change circleMap (arcHiG SourceExactRoot.sourceRoot (tieMirror k))=
      SourceFaceReflection.flip (circleMap (arcHiG SourceExactRoot.sourceRoot k))
    rw [he]
    ext i
    fin_cases i <;> simp [circleMap,SourceFaceReflection.flip]

theorem eta_reflection (k : Fin 9) :
    SourceBoundaryTieDerivative.eta (tieMirror k)=1-SourceBoundaryTieDerivative.eta k := by
  have hp : SourceBoundaryWeights.slope (tieMirror k)=SourceBoundaryWeights.slope (k+1) := by
    fin_cases k <;> simp [SourceBoundaryWeights.slope,tieMirror,rhoK,angleVec,
      nd_fin_succ_0,nd_fin_succ_1,nd_fin_succ_2,nd_fin_succ_3,succ_four,
      nd_fin_succ_5,nd_fin_succ_6,nd_fin_succ_7,nd_fin_succ_8]
  have hq : SourceBoundaryWeights.slope (tieMirror k+1)=SourceBoundaryWeights.slope k := by
    fin_cases k <;> simp [SourceBoundaryWeights.slope,tieMirror,rhoK,angleVec,
      nd_fin_succ_0,nd_fin_succ_1,nd_fin_succ_2,nd_fin_succ_3,succ_four,
      nd_fin_succ_5,nd_fin_succ_6,nd_fin_succ_7,nd_fin_succ_8]
  rw [SourceBoundaryWeights.eta_eq,SourceBoundaryWeights.eta_eq,hp,hq]
  have hd := ne_of_gt (add_pos (SourceBoundaryWeights.slope_pos k)
    (SourceBoundaryWeights.slope_pos (k+1)))
  have hd' := ne_of_gt (add_pos (SourceBoundaryWeights.slope_pos (k+1))
    (SourceBoundaryWeights.slope_pos k))
  field_simp [hd,hd']
  ring

theorem split_reflection (k : Fin 9) (s : Fin 2) :
    SourceSignedStressAssembly.split (tieMirror k) (opposite s)=
      SourceSignedStressAssembly.split k s := by
  fin_cases s
  · change (1-SourceBoundaryTieDerivative.eta (tieMirror k))=SourceBoundaryTieDerivative.eta k
    rw [eta_reflection]
    ring
  · change SourceBoundaryTieDerivative.eta (tieMirror k)=1-SourceBoundaryTieDerivative.eta k
    exact eta_reflection k

def tieForce (k : Fin 9) (v : Full) : ℝ :=
  ∑ s : Fin 2,SourceSignedStressAssembly.split k s*
    inner ℝ (centersOfRoot SourceExactRoot.sourceRoot (spokeSite k s)-arcEnd SourceExactRoot.sourceRoot k)
      (siteFull v (spokeSite k s))

private theorem opposite_sum (g : Fin 2 → ℝ) : (∑ s : Fin 2,g (opposite s))=∑ s : Fin 2,g s := by
  simp [opposite,Fin.sum_univ_two]
  ring

theorem tieForce_mirror (k : Fin 9) (v : Full) :
    tieForce (tieMirror k) v=tieForce k (reflect v) := by
  have hv (i : Fin 11) : siteFull v (siteMirror i)=SourceFaceReflection.flip (siteFull (reflect v) i) := by
    have h := siteFull_reflect (reflect v) i
    rw [reflect_involution] at h
    exact h
  have hs := opposite_sum (fun s : Fin 2 =>
    SourceSignedStressAssembly.split (tieMirror k) s*
      inner ℝ (centersOfRoot SourceExactRoot.sourceRoot (spokeSite (tieMirror k) s)-
        arcEnd SourceExactRoot.sourceRoot (tieMirror k))
        (siteFull v (spokeSite (tieMirror k) s)))
  unfold tieForce
  rw [← hs]
  apply Finset.sum_congr rfl
  intro s _
  rw [split_reflection,spoke_site_mirror,actual_site_reflection,endpoint_reflection,hv,
    ← flip_sub,SourceSelfFaceSymmetry.inner_flip]

theorem representative_tie_radius_force (j : Fin 5) (v : Full) :
    fderiv ℝ (SourceBoundaryTie.radiusExcess (BoundaryGapConversion.representative j))
      FullCartesianResidual.sourcePoint v =
      tieForce (BoundaryGapConversion.representative j) v/SourceExactRoot.sourceRoot 6-v 22 := by
  have hk := BoundaryGapConversion.representative_active j
  rw [BoundaryGapConversion.excess_source_fderiv _ hk,
    SourceBoundaryTieDerivative.radiusFull_source_fderiv _ hk]
  have he (k : Fin 9) :
      tieForce k v =
        SourceBoundaryTieDerivative.eta k*inner ℝ
          (ringCenter SourceExactRoot.sourceRoot k-arcEnd SourceExactRoot.sourceRoot k)
          (FullCartesianResidual.ring v k)+
        (1-SourceBoundaryTieDerivative.eta k)*inner ℝ
          (ringCenter SourceExactRoot.sourceRoot (k+1)-arcEnd SourceExactRoot.sourceRoot k)
          (FullCartesianResidual.ring v (k+1)) := by
    rw [tieForce,Fin.sum_univ_two]
    simp [SourceSignedStressAssembly.split,spokeSite,centersOfRoot,
      SourceCentreCovector.source_site_velocity_ring,Fin.ext_iff]
  rw [he]
  unfold SourceBoundaryTieDerivative.nP SourceBoundaryTieDerivative.nQ SourceBoundaryTieDerivative.T
  simp only [inner_sub_left]
  ring

def totalTieForce (v : Full) : ℝ :=
  ∑ k : Fin 9,SourceSignedStressAssembly.tieWeight k*tieForce k v

theorem totalTieForce_average (v : Full) :
    totalTieForce v=(2 : ℝ)⁻¹*
      ((∑ j : Fin 5,PhysicalBoundaryStationarity.tieWeight j*
          tieForce (BoundaryGapConversion.representative j) v)+
       (∑ j : Fin 5,PhysicalBoundaryStationarity.tieWeight j*
          tieForce (BoundaryGapConversion.representative j) (reflect v))) := by
  have h0 := tieForce_mirror 0 v
  have h1 := tieForce_mirror 1 v
  have h2 := tieForce_mirror 2 v
  have h3 := tieForce_mirror 3 v
  have h8 := tieForce_mirror 8 v
  simp only [tieMirror,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Fin.reduceFinMk] at h0 h1 h2 h3 h8
  simp [totalTieForce,SourceSignedStressAssembly.tieWeight,SourceSignedStressAssembly.tieRep,
    SourceSignedStressAssembly.tieOrbitSize,BoundaryGapConversion.representative,Fin.sum_univ_succ]
  rw [h0,h1,h2,h3,← h8]
  ring

end
end N11Formalization.SourceTieForceTransport
#check @N11Formalization.SourceTieForceTransport.tieForce_mirror
#check @N11Formalization.SourceTieForceTransport.totalTieForce_average
#print axioms N11Formalization.SourceTieForceTransport.totalTieForce_average
