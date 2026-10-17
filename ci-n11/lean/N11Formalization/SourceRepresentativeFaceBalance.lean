import N11Formalization.SourceFanBarycentricSigns
import N11Formalization.PhysicalInteriorObjective
import N11Formalization.SourceN2Geom

/-!
Actual five representative active faces are bound to the CORRECT Fin11 source
table and shared SourceN2 circumcentres. Their positive barycentric edge
coefficients give the actual two auxiliary B2 rows for each representative.
These are local face blocks, not the full reflected45-edge stress, centre
balance or the complete40-row B2 certificate.
-/
set_option autoImplicit false
namespace N11Formalization.SourceRepresentativeFaceBalance
open N11Formalization ResumeLocalIncidence
noncomputable section

def faceIndex (j : Fin 5) : Fin 9 := ![2,3,4,8,1] j
def vertices (j : Fin 5) : Fin 3 → Point :=
  ![![ringCenter SourceExactRoot.sourceRoot 1,ringCenter SourceExactRoot.sourceRoot 2,hub1 SourceExactRoot.sourceRoot],
    ![ringCenter SourceExactRoot.sourceRoot 2,ringCenter SourceExactRoot.sourceRoot 3,hub0 SourceExactRoot.sourceRoot],
    ![ringCenter SourceExactRoot.sourceRoot 3,ringCenter SourceExactRoot.sourceRoot 4,hub0 SourceExactRoot.sourceRoot],
    ![ringCenter SourceExactRoot.sourceRoot 8,ringCenter SourceExactRoot.sourceRoot 0,hub1 SourceExactRoot.sourceRoot],
    ![SourceCentralGeometry.H,SourceCentralGeometry.P,SourceCentralGeometry.Q]] j
def center (j : Fin 5) : Point :=
  ![Uvec SourceExactRoot.sourceRoot 1,Uvec SourceExactRoot.sourceRoot 2,
    Uvec SourceExactRoot.sourceRoot 3,Uvec SourceExactRoot.sourceRoot 8,SourceCentralGeometry.U] j
def beta (j : Fin 5) : Fin 3 → ℝ :=
  ![![SourceFanConversion.betaP 1,SourceFanConversion.betaQ 1,SourceFanConversion.betaH 1],
    ![SourceFanConversion.betaP 2,SourceFanConversion.betaQ 2,SourceFanConversion.betaH 2],
    ![SourceFanConversion.betaP 3,SourceFanConversion.betaQ 3,SourceFanConversion.betaH 3],
    ![SourceFanConversion.betaP 8,SourceFanConversion.betaQ 8,SourceFanConversion.betaH 8],
    ![SourceCentralGeometry.betaH,SourceCentralGeometry.betaP,SourceCentralGeometry.betaQ]] j

theorem source_vertex (j : Fin 5) (t : Fin 3) :
    centersOfRoot SourceExactRoot.sourceRoot (sourceFaces (faceIndex j) t)=vertices j t := by
  fin_cases j <;> fin_cases t <;>
    simp [faceIndex,vertices,sourceFaces,centersOfRoot,SourceCentralGeometry.H,
      SourceCentralGeometry.P,SourceCentralGeometry.Q,Fin.reduceFinMk]

theorem beta_pos (j : Fin 5) (t : Fin 3) : 0<beta j t := by
  have h1 := SourceFanBarycentricSigns.source_betas_pos 1 (by simp)
  have h2 := SourceFanBarycentricSigns.source_betas_pos 2 (by simp)
  have h3 := SourceFanBarycentricSigns.source_betas_pos 3 (by simp)
  have h8 := SourceFanBarycentricSigns.source_betas_pos 8 (by simp)
  have hc := SourceFanBarycentricSigns.central_betas_pos
  fin_cases j <;> fin_cases t
  all_goals first
    | exact h1.1 | exact h1.2.1 | exact h1.2.2
    | exact h2.1 | exact h2.2.1 | exact h2.2.2
    | exact h3.1 | exact h3.2.1 | exact h3.2.2
    | exact h8.1 | exact h8.2.1 | exact h8.2.2
    | exact hc.1 | exact hc.2.1 | exact hc.2.2

theorem beta_sum (j : Fin 5) : ∑ t : Fin 3, beta j t=1 := by
  have h1 := SourceFanConversion.beta_sum_one 1 (by simp)
  have h2 := SourceFanConversion.beta_sum_one 2 (by simp)
  have h3 := SourceFanConversion.beta_sum_one 3 (by simp)
  have h8 := SourceFanConversion.beta_sum_one 8 (by simp)
  have hc := SourceCentralGeometry.beta_sum_one
  fin_cases j <;> simp [beta,Fin.sum_univ_succ]
  all_goals linarith

theorem center_affine (j : Fin 5) :
    center j=∑ t : Fin 3, beta j t • vertices j t := by
  have h1 := SourceFanConversion.beta_center_identity 1 (by simp)
  have h2 := SourceFanConversion.beta_center_identity 2 (by simp)
  have h3 := SourceFanConversion.beta_center_identity 3 (by simp)
  have h8 := SourceFanConversion.beta_center_identity 8 (by simp)
  have hc := SourceCentralGeometry.beta_center_identity
  simp [SourceFanLengthCovector.sourceHub,nd_fin_succ_1,nd_fin_succ_2,
    nd_fin_succ_3,nd_fin_succ_8,Fin.ext_iff,add_assoc] at h1 h2 h3 h8
  fin_cases j <;> simp [center,beta,vertices,Fin.sum_univ_succ]
  · exact h1
  · exact h2
  · exact h3
  · exact h8
  · calc
      SourceCentralGeometry.U =
          SourceCentralGeometry.betaP • SourceCentralGeometry.P+
          SourceCentralGeometry.betaQ • SourceCentralGeometry.Q+
          SourceCentralGeometry.betaH • SourceCentralGeometry.H := hc
      _ = _ := by abel

private theorem fan_circumcenter_source (k : Fin 9)
    (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    circumcenter (ringCenter SourceExactRoot.sourceRoot k)
      (ringCenter SourceExactRoot.sourceRoot (k+1))
      (SourceFanLengthCovector.sourceHub k)=Uvec SourceExactRoot.sourceRoot k := by
  have h := SourceFanCircumradius.center_source k hk
  have hr (i : Fin 9) :
      FullCartesianResidual.ring FullCartesianResidual.sourcePoint i=ringCenter SourceExactRoot.sourceRoot i :=
    FullCartesianResidual.ring_pack _ i
  simpa only [SourceFanCircumradius.center,hr,SourceFanLengthCovector.fullHub_source] using h

private theorem central_cyclic_det :
    CircumcenterGeometry.triangleDet SourceCentralGeometry.H SourceCentralGeometry.P SourceCentralGeometry.Q=
      CircumcenterGeometry.triangleDet SourceCentralGeometry.P SourceCentralGeometry.Q SourceCentralGeometry.H := by
  unfold CircumcenterGeometry.triangleDet PinTangentGeometry.det
  simp only [PiLp.sub_apply]
  ring

theorem source_aux (j : Fin 5) :
    SourceN2.srcZ2 SourceExactRoot.sourceRoot (faceIndex j)=center j := by
  rw [SourceN2.srcZ2_eq,source_vertex,source_vertex,source_vertex]
  have h1 := fan_circumcenter_source 1 (by simp)
  have h2 := fan_circumcenter_source 2 (by simp)
  have h3 := fan_circumcenter_source 3 (by simp)
  have h8 := fan_circumcenter_source 8 (by simp)
  simp [SourceFanLengthCovector.sourceHub,nd_fin_succ_1,nd_fin_succ_2,
    nd_fin_succ_3,nd_fin_succ_8,Fin.ext_iff] at h1 h2 h3 h8
  fin_cases j
  · exact h1
  · exact h2
  · exact h3
  · exact h8
  · apply CircumcenterGeometry.circumcenter_eq_of_equidistant
      SourceCentralGeometry.H SourceCentralGeometry.P SourceCentralGeometry.Q SourceCentralGeometry.U
    · rw [central_cyclic_det]
      exact SourceCentralGeometry.source_triangle_det
    · exact SourceCentralGeometry.source_distances.2.2.trans SourceCentralGeometry.source_distances.1.symm
    · exact SourceCentralGeometry.source_distances.2.2.trans SourceCentralGeometry.source_distances.2.1.symm

def edgeCoefficient (j : Fin 5) (t : Fin 3) : ℝ := PhysicalInteriorObjective.weight j*beta j t
theorem edgeCoefficient_pos (j : Fin 5) (t : Fin 3) : 0<edgeCoefficient j t :=
  mul_pos (PhysicalInteriorObjective.weight_pos j) (beta_pos j t)

/-- Actual source auxiliary vector balance. This only concerns the three face
edges; it is NOT the full45-edge centre force-balance theorem. -/
theorem actual_auxiliary_balance (j : Fin 5) :
    ∑ t : Fin 3, edgeCoefficient j t •
      (SourceN2.srcZ2 SourceExactRoot.sourceRoot (faceIndex j) -
        centersOfRoot SourceExactRoot.sourceRoot (sourceFaces (faceIndex j) t))=0 := by
  simp only [edgeCoefficient,source_aux,source_vertex,mul_smul]
  rw [← Finset.smul_sum]
  have hz : (∑ t : Fin 3, beta j t • (center j-vertices j t))=0 := by
    simp only [smul_sub,Finset.sum_sub_distrib]
    rw [← Finset.sum_smul,beta_sum,one_smul,← center_affine,sub_self]
  rw [hz,smul_zero]

/-- Ten actual auxiliary B2 coordinate equations, indexed by the correct
five Fin9 source faces and their actual (22+2*f+c) rows. All source geometry
and all positive three-edge coefficients are supplied, not assumed. -/
theorem actual_auxiliary_B2_rows (j : Fin 5) (c : Fin 2) :
    ∑ t : Fin 3,
      SourceN2.srcB2 SourceExactRoot.sourceRoot
        (⟨22+2*(faceIndex j).val+c.val,by omega⟩ : Fin 41)
        (SourceN2.faceFlatEdge (faceIndex j) t) * edgeCoefficient j t=0 := by
  simp only [SourceN2Geom.srcB2_face_aux_row,SourceN2.srcD2_face]
  have hc := congrArg (fun p : Point => p c) (actual_auxiliary_balance j)
  simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,
    PiLp.sub_apply,PiLp.zero_apply,smul_eq_mul] at hc
  convert hc using 1
  apply Finset.sum_congr rfl
  intro t _
  ring

end
end N11Formalization.SourceRepresentativeFaceBalance
#check @N11Formalization.SourceRepresentativeFaceBalance.source_aux
#check @N11Formalization.SourceRepresentativeFaceBalance.edgeCoefficient_pos
#check @N11Formalization.SourceRepresentativeFaceBalance.actual_auxiliary_B2_rows
#print axioms N11Formalization.SourceRepresentativeFaceBalance.actual_auxiliary_B2_rows
