import N11Formalization.SourceResponseFluxIdentity

/-! Exact base-energy calibration at SAME root: all45 carrying edges have
sourceRoot6 length, normalized actual energy=sourceRadius², and the already
constructed harmonic certificate matches the actual canonical oracle at the
SOURCE datum. The source oracle upper uses the paid full51 feasible witness;
zero stress does not delete primal slack constraints. NOT arbitrary-cover
global optimality or sharpness for other boundary data. -/
set_option autoImplicit false
namespace N11Formalization.SourceSharpEnergyCalibration
open N11Formalization ResumeNetwork ResumeLocalIncidence
open SourceCentreB2Readout SourcePositiveHarmonicConsumer
noncomputable section

private theorem fan_distances (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ‖ringCenter SourceExactRoot.sourceRoot k-Uvec SourceExactRoot.sourceRoot k‖=
      SourceExactRoot.sourceRoot 6 ∧
    ‖ringCenter SourceExactRoot.sourceRoot (k+1)-Uvec SourceExactRoot.sourceRoot k‖=
      SourceExactRoot.sourceRoot 6 ∧
    ‖SourceFanLengthCovector.sourceHub k-Uvec SourceExactRoot.sourceRoot k‖=
      SourceExactRoot.sourceRoot 6 := by
  have h := TrueCirclePinSmooth.source_distances k
  simp only [TrueCirclePinSmooth.left_source,TrueCirclePinSmooth.right_source,
    TrueCirclePinSmooth.radius_source] at h
  refine ⟨?_,?_,?_⟩
  · rw [norm_sub_rev]
    exact h.1
  · rw [norm_sub_rev]
    exact h.2
  · rw [norm_sub_rev]
    exact SourceFanLengthCovector.source_normalH_norm k hk

theorem representative_lengths (j : Fin 5) (t : Fin 3) :
    ‖SourceRepresentativeFaceBalance.vertices j t-SourceRepresentativeFaceBalance.center j‖=
      SourceExactRoot.sourceRoot 6 := by
  have h1 := fan_distances 1 (by simp)
  have h2 := fan_distances 2 (by simp)
  have h3 := fan_distances 3 (by simp)
  have h8 := fan_distances 8 (by simp)
  have hH : ‖SourceCentralGeometry.H-SourceCentralGeometry.U‖=SourceExactRoot.sourceRoot 6 :=
    by simpa only [norm_sub_rev,SourceCentralGeometry.R] using SourceCentralGeometry.source_distances.2.2
  have hP : ‖SourceCentralGeometry.P-SourceCentralGeometry.U‖=SourceExactRoot.sourceRoot 6 :=
    by simpa only [norm_sub_rev,SourceCentralGeometry.R] using SourceCentralGeometry.source_distances.1
  have hQ : ‖SourceCentralGeometry.Q-SourceCentralGeometry.U‖=SourceExactRoot.sourceRoot 6 :=
    by simpa only [norm_sub_rev,SourceCentralGeometry.R] using SourceCentralGeometry.source_distances.2.1
  simp only [SourceFanLengthCovector.sourceHub,Fin.ext_iff,nd_fin_succ_1,
    nd_fin_succ_2,nd_fin_succ_3,nd_fin_succ_8] at h1 h2 h3 h8
  fin_cases j <;> fin_cases t
  all_goals simp only [SourceRepresentativeFaceBalance.vertices,SourceRepresentativeFaceBalance.center,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
  · exact h1.1
  · exact h1.2.1
  · exact h1.2.2
  · exact h2.1
  · exact h2.2.1
  · exact h2.2.2
  · exact h3.1
  · exact h3.2.1
  · exact h3.2.2
  · exact h8.1
  · exact h8.2.1
  · exact h8.2.2
  · exact hH
  · exact hP
  · exact hQ

theorem all_face_lengths (f : Fin 9) (t : Fin 3) :
    ‖centersOfRoot SourceExactRoot.sourceRoot (sourceFaces f t)-
      SourceN2.srcZ2 SourceExactRoot.sourceRoot f‖=SourceExactRoot.sourceRoot 6 := by
  rw [SourceAllFaceBalance.actual_vertex,SourceAllFaceBalance.actual_aux]
  unfold SourceAllFaceBalance.vertex SourceAllFaceBalance.center
  split_ifs
  · rw [SourceFaceReflection.norm_flip_sub]
    exact representative_lengths _ _
  · exact representative_lengths _ _

theorem carrying_edge_length (e : SourceEdge) :
    edgeLength sourceAnchors sourceCenters sourceAux (edgeMap e)=SourceExactRoot.sourceRadius := by
  have h := FlashRootNetwork.edgeLength_edgeMap_eq_sourceLength SourceExactRoot.sourceRoot sourceAux e
  change edgeLength sourceAnchors sourceCenters sourceAux (edgeMap e)=_ at h
  rw [h]
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · have hp := SourceBoundaryTie.source_endpoint_distances k
    fin_cases s
    · simpa [sourceLength,centersOfRoot_ring,dist_eq_norm,norm_sub_rev,
        SourceExactRoot.sourceRadius,Fin.ext_iff] using hp.1
    · have hs : (1 : Fin 2)≠0 := by decide
      simpa [sourceLength,centersOfRoot_ring,dist_eq_norm,norm_sub_rev,hs,
        SourceExactRoot.sourceRadius,Fin.ext_iff] using hp.2
  · have haux : sourceAux (faceMap f)=SourceN2.srcZ2 SourceExactRoot.sourceRoot f :=
      (LocalSharpAuxZ.canonFaceZ_active SourceExactRoot.sourceRoot f).trans
        (congrFun (SourceN2.srcZ2_eq_auxZ SourceExactRoot.sourceRoot) f).symm
    simp only [sourceLength,haux,dist_eq_norm]
    exact all_face_lengths f t

/-- Exact calibration of the actual weighted source energy. Six zero-weight
slack edges affect this weighted identity only, not primal feasibility. -/
theorem actual_source_energy :
    energy canonicalStress sourceAnchors sourceCenters sourceAux=SourceExactRoot.sourceRadius^2 := by
  unfold energy
  rw [sum_reindex _ (fun f q hf => by
    rcases hf with rfl | rfl
    · simp only [(canonical_slack_zero q).1,zero_mul]
    · simp only [(canonical_slack_zero q).2,zero_mul])]
  simp only [canonicalStress,SourceAlphaOf.alphaEdge_edgeMap,carrying_edge_length]
  rw [← Finset.sum_mul,SourceSignedStressAssembly.stress_mass_one,one_mul]

theorem source_dirichlet_radius_sq :
    dirichletEnergy canonicalStress sourceAnchors=SourceExactRoot.sourceRadius^2 :=
  source_dirichlet_energy.trans actual_source_energy

theorem source_oracle_lower :
    SourceExactRoot.sourceRadius^2≤V2 sourceAnchors := by
  have h := source_harmonic_le_oracle sourceAnchors
    (fun j => (SourceResponseFluxIdentity.sourceAnchors_unit j).le)
  have he :
      (∑ e : Edge,canonicalStress e*
        ‖∑ j : Fin 9,ResumeHarmonic.coeff sourceH e j • sourceAnchors j‖^2)=
          SourceExactRoot.sourceRadius^2 :=
    (ResumeResponseGram.gram_energy canonicalStress (ResumeHarmonic.coeff sourceH) sourceAnchors).symm.trans
      ((source_response_identity sourceAnchors).trans source_dirichlet_radius_sq)
  rw [he] at h
  exact h

theorem source_oracle_upper :
    V2 sourceAnchors≤SourceExactRoot.sourceRadius^2 :=
  FlashRootNetwork.oracle_le_sq_root SourceExactRoot.sourceSpec rfl rfl rfl rfl

/-- EXACT source-datum oracle value; NOT a lower bound for other W or Covers. -/
theorem source_oracle_eq :
    V2 sourceAnchors=SourceExactRoot.sourceRadius^2 :=
  le_antisymm source_oracle_upper source_oracle_lower

end
end N11Formalization.SourceSharpEnergyCalibration
#check @N11Formalization.SourceSharpEnergyCalibration.carrying_edge_length
#check @N11Formalization.SourceSharpEnergyCalibration.actual_source_energy
#check @N11Formalization.SourceSharpEnergyCalibration.source_oracle_eq
#print axioms N11Formalization.SourceSharpEnergyCalibration.actual_source_energy
#print axioms N11Formalization.SourceSharpEnergyCalibration.source_oracle_eq
