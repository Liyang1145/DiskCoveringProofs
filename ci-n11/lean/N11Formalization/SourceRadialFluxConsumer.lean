import N11Formalization.SourceRadialFluxGeometry

/-! Actual canonical51 anchor flux, derived from the same actual45 carrying
stress and correctly reindexed source spokes. The outward loads are positive
and are transported to the constructed harmonic lift. No flux premise. -/
set_option autoImplicit false
namespace N11Formalization.SourceRadialFluxConsumer
open N11Formalization ResumeNetwork ResumeDirichlet ResumeAnchorFlux
open ResumeLocalIncidence SourceCentreB2Readout SourcePositiveHarmonicConsumer
open SourceRadialFluxGeometry
noncomputable section

theorem siteMap_injective : Function.Injective siteMap := by decide

theorem incidence_source_spoke (k l : Fin 9) (s : Fin 2) :
    anchorIncidence (edgeMap (.inl (l,s))) (siteMap k)=
      if l=k then -1 else 0 := by
  have hi : siteMap l=siteMap k ↔ l=k := siteMap_injective.eq_iff
  fin_cases s
  · change (if anchorIndex (siteMap l) 1=siteMap k then (-1 : ℝ) else 0)=_
    simp only [SourceN2GeomEdge.anchorIndex_side_one,hi]
  · change (if anchorIndex (siteMap (l+1)) 0=siteMap k then (-1 : ℝ) else 0)=_
    simp only [SourceN2GeomEdge.anchorIndex_side_zero_succ,hi]

theorem vector_source_spoke (l : Fin 9) (s : Fin 2) :
    ResumeDirichlet.edgeVector sourceAnchors sourceCenters sourceAux (edgeMap (.inl (l,s)))=
      centersOfRoot SourceExactRoot.sourceRoot (SourceTieForceTransport.spokeSite l s)-
        arcEnd SourceExactRoot.sourceRoot l := by
  fin_cases s
  · change ResumeDirichlet.edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
      (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot) sourceAux
      (.inl (siteMap l,1))=_
    simp only [ResumeDirichlet.edgeVector,SourceN2GeomEdge.anchorIndex_side_one,
      FlashRootNetwork.hU_siteMap,SourceN2GeomEdge.canonCenters_siteMap]
    rfl
  · change ResumeDirichlet.edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
      (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot) sourceAux
      (.inl (siteMap (l+1),0))=_
    simp only [ResumeDirichlet.edgeVector,SourceN2GeomEdge.anchorIndex_side_zero_succ,
      FlashRootNetwork.hU_siteMap,SourceN2GeomEdge.canonCenters_siteMap]
    simp [SourceTieForceTransport.spokeSite,Fin.ext_iff]

/-- Correct source/canonical anchor transport. Boundary incidence contributes
a minus sign, converting centre-minus-anchor into outward anchor-minus-centre. -/
theorem flux_source_spokes (k : Fin 9) :
    flux canonicalStress sourceAnchors sourceCenters sourceAux (siteMap k)=
      ∑ s : Fin 2,SourceSignedStressAssembly.stress (.inl (k,s)) •
        (arcEnd SourceExactRoot.sourceRoot k-
          centersOfRoot SourceExactRoot.sourceRoot (SourceTieForceTransport.spokeSite k s)) := by
  classical
  have hz (e : Edge) (he : e∉Finset.univ.image edgeMap) :
      anchorIncidence e (siteMap k)*canonicalStress e=0 := by
    have hn : ¬∃ s : SourceEdge,edgeMap s=e := by simpa using he
    have hα := SourceAlphaOf.alphaEdge_of_not_mem SourceSignedStressAssembly.stress hn
    change canonicalStress e=0 at hα
    rw [hα,mul_zero]
  have hr := HarmonicSourceGeometryV2.point_sum_edgeMap_reindex
    (α := fun e => anchorIncidence e (siteMap k)*canonicalStress e)
    (F := ResumeDirichlet.edgeVector sourceAnchors sourceCenters sourceAux) hz
  rw [flux,hr,Fintype.sum_sum_type]
  have hf (p : Fin 9 × Fin 3) : anchorIncidence (edgeMap (.inr p)) (siteMap k)=0 := rfl
  simp only [hf,zero_mul,zero_smul,Finset.sum_const_zero,add_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [incidence_source_spoke,vector_source_spoke,canonicalStress,
    SourceAlphaOf.alphaEdge_edgeMap]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true,neg_one_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [neg_smul,← smul_neg,neg_sub]
  · intro l _ hl
    simp only [if_neg hl,zero_mul,zero_smul,Finset.sum_const_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

theorem canonical_flux_raw (k : Fin 9) :
    flux canonicalStress sourceAnchors sourceCenters sourceAux (siteMap k)=
      rawLoad k • arcEnd SourceExactRoot.sourceRoot k := by
  rw [flux_source_spokes]
  exact raw_spoke_resultant k

def sourceLoad (j : Fin 9) : ℝ := rawLoad (FlashRootNetwork.rawOfRing j)

theorem sourceLoad_pos (j : Fin 9) : 0<sourceLoad j := rawLoad_pos _

theorem siteMap_rawOfRing (j : Fin 9) : siteMap (FlashRootNetwork.rawOfRing j)=j := by
  fin_cases j <;> decide

/-- Actual all9 canonical strictly outward radial flux; no hflux premise. -/
theorem canonical_flux_radial (j : Fin 9) :
    flux canonicalStress sourceAnchors sourceCenters sourceAux j=
      sourceLoad j • sourceAnchors j := by
  have h := canonical_flux_raw (FlashRootNetwork.rawOfRing j)
  rw [siteMap_rawOfRing] at h
  exact h

theorem harmonic_flux_radial (j : Fin 9) :
    flux canonicalStress sourceAnchors
      (fun i => ResumeHarmonic.lift sourceH sourceAnchors (.inl i))
      (fun f => ResumeHarmonic.lift sourceH sourceAnchors (.inr f)) j=
      sourceLoad j • sourceAnchors j :=
  (sourceH_flux_reproduces j).trans (canonical_flux_radial j)

end
end N11Formalization.SourceRadialFluxConsumer
#check @N11Formalization.SourceRadialFluxConsumer.canonical_flux_radial
#check @N11Formalization.SourceRadialFluxConsumer.harmonic_flux_radial
#check @N11Formalization.SourceRadialFluxConsumer.sourceLoad_pos
#print axioms N11Formalization.SourceRadialFluxConsumer.canonical_flux_radial
#print axioms N11Formalization.SourceRadialFluxConsumer.harmonic_flux_radial
