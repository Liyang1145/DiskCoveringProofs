import N11Formalization.SourceFineCompactStressIntervals
import N11Formalization.SourceResponsePSDConsumer
import N11Formalization.ResumeResponseBound
import N11Formalization.SourceRadialFluxConsumer

/-! Actual canonical anchorWeight<=2/25 and full bilinear response bound.
Exact source two-spoke bound is transported with all51 incidence and zero
slack weights; no source/H/PSD/diagonal premise is supplied. -/
set_option autoImplicit false
namespace N11Formalization.SourceActualResponseBound
open N11Formalization ResumeNetwork ResumeAnchorFlux ResumeStressComparison
open ResumeLocalIncidence SourceCentreB2Readout SourceResponsePSDConsumer
noncomputable section

private theorem anchorWeight_as_sum (α : Edge → ℝ) (j : Fin 9) :
    anchorWeight α j=∑ e : Edge,-α e*anchorIncidence e j := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,anchorIncidence]
  have hf : (∑ f : Fin 11,∑ t : Fin 3,-α (.inr (f,t))*0)=0 := by simp
  rw [hf,add_zero]
  unfold anchorWeight
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> ring

theorem anchorWeight_two_spokes (k : Fin 9) :
    anchorWeight canonicalStress (siteMap k)=
      ∑ s : Fin 2,SourceSignedStressAssembly.stress (.inl (k,s)) := by
  rw [anchorWeight_as_sum,ResumeLocalIncidence.sum_reindex _ (fun f t hf => by
    rcases hf with rfl | rfl
    · simp only [(canonical_slack_zero t).1,neg_zero,zero_mul]
    · simp only [(canonical_slack_zero t).2,neg_zero,zero_mul])]
  rw [Fintype.sum_sum_type]
  have hf (p : Fin 9 × Fin 3) :
      anchorIncidence (edgeMap (.inr p)) (siteMap k)=0 := rfl
  simp only [hf,mul_zero,Finset.sum_const_zero,add_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [SourceRadialFluxConsumer.incidence_source_spoke,
    canonicalStress,SourceAlphaOf.alphaEdge_edgeMap]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true,neg_mul_neg, mul_one]
  · intro l _ hl
    simp only [if_neg hl,mul_zero,Finset.sum_const_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- Actual51-edge canonical boundary diagonal, no endpoint/mapping premise. -/
theorem actual_anchorWeight (j : Fin 9) : anchorWeight canonicalStress j≤(2 : ℝ)/25 := by
  have h := SourceFineCompactStressIntervals.actual_anchor_diagonal (FlashRootNetwork.rawOfRing j)
  rw [← SourceRadialFluxConsumer.siteMap_rawOfRing j,anchorWeight_two_spokes]
  simpa only [Fin.sum_univ_two] using h

/-- All mixed directions of the actual response (not just a block/diagonal). -/
theorem actual_response_bound (U W : Fin 9 → Point) :
    |FlashLocal.Eform Λ U W|≤(2/25 : ℝ)*FlashLocal.frob U*FlashLocal.frob W :=
  ResumeResponseBound.network_response_bound canonicalStress Λ (2/25) (by norm_num)
    SourceBoundaryStressPositive.canonical_nonneg Λ_symm Λ_psd Λ_energy_eq_source
    actual_anchorWeight U W

end
end N11Formalization.SourceActualResponseBound
#check @N11Formalization.SourceActualResponseBound.anchorWeight_two_spokes
#check @N11Formalization.SourceActualResponseBound.actual_anchorWeight
#check @N11Formalization.SourceActualResponseBound.actual_response_bound
#print axioms N11Formalization.SourceActualResponseBound.actual_response_bound
