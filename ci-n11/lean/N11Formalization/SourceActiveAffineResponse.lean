import N11Formalization.SourceActiveHarmonicSolve

/-! Actual source harmonic affine rows and the resulting response zero row
sums. The proof uses the nonsingular ACTUAL20-node matrix, not an assumed
normalization of the22-node H. Two slack auxiliaries may have arbitrary rows;
their zero weights do not affect response. Supplies the actual36-pair cosine
energy representation and oracle consumer without any hH row-sum premise. -/
set_option autoImplicit false
namespace N11Formalization.SourceActiveAffineResponse
open N11Formalization ResumeNetwork ResumeDirichlet ResumeHarmonic ResumeAnchorFlux
open ResumeLocalIncidence HarmonicSourceTransport SourceCentreB2Readout
open SourcePositiveHarmonicConsumer SourceResponseFluxIdentity
open SourceActiveLaplacian SourceActiveHarmonicSolve
noncomputable section

theorem uniform_edge_identity (e : SourceEdge) :
    (∑ j : Fin 9,anchorRow e j)+(∑ v : SrcFree,B e v)=0 := by
  have hg : (∑ v : SrcFree,B e v)=SourceActiveLaplacian.gradient (fun _ => 1) e := by
    simp only [SourceActiveLaplacian.gradient,mul_one]
  rw [hg]
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · rw [gradient_spoke]
    fin_cases s <;> simp [anchorRow,edgeMap,ResumeAnchorFlux.anchorIncidence]
  · rw [gradient_face]
    simp [anchorRow,edgeMap,ResumeAnchorFlux.anchorIncidence]

def rowDefect (v : SrcFree) : ℝ := (∑ j : Fin 9,activeH v j)-1

theorem defect_gradient (e : SourceEdge) :
    SourceActiveLaplacian.gradient rowDefect e=∑ j : Fin 9,K e j := by
  have hc := uniform_edge_identity e
  unfold SourceActiveLaplacian.gradient rowDefect K LaplacianSchurBridge.edgeCoeff
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  linarith

theorem rowDefect_zero : rowDefect=0 := by
  apply A_kernel_zero
  funext v
  rw [A_mulVec]
  simp_rw [defect_gradient,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [active_balance,Finset.sum_const_zero,Pi.zero_apply]

/-- Actual harmonic row sums on ALL20 active nodes. No22-row hH premise. -/
theorem activeH_affine (v : SrcFree) : ∑ j : Fin 9,activeH v j=1 := by
  have h := congrFun rowDefect_zero v
  change (∑ j : Fin 9,activeH v j)-1=0 at h
  linarith

theorem K_sum_zero (e : SourceEdge) : ∑ j : Fin 9,K e j=0 := by
  rw [← defect_gradient,rowDefect_zero]
  simp [SourceActiveLaplacian.gradient]

/-- The actual sourceResponse is independent of the arbitrary slack rows. -/
theorem response_active (i j : Fin 9) :
    sourceResponse i j=
      ∑ e : SourceEdge,SourceSignedStressAssembly.stress e*K e i*K e j := by
  unfold sourceResponse ResumeResponseGram.response
  have hr := sum_edge_eq_sum_sourceEdge
    (α := canonicalStress) (F := fun e => coeff sourceH e i*coeff sourceH e j)
    (zero_off_image_of_slack canonical_slack_zero)
  calc
    _ = ∑ e : Edge,canonicalStress e*(coeff sourceH e i*coeff sourceH e j) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by
      rw [hr]
      simp only [canonicalStress,SourceAlphaOf.alphaEdge_edgeMap,coeff_active]
      apply Finset.sum_congr rfl
      intro e _
      ring

theorem response_rows_zero (i : Fin 9) : ∑ j : Fin 9,sourceResponse i j=0 := by
  simp_rw [response_active]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,K_sum_zero,mul_zero]
  exact Finset.sum_const_zero

theorem actual_pair_energy (θ : Fin 9 → ℝ) :
    FlashLocal.Eform sourceResponse (fun j => circleMap (θ j)) (fun j => circleMap (θ j))=
      2*∑ i : Fin 9,∑ j : Fin 9,if i<j then
        -sourceResponse i j*(1-Real.cos (θ i-θ j)) else 0 := by
  have he :
      FlashLocal.Eform sourceResponse (fun j => circleMap (θ j)) (fun j => circleMap (θ j))=
        ∑ i : Fin 9,∑ j : Fin 9,-sourceResponse i j*(1-Real.cos (θ i-θ j)) := by
    unfold FlashLocal.Eform
    simp_rw [inner_circleMap]
    apply Finset.sum_congr rfl
    intro i _
    have hrow := response_rows_zero i
    calc
      _ = (∑ j : Fin 9,sourceResponse i j*Real.cos (θ i-θ j))-
          ∑ j : Fin 9,sourceResponse i j := by rw [hrow]; ring
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [he]
  apply ResumeSchurEnergy.sum_symmetric_pairs
  · intro i j
    have hs : sourceResponse i j=sourceResponse j i :=
      ResumeResponseProperties.response_symm canonicalStress (coeff sourceH) i j
    rw [hs]
    have hc : Real.cos (θ i-θ j)=Real.cos (θ j-θ i) := by
      rw [← Real.cos_neg (θ j-θ i)]
      congr 1
      ring
    rw [hc]
  · intro i
    simp

/-- Actual36-pair cosine functional bounds V2 for EVERY angular tuple.
No row-sum, stress normalization or harmonic-balance assumption remains. -/
theorem actual_pair_le_oracle (θ : Fin 9 → ℝ) :
    (2*∑ i : Fin 9,∑ j : Fin 9,if i<j then
      -sourceResponse i j*(1-Real.cos (θ i-θ j)) else 0)≤
        V2 (fun j => circleMap (θ j)) := by
  rw [← actual_pair_energy]
  change FlashLocal.Eform (ResumeResponseGram.response canonicalStress (coeff sourceH))
    (fun j => circleMap (θ j)) (fun j => circleMap (θ j))≤_
  rw [source_response_identity]
  have h := source_harmonic_le_oracle (fun j => circleMap (θ j))
    (fun j => (circleMap_norm (θ j)).le)
  rw [← ResumeResponseGram.gram_energy,source_response_identity] at h
  exact h

end
end N11Formalization.SourceActiveAffineResponse
#check @N11Formalization.SourceActiveAffineResponse.activeH_affine
#check @N11Formalization.SourceActiveAffineResponse.response_rows_zero
#check @N11Formalization.SourceActiveAffineResponse.actual_pair_le_oracle
#print axioms N11Formalization.SourceActiveAffineResponse.activeH_affine
#print axioms N11Formalization.SourceActiveAffineResponse.actual_pair_le_oracle
