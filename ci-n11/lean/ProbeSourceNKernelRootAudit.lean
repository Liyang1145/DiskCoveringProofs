import N11Formalization
set_option autoImplicit false
open N11Formalization
open SourceB41ActualContraction SourceNormalizedKernel
open SourceNormalizedCanonical
open SourceAdaptiveBalanceInputs

#check @SourceB41ActualContraction.actual_matrix_bounds
#check @SourceB41ActualContraction.actual_residual_rows
#check @SourceB41ActualContraction.actual_contraction
#check @SourceB41ActualContraction.M_mulVec_injective
#check @SourceB41ActualContraction.M_det_ne_zero
#check @SourceNormalizedKernel.all_B_rows
#check @SourceNormalizedKernel.column_sum_zero
#check @SourceNormalizedKernel.coefficients_zero
#check @SourceNormalizedKernel.kernel_representation
#check @SourceNormalizedCanonical.Ncanon_edgeMap
#check @SourceNormalizedCanonical.source_vector_balance
#check @SourceNormalizedCanonical.canonical_free_balance
#check @SourceAdaptiveBalanceInputs.adaptive_hNcol
#check @SourceAdaptiveBalanceInputs.adaptive_hNbal

#print SourceB41ActualContraction.M
#print SourceNormalizedKernel.N
#print axioms SourceB41ActualContraction.actual_contraction
#print axioms SourceB41ActualContraction.M_det_ne_zero
#print axioms SourceNormalizedKernel.all_B_rows
#print axioms SourceNormalizedKernel.kernel_representation
#print axioms SourceNormalizedCanonical.canonical_free_balance
#print axioms SourceAdaptiveBalanceInputs.adaptive_hNcol
#print axioms SourceAdaptiveBalanceInputs.adaptive_hNbal

example (i j : Fin 41) :
    (SourceB41Proposal.ML i j : ℝ) / 100000 ≤
      SourceB41ActualContraction.M i j ∧
      SourceB41ActualContraction.M i j ≤
        (SourceB41Proposal.MH i j : ℝ) / 100000 :=
  SourceB41ActualContraction.actual_matrix_bounds i j

example (a : Fin 4) (i : Fin 41) :
    ∑ e : Fin 45,
      SourceN2.srcB2 SourceExactRoot.sourceRoot i e *
        SourceNormalizedKernel.N e a = 0 :=
  SourceNormalizedKernel.all_B_rows i a

example (a : Fin 4) :
    ∑ e : Fin 45, SourceNormalizedKernel.N e a = 0 :=
  SourceNormalizedKernel.column_sum_zero a

example (v : Fin 45 → ℝ)
    (hv : ∀ i : Fin 41, ∑ e : Fin 45,
      SourceN2.srcB2 SourceExactRoot.sourceRoot i e * v e = 0) :
    v = SourceNormalizedKernel.combine
      (fun b : Fin 4 => v (SourceB41Proposal.freeCol b)) :=
  SourceNormalizedKernel.kernel_representation v hv

example (a : Fin 4) (v : ResumeDirichlet.Free) :
    ∑ e : ResumeNetwork.Edge,
      (SourceNormalizedCanonical.NcanonCol a e * ResumeDirichlet.incidence e v) •
        ResumeDirichlet.edgeVector
          (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
          (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
          (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e = 0 :=
  SourceNormalizedCanonical.canonical_free_balance a v

example (a : Fin 4) : ∑ e : ResumeNetwork.Edge,
    SourceNormalizedCanonical.NcanonCol a e = 0 :=
  SourceAdaptiveBalanceInputs.adaptive_hNcol a

example (a : Fin 4) (v : ResumeDirichlet.Free) :
    ∑ e : ResumeNetwork.Edge,
      (SourceNormalizedCanonical.NcanonCol a e * ResumeDirichlet.incidence e v) •
        ResumeDirichlet.edgeVector
          (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
          (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
          (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e = 0 :=
  SourceAdaptiveBalanceInputs.adaptive_hNbal a v

#check @SourceExactRoot.source_attainment
#check @SourceExactRoot.main_of_lower_bound
