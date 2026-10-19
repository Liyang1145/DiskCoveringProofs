import N11Formalization
open N11Formalization
open SourceSchurResponseBinding SourceHarmonicUniqueness
open SourcePositiveHarmonicConsumer SourceCentreB2Readout
open ResumeNetwork ResumeDirichlet ResumeHarmonic ResumeAnchorFlux

#check @SourceSchurResponseBinding.source_balanced
#check @SourceSchurResponseBinding.sourceY_solve
#check @SourceSchurResponseBinding.schur_eq_response
#check @SourceSchurResponseBinding.schur_eq_sourceResponse
#print axioms SourceSchurResponseBinding.sourceY_solve
#print axioms SourceSchurResponseBinding.schur_eq_response

example (i j : Fin 9) :
    LaplacianSchurBridge.anchorBlock canonicalStress ResumeAnchorFlux.anchorIncidence i j -
      ∑ v : Free,
        LaplacianSchurBridge.crossBlock canonicalStress ResumeDirichlet.incidence
          ResumeAnchorFlux.anchorIncidence v i *
          SourceSchurResponseBinding.sourceY v j =
      SourceResponseFluxIdentity.sourceResponse i j :=
  SourceSchurResponseBinding.schur_eq_sourceResponse i j
