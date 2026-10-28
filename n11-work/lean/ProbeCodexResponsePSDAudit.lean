import N11Formalization
open N11Formalization
open SourceResponsePSDConsumer SourceResponseFluxIdentity
open SourceBoundaryStressPositive SourcePositiveHarmonicConsumer
open ResumeNetwork ResumeDirichlet ResumeHarmonic

#check @SourceResponsePSDConsumer.Λ_symm
#check @SourceResponsePSDConsumer.Λ_psd
#check @SourceResponsePSDConsumer.Λ_energy_eq_source
#check @SourceResponsePSDConsumer.H0_symm
#print axioms SourceResponsePSDConsumer.Λ_psd
#print axioms SourceResponsePSDConsumer.Λ_energy_eq_source
#print axioms SourceResponsePSDConsumer.H0_symm

example (W : Fin 9 → Point) : 0 ≤ FlashLocal.Eform Λ W W :=
  Λ_psd W

example (i j : Fin 9) : Λ i j = Λ j i := Λ_symm i j
