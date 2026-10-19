import N11Formalization
open N11Formalization
open SourceResponseKernelConsumer SourceResponsePSDConsumer
open SourceResponseFluxIdentity SourceRadialFluxConsumer

#check @SourceResponseKernelConsumer.H0_eq_hsrc
#check @SourceResponseKernelConsumer.H0_rowsum
#check @SourceResponseKernelConsumer.H0_constant_kernel
#check @SourceResponseKernelConsumer.H0_symmetric
#print axioms SourceResponseKernelConsumer.H0_rowsum
#print axioms SourceResponseKernelConsumer.H0_constant_kernel
#print axioms SourceResponseKernelConsumer.H0_symmetric

example (i : Fin 9) : ∑ j : Fin 9,H0 i j=0 := H0_rowsum i
example (i : Fin 9) : ∑ j : Fin 9,H0 i j*(1 : ℝ)=0 :=
  H0_constant_kernel i
