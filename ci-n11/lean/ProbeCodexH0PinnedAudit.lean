import N11Formalization
open N11Formalization SourceH0PinnedReduction SourceResponseKernelConsumer

#check @SourceH0PinnedReduction.quadratic_pin_reduce
#check @SourceH0PinnedReduction.H0_row_sum_pin
#print axioms SourceH0PinnedReduction.quadratic_pin_reduce
#print axioms SourceH0PinnedReduction.H0_row_sum_pin

example (p : Fin 9) (x : Fin 9 → ℝ) (hp : x p=0) :
    (∑ i : Fin 9, ∑ j : Fin 9,H0 i j*x i*x j)=
      ∑ i : Fin 8, ∑ j : Fin 8,
        H0 (p.succAbove i) (p.succAbove j)*
          x (p.succAbove i)*x (p.succAbove j) :=
  quadratic_pin_reduce p x hp
