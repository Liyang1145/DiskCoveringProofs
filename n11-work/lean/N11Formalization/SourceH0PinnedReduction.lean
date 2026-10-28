import N11Formalization.SourceResponseKernelConsumer
import N11Formalization.ResumePinnedCoercivity

/-! Exact pinned reduction for the ACTUAL H0 quadratic form. This is only an
algebraic quotient/pin identity; it does not claim any numerical coercivity.
It is the consumer shape required by a future 8x8 interval certificate. -/
set_option autoImplicit false
namespace N11Formalization.SourceH0PinnedReduction
open N11Formalization SourceResponseKernelConsumer
noncomputable section

theorem quadratic_pin_reduce (p : Fin 9) (x : Fin 9 → ℝ) (hp : x p=0) :
    (∑ i : Fin 9, ∑ j : Fin 9,H0 i j*x i*x j)=
      ∑ i : Fin 8, ∑ j : Fin 8,
        H0 (p.succAbove i) (p.succAbove j)*
          x (p.succAbove i)*x (p.succAbove j) :=
  ResumePinnedCoercivity.quadratic_delete_pin p H0 x hp

theorem constant_kernel_pin (p : Fin 9) :
    (fun i : Fin 9 => (1 : ℝ)) p=1 := by simp

theorem H0_row_sum_pin (p : Fin 9) (i : Fin 8) :
    ∑ j : Fin 8,H0 (p.succAbove i) (p.succAbove j)=
      -H0 (p.succAbove i) p := by
  have h := H0_rowsum (p.succAbove i)
  rw [Fin.sum_univ_succAbove _ p] at h
  linarith

end
end N11Formalization.SourceH0PinnedReduction
#check @N11Formalization.SourceH0PinnedReduction.quadratic_pin_reduce
#check @N11Formalization.SourceH0PinnedReduction.H0_row_sum_pin
#print axioms N11Formalization.SourceH0PinnedReduction.quadratic_pin_reduce
