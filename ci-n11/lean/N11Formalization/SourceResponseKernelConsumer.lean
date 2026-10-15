import N11Formalization.SourceResponsePSDConsumer

/-! Exact kernel-side consumers for the actual tangent H0 matrix. The constant
boundary direction is a genuine zero mode, so later coercivity must be pinned
to the quotient/congruence subspace; this module does not claim strict
coercivity. -/
set_option autoImplicit false
namespace N11Formalization.SourceResponseKernelConsumer
open N11Formalization SourceResponsePSDConsumer SourceResponseFluxIdentity
open SourceRadialFluxConsumer
noncomputable section

def H0 : Fin 9 → Fin 9 → ℝ :=
  FlashLocal.H0mat Λ sourceLoad
    (fun i => FlashLocal.circleTangent (sourceAngle i))

theorem H0_eq_hsrc (i j : Fin 9) :
    H0 i j=
      FlashResponseHessian.hsrc Λ
        (fun i => FlashLocal.circleTangent (sourceAngle i)) i j := by
  unfold H0
  change FlashLocal.H0mat SourceResponseFluxIdentity.sourceResponse sourceLoad
    (fun i => FlashLocal.circleTangent (sourceAngle i)) i j =
      FlashResponseHessian.hsrc SourceResponseFluxIdentity.sourceResponse
        (fun i => FlashLocal.circleTangent (sourceAngle i)) i j
  rw [← SourceResponseFluxIdentity.actual_hsrc_eq_H0mat]

theorem H0_rowsum (i : Fin 9) : ∑ j : Fin 9,H0 i j=0 := by
  simp_rw [H0_eq_hsrc]
  exact FlashResponseHessian.hsrc_rowsum Λ
    (fun i => FlashLocal.circleTangent (sourceAngle i)) i

theorem H0_constant_kernel (i : Fin 9) :
    ∑ j : Fin 9,H0 i j*(1 : ℝ)=0 := by
  simp only [mul_one]
  exact H0_rowsum i

theorem H0_symmetric (i j : Fin 9) : H0 i j=H0 j i := by
  unfold H0
  exact SourceResponsePSDConsumer.H0_symm i j

end
end N11Formalization.SourceResponseKernelConsumer
#check @N11Formalization.SourceResponseKernelConsumer.H0_rowsum
#check @N11Formalization.SourceResponseKernelConsumer.H0_constant_kernel
#print axioms N11Formalization.SourceResponseKernelConsumer.H0_rowsum
