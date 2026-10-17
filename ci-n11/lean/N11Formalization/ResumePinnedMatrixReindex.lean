import N11Formalization.ResumePinnedReindex
import N11Formalization.ResumeIntervalMatrix

namespace N11Formalization.ResumePinnedMatrixReindex
open Matrix Finset ResumeLocalIncidence

/-- Canonical6 deletion to raw8 deletion: [2,3,4,5,6,7,0,1]. -/
def pinEquiv : Fin 8 ≃ Fin 8 where
  toFun := fun i => i+2
  invFun := fun i => i+6
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

theorem pin_equiv_actual (i : Fin 8) :
    canonRawEquiv ((6 : Fin 9).succAbove i) = (8 : Fin 9).succAbove (pinEquiv i) := by
  fin_cases i <;> decide

/-- Reindex both indices of M and only the rows of C. Certificate column
coordinates are intentionally unchanged: no silent extra permutation of Q. -/
theorem congruence_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ ι) (M : Matrix ι ι ℝ) (C : Matrix ι κ ℝ) :
    (fun i a => C (e i) a)ᵀ * (show Matrix ι ι ℝ from fun i j => M (e i) (e j)) * (show Matrix ι κ ℝ from fun i a => C (e i) a)
      = Cᵀ * M * C := by
  ext a b
  change (∑ j, (∑ i, C (e i) a * M (e i) (e j)) * C (e j) b) =
    ∑ j, (∑ i, C i a * M i j) * C j b
  have he (j : ι) : (∑ i, C (e i) a * M (e i) (e j)) = ∑ i, C i a * M i (e j) :=
    Equiv.sum_comp e (fun i => C i a * M i (e j))
  simp_rw [he]
  exact Equiv.sum_comp e (fun j => (∑ i, C i a * M i j) * C j b)

#print axioms pin_equiv_actual
#print axioms congruence_reindex
end N11Formalization.ResumePinnedMatrixReindex
