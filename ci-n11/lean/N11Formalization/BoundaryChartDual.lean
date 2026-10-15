import Mathlib
import N11Formalization.BoundaryChartLinear
set_option autoImplicit false
namespace N11Formalization.BoundaryChartDual
open N11Formalization.BoundaryChartLinear
noncomputable section

def multiplier (a : Fin 12 → ℝ) : Fin 5 → ℝ :=
  ![a 6 + a 7 + a 8 - a 4, a 7 + a 8 - a 4,
    a 8 - a 4, -a 4, (a 5 + a 6 + a 7 + a 8 - a 4) / 2]

/-- Exact annihilator factorization on the width/direction chart, NOT yet physical KKT. -/
theorem factor_through_boundary (a : Fin 12 → ℝ)
    (hchart : ∀ z : Fin 7 → ℝ, ∑ i, a i * chart z i = 0) :
    ∀ x : Fin 12 → ℝ, ∑ i, a i * x i = ∑ j, multiplier a j * boundary x j := by
  have h0 := hchart (Pi.single 0 1)
  have h1 := hchart (Pi.single 1 1)
  have h2 := hchart (Pi.single 2 1)
  have h3 := hchart (Pi.single 3 1)
  have h4 := hchart (Pi.single 4 1)
  have h5 := hchart (Pi.single 5 1)
  have h6 := hchart (Pi.single 6 1)
  simp [chart, Fin.sum_univ_succ, Pi.single_apply, Fin.reduceFinMk] at h0 h1 h2 h3 h4 h5 h6
  have ha0 : a 0 = 2 * a 4 - a 5 - 2 * a 6 - 2 * a 7 - 2 * a 8 := by linarith
  have ha1 : a 1 = 2 * a 4 - a 6 - 2 * a 7 - 2 * a 8 := by linarith
  have ha2 : a 2 = 2 * a 4 - a 7 - 2 * a 8 := by linarith
  have ha3 : a 3 = 2 * a 4 - a 8 := by linarith
  have ha9 : a 9 = 0 := by linarith
  have ha10 : a 10 = 0 := by linarith
  have ha11 : a 11 = 0 := by linarith
  intro x
  simp [Fin.sum_univ_succ, multiplier, boundary, Fin.reduceFinMk]
  rw [ha0, ha1, ha2, ha3, ha9, ha10, ha11]
  ring

theorem multiplier_unique (a : Fin 12 → ℝ) (lam : Fin 5 → ℝ)
    (h : ∀ x : Fin 12 → ℝ, ∑ i, a i * x i = ∑ j, lam j * boundary x j)
    (hchart : ∀ z : Fin 7 → ℝ, ∑ i, a i * chart z i = 0) :
    lam = multiplier a := by
  funext j
  have h1 := h (rightInverse (Pi.single j 1))
  have h2 := factor_through_boundary a hchart (rightInverse (Pi.single j 1))
  rw [boundary_rightInverse] at h1 h2
  have h3 : (∑ k : Fin 5, lam k * (Pi.single j (1 : ℝ) : Fin 5 → ℝ) k) = (∑ k : Fin 5, multiplier a k * (Pi.single j (1 : ℝ) : Fin 5 → ℝ) k) :=
    h1.symm.trans h2
  simpa [Pi.single_apply] using h3

end
end N11Formalization.BoundaryChartDual
#print axioms N11Formalization.BoundaryChartDual.factor_through_boundary
#print axioms N11Formalization.BoundaryChartDual.multiplier_unique
#check @N11Formalization.BoundaryChartDual.factor_through_boundary


