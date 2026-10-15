import Mathlib

/-!
# ResumeGlobal: C921 hsem layer (d) — the LP/weak-duality step, generic.
DRAFT, NOT COMPILED (lead forbade lake/lean; queue for serial check).
Discharges layer (d) of `C921Sem.LeafSemBound`'s docstring: for λ ≥ 0, A y ≤ b,
y in the closed simplex, with reduced costs r_q = c_q + (Aᵀλ)_q,
  f0 + c·y ≥ f0 − λᵀb + min_q r_q.
No data, no symmetry, no leaf-specific arithmetic: universally quantified.
-/

namespace N11Formalization.ResumeGlobal

open Finset

/-- LP step with an explicit lower bound `rmin ≤ r_q` for all q (so `min` need not be
computed). Hypotheses: λ ≥ 0, rows `∑ A j q * y q ≤ b j`, `y ≥ 0`, `∑ y = 1`. -/
theorem lp_step {m : ℕ} (f0 : ℝ) (c : Fin 8 → ℝ) (A : Fin m → Fin 8 → ℝ) (b : Fin m → ℝ)
    (lam : Fin m → ℝ) (rmin : ℝ) (y : Fin 8 → ℝ)
    (hlam : ∀ j, 0 ≤ lam j)
    (hrow : ∀ j, ∑ q, A j q * y q ≤ b j)
    (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hr : ∀ q, rmin ≤ c q + ∑ j, lam j * A j q) :
    f0 - ∑ j, lam j * b j + rmin ≤ f0 + ∑ q, c q * y q := by
  -- λᵀ(Ay) ≤ λᵀb
  have h1 : ∑ j, lam j * (∑ q, A j q * y q) ≤ ∑ j, lam j * b j :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hrow j) (hlam j)
  -- rmin = ∑ rmin*y ≤ ∑ r_q y_q
  have h2 : rmin ≤ ∑ q, (c q + ∑ j, lam j * A j q) * y q := by
    calc rmin = ∑ q, rmin * y q := by rw [← Finset.mul_sum, hy1, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hr q) (hy0 q)
  -- swap sums
  have h3 : ∑ q, (c q + ∑ j, lam j * A j q) * y q
      = ∑ q, c q * y q + ∑ j, lam j * (∑ q, A j q * y q) := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring
  linarith

end N11Formalization.ResumeGlobal
