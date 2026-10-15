import N11Formalization.ResumeCoercivityCertificate
import N11Formalization.FlashLocalDirectionalActual

noncomputable section
namespace N11Formalization.ResumePinnedCoercivity
open Finset Matrix ResumeCoercivityCertificate
open FlashLocal ResumeNetwork ResumeAdaptiveRoot

theorem sum_delete_pin {n : ℕ} (p : Fin (n+1)) (f : Fin (n+1) → ℝ)
    (hp : f p = 0) : (∑ i, f i) = ∑ i : Fin n, f (p.succAbove i) := by
  rw [Fin.sum_univ_succAbove _ p, hp, zero_add]

theorem quadratic_delete_pin {n : ℕ} (p : Fin (n+1))
    (H : Fin (n+1) → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) (hp : x p = 0) :
    (∑ i, ∑ j, H i j*x i*x j) =
      ∑ i : Fin n, ∑ j : Fin n, H (p.succAbove i) (p.succAbove j)*x (p.succAbove i)*x (p.succAbove j) := by
  rw [sum_delete_pin p _ (by simp [hp])]
  apply Finset.sum_congr rfl
  intro i _
  exact sum_delete_pin p _ (by simp [hp])

/-- Restrict only the zero-pinned coordinate. Both H and G refer to the same
full vector; canonical p=6 and raw p=8 are legal, but not silently identified. -/
theorem pinned_coercivity {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin (n+1)) (H : Fin (n+1) → Fin (n+1) → ℝ)
    (G : Fin (n+1) → κ → ℝ) (t μ η : ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hη : 0 < η)
    (hs : ∀ i j, (C.transpose * augmented
      (fun i j => H (p.succAbove i) (p.succAbove j))
      (fun i a => G (p.succAbove i) a) t μ * C) i j =
      (C.transpose * augmented
      (fun i j => H (p.succAbove i) (p.succAbove j))
      (fun i a => G (p.succAbove i) a) t μ * C) j i)
    (hd : ∀ i, η + (∑ j, |(C.transpose * augmented
      (fun i j => H (p.succAbove i) (p.succAbove j))
      (fun i a => G (p.succAbove i) a) t μ * C) i j|) ≤
      (C.transpose * augmented
      (fun i j => H (p.succAbove i) (p.succAbove j))
      (fun i a => G (p.succAbove i) a) t μ * C) i i +
      |(C.transpose * augmented
      (fun i j => H (p.succAbove i) (p.succAbove j))
      (fun i a => G (p.succAbove i) a) t μ * C) i i|)
    (x : Fin (n+1) → ℝ) (hp : x p = 0) :
    μ*(∑ i, x i^2) ≤ (∑ i, ∑ j, H i j*x i*x j) +
      2*t*(∑ a, (∑ i, G i a*x i)^2) := by
  rw [sum_delete_pin p (fun i => x i^2) (by simp [hp]), quadratic_delete_pin p H x hp]
  have he : (∑ a, (∑ i, G i a*x i)^2) =
      ∑ a, (∑ i : Fin n, G (p.succAbove i) a*x (p.succAbove i))^2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [sum_delete_pin p (fun i => G i a*x i) (by simp [hp])]
  rw [he]
  exact coercivity _ _ t μ η C hη hs hd (fun i => x (p.succAbove i))

#print axioms pinned_coercivity
end N11Formalization.ResumePinnedCoercivity
