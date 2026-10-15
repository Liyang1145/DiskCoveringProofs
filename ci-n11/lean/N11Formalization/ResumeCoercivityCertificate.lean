import N11Formalization.ResumeQuadraticCertificate
import N11Formalization.ResumeRelativeScalar

noncomputable section
namespace N11Formalization.ResumeCoercivityCertificate
open Finset Matrix ResumeQuadraticCertificate

def augmented {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (H : ι → ι → ℝ) (G : ι → κ → ℝ) (t μ : ℝ) : Matrix ι ι ℝ := fun i j =>
  H i j + 2*t*(∑ a, G i a*G j a) - if i=j then μ else 0

theorem gram_expansion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : ι → κ → ℝ) (x : ι → ℝ) :
    (∑ i, ∑ j, (∑ a, G i a*G j a)*x i*x j) =
      ∑ a, (∑ i, G i a*x i)^2 := by
  simp only [Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem augmented_expansion {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (H : ι → ι → ℝ) (G : ι → κ → ℝ) (t μ : ℝ) (x : ι → ℝ) :
    (∑ i, ∑ j, augmented H G t μ i j*x i*x j) =
      (∑ i, ∑ j, H i j*x i*x j) + 2*t*(∑ a, (∑ i, G i a*x i)^2)
        - μ*(∑ i, x i^2) := by
  have hg := gram_expansion G x
  unfold augmented
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hdiag : (∑ i, ∑ j, (if i=j then μ else 0)*x i*x j) = μ*∑ i, x i^2 := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiag]
  have hscale : (∑ i, ∑ j, 2*t*(∑ a, G i a*G j a)*x i*x j) =
      2*t*(∑ i, ∑ j, (∑ a, G i a*G j a)*x i*x j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hscale, hg]

/-- The actual finite certificate shape used by certify_relative_stress_ball.py.
Strict congruence dominance discharges coercivity; no inverse premise remains. -/
theorem coercivity {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (H : ι → ι → ℝ) (G : ι → κ → ℝ) (t μ η : ℝ)
    (C : Matrix ι ι ℝ) (hη : 0 < η)
    (hs : ∀ i j, (C.transpose * augmented H G t μ * C) i j =
      (C.transpose * augmented H G t μ * C) j i)
    (hd : ∀ i, η + (∑ j, |(C.transpose * augmented H G t μ * C) i j|) ≤
      (C.transpose * augmented H G t μ * C) i i +
      |(C.transpose * augmented H G t μ * C) i i|) (x : ι → ℝ) :
    μ*(∑ i, x i^2) ≤ (∑ i, ∑ j, H i j*x i*x j) +
      2*t*(∑ a, (∑ i, G i a*x i)^2) := by
  have h := strict_preconditioned_nonneg (augmented H G t μ) C η hη hs hd x
  rw [augmented_expansion] at h
  linarith

/-- Actual C920 scalar consumer: coercivity with t0=734 upgrades the
already derived directional inequality to a positive gain on the closed ball.
H and p must be the quantities from that same directional instance. -/
theorem directional_to_local_gain (E H q p : ℝ) (hq : 0 ≤ q) (hr : q ≤ 729/50000)
    (hc : (9/5000 : ℝ)*q^2 ≤ H + 1468*p^2)
    (hdir : H/2 + 1468*p^2 - (179/5000)*q^3 - ((2/25)/3)*q^4
      - 1468*((99/200)*(2/25)+429/50000)*p*q^2 ≤ E) :
    q^2/100000 ≤ E := by
  apply ResumeRelativeScalar.local_gain (p := p) hq hr
  linarith

#print axioms directional_to_local_gain
#print axioms coercivity
end N11Formalization.ResumeCoercivityCertificate
