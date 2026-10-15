import Mathlib

noncomputable section
namespace N11Formalization.ResumeQuadraticCertificate
open Finset

/-- Scalar kernel behind a symmetric diagonally dominant certificate. -/
theorem pair_lower (a x y : ℝ) : -(abs a * (x^2+y^2) / 2) ≤ a*x*y := by
  have h := neg_abs_le (a*x*y)
  rw [abs_mul, abs_mul] at h
  have hxy : 2 * |x| * |y| ≤ x^2+y^2 := by
    nlinarith [sq_nonneg (|x|-|y|), sq_abs x, sq_abs y]
  have hm := mul_le_mul_of_nonneg_left hxy (abs_nonneg a)
  nlinarith

/-- Finite exact Gershgorin quadratic lower bound; applies to every vector,
not just separately tested coordinate blocks or sampled directions. -/
theorem quadratic_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (μ : ℝ) (hs : ∀ i j, M i j = M j i)
    (hd : ∀ i, μ + ∑ j, |M i j| ≤ M i i + |M i i|) (x : ι → ℝ) :
    μ * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, M i j * x i * x j := by
  have hpair : ∀ i j, (if i=j then (M i i+|M i i|)*x i^2 else 0)
      - |M i j| *(x i^2+x j^2)/2 ≤ M i j*x i*x j := by
    intro i j
    by_cases hij : i=j
    · subst j
      simp only [ite_true]
      nlinarith
    · simp only [hij, ite_false, zero_sub]
      exact pair_lower _ _ _
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpair i j))
  have hswap : (∑ i, ∑ j, |M i j| * x j^2) = ∑ i, ∑ j, |M i j| * x i^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  have hrow : (∑ i, ∑ j, |M i j| * x i^2) = ∑ i, (∑ j, |M i j|)*x i^2 := by
    simp only [Finset.sum_mul]
  have he : (∑ i, ∑ j, ((if i=j then (M i i+|M i i|)*x i^2 else 0)
      - |M i j| *(x i^2+x j^2)/2)) =
      ∑ i, (M i i + |M i i| - ∑ j, |M i j|) * x i^2 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      mul_add, add_div, Finset.sum_add_distrib]
    simp only [← Finset.sum_div]
    rw [hswap, hrow]
    simp only [sub_mul, Finset.sum_sub_distrib, add_mul, Finset.sum_add_distrib]
    ring
  rw [he] at hsum
  apply le_trans ?_ hsum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (by linarith [hd i]) (sq_nonneg _)

/-- Congruence is transported by a right inverse, not by a floating assertion
that a proposed Cholesky preconditioner is invertible. -/
theorem congruence_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → ι → ℝ) (C : κ → ι → ℝ)
    (hcover : ∀ x : ι → ℝ, ∃ y : κ → ℝ, ∀ i, x i = ∑ j, C j i * y j)
    (h : ∀ y : κ → ℝ, 0 ≤ ∑ i, ∑ j, M i j *
      (∑ k, C k i*y k) * (∑ k, C k j*y k)) (x : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, M i j*x i*x j := by
  obtain ⟨y, hy⟩ := hcover x
  simpa only [hy] using h y

open Matrix

 theorem quad_eq_dot {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    (∑ i, ∑ j, M i j*x i*x j) = dotProduct x (M.mulVec x) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A finite entrywise certificate of the congruence controls the original
quadratic form. The right-inverse equation is exact and explicit. -/
theorem preconditioned_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M C D : Matrix ι ι ℝ) (hinv : C * D = 1)
    (hs : ∀ i j, (C.transpose * M * C) i j = (C.transpose * M * C) j i)
    (hd : ∀ i, (∑ j, |(C.transpose * M * C) i j|) ≤
      (C.transpose * M * C) i i + |(C.transpose * M * C) i i|)
    (x : ι → ℝ) : 0 ≤ ∑ i, ∑ j, M i j*x i*x j := by
  let y := D.mulVec x
  have hxy : C.mulVec y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have h := quadratic_lower (C.transpose * M * C) 0 hs (by simpa using hd) y
  simp only [zero_mul] at h
  rw [quad_eq_dot] at h ⊢
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, hxy] at h
  simpa only [dotProduct_comm] using h

/-- Strict dominance of the congruence itself proves the proposed square
preconditioner has no kernel. No separately validated inverse is necessary. -/
theorem preconditioner_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M C : Matrix ι ι ℝ) (η : ℝ) (hη : 0 < η)
    (hs : ∀ i j, (C.transpose * M * C) i j = (C.transpose * M * C) j i)
    (hd : ∀ i, η + (∑ j, |(C.transpose * M * C) i j|) ≤
      (C.transpose * M * C) i i + |(C.transpose * M * C) i i|) :
    Function.Injective C.mulVec := by
  have hker : ∀ y, C.mulVec y = 0 → y = 0 := by
    intro y hy
    have h := quadratic_lower (C.transpose * M * C) η hs hd y
    rw [quad_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_transpose_mulVec, hy] at h
    simp only [Matrix.mulVec_zero, dotProduct_zero] at h
    have hsum : ∑ i, y i^2 = 0 := by
      have hn : 0 ≤ ∑ i, y i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      nlinarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (Finset.univ : Finset ι)) => sq_nonneg (y i))).mp hsum
    funext i
    have hi := hz i (Finset.mem_univ i)
    simpa only [Pi.zero_apply] using (sq_eq_zero_iff.mp hi)
  intro x y hxy
  have hz : C.mulVec (x-y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hker _ hz)

/-- Consumer-first strengthening: strict entrywise dominance after any real
square congruence proves the original quadratic form nonnegative, without
an inverse hypothesis, whitening hypothesis, or eigenvalue computation. -/
theorem strict_preconditioned_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M C : Matrix ι ι ℝ) (η : ℝ) (hη : 0 < η)
    (hs : ∀ i j, (C.transpose * M * C) i j = (C.transpose * M * C) j i)
    (hd : ∀ i, η + (∑ j, |(C.transpose * M * C) i j|) ≤
      (C.transpose * M * C) i i + |(C.transpose * M * C) i i|)
    (x : ι → ℝ) : 0 ≤ ∑ i, ∑ j, M i j*x i*x j := by
  have hi := preconditioner_injective M C η hη hs hd
  have hu := Matrix.mulVec_injective_iff_isUnit.mp hi
  obtain ⟨D, hD⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp
    (Matrix.mulVec_surjective_iff_isUnit.mpr hu)
  apply preconditioned_nonneg M C D hD hs ?_ x
  intro i
  linarith [hd i]

#print axioms strict_preconditioned_nonneg
#print axioms preconditioned_nonneg
#print axioms quadratic_lower
#print axioms congruence_nonneg
end N11Formalization.ResumeQuadraticCertificate
