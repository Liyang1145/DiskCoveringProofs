import Mathlib

open Metric

abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

#check @Fin.sum_univ_two
#check @Fin.sum_univ_succ
#check @Fin.sum_univ_zero
#check @Fin.sum_univ_one
#check @EuclideanSpace.norm_eq
#check @EuclideanSpace.dist_eq
#check @EuclideanSpace.norm_sq_eq

example (f : Fin 2 → ℝ) : (∑ i : Fin 2, f i) = f 0 + f 1 := by
  simp [Fin.sum_univ_succ]

example (p q : Point) :
    dist p q = Real.sqrt ((p.ofLp 0 - q.ofLp 0) ^ 2 + (p.ofLp 1 - q.ofLp 1) ^ 2) := by
  rw [dist_eq_norm]
  have h0 : (p - q).ofLp 0 = p.ofLp 0 - q.ofLp 0 := rfl
  have h1 : (p - q).ofLp 1 = p.ofLp 1 - q.ofLp 1 := rfl
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, add_zero, h0, h1,
    Real.norm_eq_abs, sq_abs]
