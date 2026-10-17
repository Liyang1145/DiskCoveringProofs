import N11Formalization.ResumeLinearSolve

noncomputable section
namespace N11Formalization.ResumeLinearSolveInterval


/-- Real matrix action in the sup norm; not the local Frobenius norm. -/
def realMatCLM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => ∑ k, A i k •
    (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ))

theorem realMatCLM_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    realMatCLM A x = A.mulVec x := by
  funext i
  simp only [realMatCLM, ContinuousLinearMap.pi_apply, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Matrix.mulVec, dotProduct]

theorem realMatCLM_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    realMatCLM A (Pi.single j 1) i = A i j := by
  rw [realMatCLM_apply]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem residual_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℚ) (J : Fin n → Fin n → RatInterval)
    (q : ℝ) (hq : 0 ≤ q) (hJ : ∀ i j, (J i j).Mem (A i j))
    (hrow : ∀ i, ∑ j, max |((krawczykMat C J i j).lo : ℝ)|
      |((krawczykMat C J i j).hi : ℝ)| ≤ q) (x : Fin n → ℝ) :
    ‖x-(show Matrix (Fin n) (Fin n) ℝ from fun i j => (C i j : ℝ)).mulVec (A.mulVec x)‖ ≤ q*‖x‖ := by
  have ho := opNorm_le_of_jacobian_enclosure C (realMatCLM A) hq J
    (fun i j => by simpa only [realMatCLM_single] using hJ i j) hrow
  have hh := (ContinuousLinearMap.id ℝ (Fin n → ℝ) - (ratMatCLM C).comp (realMatCLM A)).le_opNorm x
  have ha : ratMatCLM C (realMatCLM A x) = (show Matrix (Fin n) (Fin n) ℝ from fun i j => (C i j : ℝ)).mulVec (A.mulVec x) := by
    rw [realMatCLM_apply]
    funext i
    exact ratMatCLM_apply C (A.mulVec x) i
  simpa only [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, ha]
    using le_trans hh (mul_le_mul_of_nonneg_right ho (norm_nonneg x))

/-- A finite outward interval certificate is enough to define an exact source
solution. Crucially, no numerical midpoint solution is promoted to equality. -/
theorem existsUnique_of_intervals {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℚ) (J : Fin n → Fin n → RatInterval)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hJ : ∀ i j, (J i j).Mem (A i j))
    (hrow : ∀ i, ∑ j, max |((krawczykMat C J i j).lo : ℝ)|
      |((krawczykMat C J i j).hi : ℝ)| ≤ q) (b : Fin n → ℝ) :
    ∃! x, A.mulVec x=b :=
  ResumeLinearSolve.existsUnique_solution A (fun i j => (C i j : ℝ)) q hq1
    (residual_bound A C J q hq hJ hrow) b

#print axioms residual_bound
#print axioms existsUnique_of_intervals
end N11Formalization.ResumeLinearSolveInterval
