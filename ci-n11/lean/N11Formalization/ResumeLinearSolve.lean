import N11Formalization.KrawczykMatrix
import N11Formalization.ResumeQuadraticCertificate

namespace N11Formalization.ResumeLinearSolve
open Matrix

/-- Source interval_network_envelope.solve uses a proposed inverse C only
through a residual contraction. The contraction forces both A and C injective. -/
theorem injective_of_residual {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℝ)
    (q : ℝ) (hq : q < 1)
    (hres : ∀ x, ‖x-C.mulVec (A.mulVec x)‖ ≤ q*‖x‖) :
    Function.Injective A.mulVec := by
  have hk : ∀ x, A.mulVec x=0 → x=0 := by
    intro x hx
    have hh := hres x
    rw [hx, Matrix.mulVec_zero, sub_zero] at hh
    have hn : ‖x‖=0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hn
  intro x y hxy
  have hz : A.mulVec (x-y)=0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hk _ hz)

theorem existsUnique_solution {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℝ)
    (q : ℝ) (hq : q < 1)
    (hres : ∀ x, ‖x-C.mulVec (A.mulVec x)‖ ≤ q*‖x‖) (b : Fin n → ℝ) :
    ∃! x, A.mulVec x=b := by
  have hi := injective_of_residual A C q hq hres
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hi)
  obtain ⟨x,hx⟩ := hs b
  exact ⟨x,hx,fun y hy => hi (hy.trans hx.symm)⟩

/-- Exact preconditioned residual enclosure for ANY proposed centre y;
no floating solve, inverse, or entrywise equality is a premise. Pi norm is sup. -/
theorem solution_error_bound {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℝ)
    (q : ℝ) (hq : q < 1)
    (hres : ∀ x, ‖x-C.mulVec (A.mulVec x)‖ ≤ q*‖x‖)
    (b x y : Fin n → ℝ) (hx : A.mulVec x=b) :
    ‖x-y‖ ≤ ‖C.mulVec (b-A.mulVec y)‖/(1-q) := by
  have hid : x-y = (x-y-C.mulVec (A.mulVec (x-y)))+C.mulVec (b-A.mulVec y) := by
    rw [Matrix.mulVec_sub, hx]; abel
  have hn : ‖x-y‖ ≤ q*‖x-y‖+‖C.mulVec (b-A.mulVec y)‖ := by
    calc ‖x-y‖ = ‖(x-y-C.mulVec (A.mulVec (x-y)))+C.mulVec (b-A.mulVec y)‖ := congrArg norm hid
      _ ≤ ‖x-y-C.mulVec (A.mulVec (x-y))‖+‖C.mulVec (b-A.mulVec y)‖ := norm_add_le _ _
      _ ≤ q*‖x-y‖+‖C.mulVec (b-A.mulVec y)‖ := add_le_add (hres (x-y)) le_rfl
  apply (le_div_iff₀ (by linarith : 0 < 1-q)).mpr
  nlinarith

#print axioms existsUnique_solution
#print axioms solution_error_bound
end N11Formalization.ResumeLinearSolve
