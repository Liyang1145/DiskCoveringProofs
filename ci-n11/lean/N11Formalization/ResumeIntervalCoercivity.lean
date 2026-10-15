import N11Formalization.ResumeQuadraticCertificate
import N11Formalization.Interval.Vector

noncomputable section
namespace N11Formalization.ResumeIntervalCoercivity
open Finset Matrix ResumeQuadraticCertificate

/-- Rational outward entry enclosures produce the real all-row dominance
hypothesis. Diagonal absolute values cancel: only off-diagonal magnitudes
need an upper bound. Membership is indispensable, not inferred from sampling. -/
theorem dominance_of_intervals {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (B : ι → ι → RatInterval) (η : ℚ)
    (hmem : ∀ i j, RatInterval.Mem (B i j) (Q i j))
    (hrow : ∀ i, η + (∑ j, if j=i then 0 else (B i j).abs.hi) ≤ (B i i).lo) :
    ∀ i, (η : ℝ) + (∑ j, |Q i j|) ≤ Q i i + |Q i i| := by
  intro i
  have hd := RatInterval.mem_lo_le (hmem i i)
  have hr : (η : ℝ) + (∑ j, if j=i then (0 : ℝ) else ((B i j).abs.hi : ℝ)) ≤ ((B i i).lo : ℝ) := by
    have hh : ((η + (∑ j, if j=i then 0 else (B i j).abs.hi) : ℚ) : ℝ) ≤ ((B i i).lo : ℝ) := Rat.cast_le.mpr (hrow i)
    simpa only [Rat.cast_add, Rat.cast_sum, apply_ite, Rat.cast_zero] using hh
  have hb : (∑ j, if j=i then (0 : ℝ) else |Q i j|) ≤
      ∑ j, if j=i then (0 : ℝ) else ((B i j).abs.hi : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · rfl
    · exact RatInterval.mem_le_hi (RatInterval.abs_mem (hmem i j))
  have he : (∑ j, |Q i j|) = |Q i i| + ∑ j, if j=i then (0 : ℝ) else |Q i j| := by
    calc
      _ = ∑ j, ((if j=i then |Q i i| else 0) + (if j=i then 0 else |Q i j|)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j=i <;> simp [h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [he]
  linarith

/-- Full certificate consumer: exact rational margin and outward bounds for
CᵀMC prove M≥0. C may be any real square proposal. -/
theorem nonneg_of_intervals {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M C : Matrix ι ι ℝ) (B : ι → ι → RatInterval) (η : ℚ) (hη : 0 < η)
    (hs : ∀ i j, (C.transpose*M*C) i j = (C.transpose*M*C) j i)
    (hmem : ∀ i j, RatInterval.Mem (B i j) ((C.transpose*M*C) i j))
    (hrow : ∀ i, η + (∑ j, if j=i then 0 else (B i j).abs.hi) ≤ (B i i).lo)
    (x : ι → ℝ) : 0 ≤ ∑ i, ∑ j, M i j*x i*x j := by
  apply strict_preconditioned_nonneg M C (η : ℝ) (by exact_mod_cast hη) hs
  exact dominance_of_intervals _ B η hmem hrow

#print axioms dominance_of_intervals
#print axioms nonneg_of_intervals
end N11Formalization.ResumeIntervalCoercivity
