import N11Formalization.FlashTenBoundary
open scoped Interval
open MeasureTheory
namespace N11Formalization
noncomputable def angPt (θ : ℝ) : Point := !₂[Real.cos θ, Real.sin θ]

example (θ : ℝ) : ‖angPt θ‖ = 1 := by
  rw [angPt, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.cos_sq_add_sin_sq]

#print IsClosed.mem_of_tendsto
#check tendsto_one_div_add_atTop_nhds_zero_nat
#check Metric.isClosed_closedBall
#check isClosed_iUnion_of_finite
#check Metric.mem_closedBall
end N11Formalization
