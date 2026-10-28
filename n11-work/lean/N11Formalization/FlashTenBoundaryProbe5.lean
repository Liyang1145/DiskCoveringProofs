import N11Formalization.FlashTenBoundaryAnalytic
open scoped Interval
open MeasureTheory
namespace N11Formalization

#print Function.Periodic.intervalIntegral_add_eq
#print intervalIntegral.integral_comp_add_right
#print Real.cos_le_cos_iff_abs_le
#print EuclideanSpace.dist_eq
#print EuclideanSpace.norm_sq_eq
#print PiLp.norm_sq_eq_of_L2
example (θ ρ φ : ℝ) :
    dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ^ 2
      = (Real.cos θ - ρ * Real.cos φ) ^ 2 + (Real.sin θ - ρ * Real.sin φ) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq] ; simp ; ring_nf
end N11Formalization
