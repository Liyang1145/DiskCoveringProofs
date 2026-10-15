import N11Formalization.ResumeAnchorFlux
import N11Formalization.FlashLocalH0

noncomputable section
namespace N11Formalization.ResumeFluxTaylor
open ResumeNetwork ResumeDirichletShift ResumeAnchorFlux FlashLocal

/-- Exact circle geometry, not a Taylor polynomial identity. -/
theorem circle_radial_inner (a x : ℝ) :
    inner ℝ (circleMap a) (circleMap (a+x)-circleMap a) = Real.cos x - 1 := by
  rw [inner_sub_right, inner_circleMap, inner_circleMap]
  simp only [sub_self, Real.cos_zero]
  congr 1
  ring_nf
  exact Real.cos_neg x

/-- Nonnegative radial base flux has a global quadratic lower bound, both
signs of angular displacement. Stationarity/radiality is an explicit premise. -/
theorem baseCross_radial_lower {α : Edge → ℝ} {U : Fin 9 → Point}
    {C Z : Fin 11 → Point} (θ x a : Fin 9 → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hflux : ∀ i, flux α U C Z i = a i • circleMap (θ i)) :
    -(∑ i, a i * x i ^ 2) ≤
      2 * baseCross α U C Z (fun i => circleMap (θ i+x i)-circleMap (θ i)) := by
  rw [baseCross_eq_flux, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [hflux i, real_inner_smul_left, circle_radial_inner]
  have hc : 1 - (x i)^2 / 2 ≤ Real.cos (x i) := Real.one_sub_sq_div_two_le_cos
  have hm := mul_le_mul_of_nonneg_left hc (ha i)
  nlinarith

/-- Generic Taylor split for signed anchor flux; the actual directional norm
bound on the remainder is a named premise, not a numerical constant here. -/
theorem baseCross_add (α : Edge → ℝ) (U V W : Fin 9 → Point) (C Z : Fin 11 → Point) :
    baseCross α U C Z (V+W) = baseCross α U C Z V + baseCross α U C Z W := by
  rw [baseCross_eq_flux, baseCross_eq_flux, baseCross_eq_flux]
  simp [inner_add_right, Finset.sum_add_distrib]

#check @baseCross_radial_lower
#print axioms baseCross_radial_lower
end N11Formalization.ResumeFluxTaylor
