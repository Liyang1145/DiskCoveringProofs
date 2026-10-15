import N11Formalization.FlashTenBoundaryArc
open scoped Interval
open MeasureTheory
namespace N11Formalization

theorem p_dist_add_left_eq (h a b : Point) : dist (h + a) (h + b) = dist a b := by
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub]

theorem p_dist_smul_of_nonneg {q : ℝ} (hq : 0 ≤ q) (a b : Point) :
    dist (q • a) (q • b) = q * dist a b := by
  rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]

theorem p_arc_scale {h : Point} {q : ℝ} (hq : 0 < q) (w : Point) {r : ℝ} (θ : ℝ) :
    dist (h + q • angPt θ) (h + q • w) ≤ r ↔ dist (angPt θ) w ≤ r / q := by
  rw [p_dist_add_left_eq, p_dist_smul_of_nonneg hq.le]
  constructor
  · intro h
    rw [le_div_iff₀ hq]
    linarith
  · intro h
    have := (le_div_iff₀ hq).mp h
    linarith

end N11Formalization
