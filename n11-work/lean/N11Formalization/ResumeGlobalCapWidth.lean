import N11Formalization.Geometry.CapArc
import N11Formalization.Geometry.ArcCovering

/-!
# ResumeGlobal: 同盘两锚点 ⇒ 短弧宽度 ≤ 2 arcsin r
若 circleMap a、circleMap b 同在 closedBall c r（0≤r≤1），且 0 ≤ b−a ≤ π，则 b−a ≤ 2 arcsin r。
复用 CapArc.inner_ge_cos_two_arcsin_of_mem_cap + ArcCovering.inner_circleMap。
-/

namespace N11Formalization.ResumeGlobal
open N11Formalization

theorem width_le_two_arcsin_of_same_ball {a b r : ℝ} {c : Point}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hab : 0 ≤ b - a) (habπ : b - a ≤ Real.pi)
    (ha : dist (circleMap a) c ≤ r) (hb : dist (circleMap b) c ≤ r) :
    b - a ≤ 2 * Real.arcsin r := by
  have hin := inner_ge_cos_two_arcsin_of_mem_cap hr0 hr1 (circleMap_norm b)
    (circleMap_norm a) hb ha
  rw [inner_circleMap] at hin
  have hs0 : 0 ≤ 2 * Real.arcsin r := by
    have := Real.arcsin_nonneg.mpr hr0; linarith
  have hsπ : 2 * Real.arcsin r ≤ Real.pi := by
    have := Real.arcsin_le_pi_div_two r; linarith
  by_contra h
  push_neg at h
  have := Real.cos_lt_cos_of_nonneg_of_le_pi hs0 habπ h
  linarith

end N11Formalization.ResumeGlobal

#print axioms N11Formalization.ResumeGlobal.width_le_two_arcsin_of_same_ball
