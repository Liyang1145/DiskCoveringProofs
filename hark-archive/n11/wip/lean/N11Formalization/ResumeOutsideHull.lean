import N11Formalization.Definitions
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Topology

/-! Outside a finite center hull, an outward ray cannot approach any center.
This removes the cap-tiling interface: boundary coverage plus hull coverage suffices,
without replacing the exact root radius by a rounded number. -/
namespace N11Formalization.ResumeOutsideHull

/-- A common nonzero outward direction for every center, with quantitative margin. -/
theorem exists_outward_direction (c : Fin 11 → Point) (p : Point)
    (hp : p ∉ convexHull ℝ (Set.range c)) :
    ∃ v : Point, v ≠ 0 ∧ ∀ i, ‖v‖ ^ 2 ≤ inner ℝ v (p - c i) := by
  let K := convexHull ℝ (Set.range c)
  have hK : Convex ℝ K := convex_convexHull ℝ _
  have hne : K.Nonempty := ⟨c 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩
  have hc : IsComplete K := ((Set.finite_range c).isCompact_convexHull ℝ).isComplete
  obtain ⟨q, hq, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc hK p
  have hproj := (norm_eq_iInf_iff_real_inner_le_zero hK hq).mp hmin
  refine ⟨p - q, ?_, ?_⟩
  · intro he
    have : p = q := sub_eq_zero.mp he
    exact hp (this ▸ hq)
  · intro i
    have hi := hproj (c i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    have hid : p - c i = (p - q) - (c i - q) := by abel
    rw [hid, inner_sub_right, real_inner_self_eq_norm_sq]
    linarith

/-- Consequently a point outside the hull admits a ray nondecreasing in distance
to every site; the nonzero requirement is essential for reaching the boundary. -/
theorem exists_outward_nonneg (c : Fin 11 → Point) (p : Point)
    (hp : p ∉ convexHull ℝ (Set.range c)) :
    ∃ v : Point, v ≠ 0 ∧ ∀ i, 0 ≤ inner ℝ v (p - c i) := by
  obtain ⟨v, hv, h⟩ := exists_outward_direction c p hp
  exact ⟨v, hv, fun i => (sq_nonneg ‖v‖).trans (h i)⟩

#check @exists_outward_nonneg
#print axioms exists_outward_nonneg
end N11Formalization.ResumeOutsideHull
