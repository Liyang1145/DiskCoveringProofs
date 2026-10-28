import N11Formalization.ActualRefinementTriangleUniqueness
import N11Formalization.ActualNearestRingTriangles

/-! Actual SELECTED refinement ring-only triangle count q<=1. Not merely
ear-index count: labelSet injectivity proves distinct finite triangle indices
cannot be duplicate realizations of the same ring triple. No noAdjacent,
global disk, Euler or two-fan classification input is used. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementEarCount
open ActualVoronoiCells ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualNearestRingTriangles ActualRingDirectionOrder ActualCoverStructuralReduction

def RingOnly {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (a : R.Index) : Prop :=
  ∀ v : Fin 3, (R.labels a v).val < 9

def ringLabel {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {a : R.Index} (ha : RingOnly R a) (v : Fin 3) : Fin 9 := ⟨(R.labels a v).val,ha v⟩

theorem ringLabel_site {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {a : R.Index} (ha : RingOnly R a) (v : Fin 3) : ringSite (ringLabel ha v) = R.labels a v :=
  Fin.ext rfl

theorem ringLabel_injective {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {a : R.Index} (ha : RingOnly R a) : Function.Injective (ringLabel ha) := by
  intro i j he
  apply Refinement.labels_injective R a
  have hh := congrArg ringSite he
  simpa only [ringLabel_site] using hh

theorem ring_only_indices_unique {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {a b : R.Index} (ha : RingOnly R a) (hb : RingOnly R b) : a = b := by
  have hA := ringLabel_injective ha
  have hB := ringLabel_injective hb
  have hnea (v : Fin 3) : R.witness a ∈ Cell c (ringSite (ringLabel ha v)) := by
    rw [ringLabel_site]
    exact (Refinement.real_triangle R a).2.1 v |>.1
  have hneb (v : Fin 3) : R.witness b ∈ Cell c (ringSite (ringLabel hb v)) := by
    rw [ringLabel_site]
    exact (Refinement.real_triangle R b).2.1 v |>.1
  have hsets := nearest_ring_triangles_same_set h hr
    (mem_unitDisk.mpr (Refinement.real_triangle R a).1.le)
    (mem_unitDisk.mpr (Refinement.real_triangle R b).1.le)
    (hA.ne (by decide : (0 : Fin 3) ≠ 1))
    (hA.ne (by decide : (2 : Fin 3) ≠ 0))
    (hA.ne (by decide : (2 : Fin 3) ≠ 1))
    (hB.ne (by decide : (0 : Fin 3) ≠ 1))
    (hB.ne (by decide : (2 : Fin 3) ≠ 0))
    (hB.ne (by decide : (2 : Fin 3) ≠ 1))
    (hnea 0) (hnea 1) (hnea 2) (hneb 0) (hneb 1) (hneb 2)
  have himage := congrArg (Finset.image ringSite) hsets
  simp only [Finset.image_insert,Finset.image_singleton,ringLabel_site] at himage
  exact labelSet_injective h.injective R himage

def ringOnlyTriangles {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) :
    Finset R.Index := by
  classical
  exact Finset.univ.filter (RingOnly R)

theorem actual_selected_ear_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (ringOnlyTriangles R).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact ring_only_indices_unique h hr R (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

end N11Formalization.ActualRefinementEarCount
#check @N11Formalization.ActualRefinementEarCount.actual_selected_ear_count
#print axioms N11Formalization.ActualRefinementEarCount.ring_only_indices_unique
#print axioms N11Formalization.ActualRefinementEarCount.actual_selected_ear_count
