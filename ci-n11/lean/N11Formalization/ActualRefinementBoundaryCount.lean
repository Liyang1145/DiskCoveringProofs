import N11Formalization.ActualRefinementSideMultiplicity
import N11Formalization.ActualBoundaryFacets

/-! Each of the nine ACTUAL boundary-ring cycle sides occurs in EXACTLY
one selected finite-refinement triangle. Existence from real boundary facet
starts; uniqueness from actual nearest vertex and local selected side.
No global disk/Euler/one-boundary-face premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementBoundaryCount
open ActualVoronoiCells ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementFacetRetention
open ActualRefinementSideMultiplicity ActualRingDirectionOrder ActualBoundaryCyclicOrder
open ActualBoundaryNeighborTies ActualBoundaryFacets ActualPositiveFacetGraph
open ActualVoronoiRadialExit

theorem boundary_positive_pair {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) :
    PositivePair c (ringSite i) (ringSite (nextRing i)) := by
  obtain ⟨z⟩ := neighbor_tie h.cover hr h.labels h.midpoint_order i
  obtain ⟨f⟩ := ActualBoundaryFacets.Representative.boundary_facet_start h hr i z
  have hij : ringSite i ≠ ringSite (nextRing i) := by
    intro he
    exact next_ne i (Fin.ext (congrArg (fun k : Fin 11 => k.val) he))
  have hne : circleMap z.angle ≠ ray (circleMap z.angle) f.direction f.time := by
    intro he
    have hh := f.inside
    rw [← he,circleMap_norm] at hh
    exact lt_irrefl 1 hh
  exact ⟨hij,circleMap z.angle,⟨mem_unitDisk.mpr (circleMap_norm z.angle).le,z.nearest⟩,
    ray (circleMap z.angle) f.direction f.time,⟨mem_unitDisk.mpr f.inside.le,f.nearest⟩,hne⟩

def boundaryTriangles {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 9) : Finset R.Index := by
  classical
  exact Finset.univ.filter (fun a =>
    ringSite i ∈ labelSet R a ∧ ringSite (nextRing i) ∈ labelSet R a)

theorem actual_boundary_triangle_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9) :
    (boundaryTriangles R i).card = 1 := by
  classical
  have hle : (boundaryTriangles R i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have hA := (Finset.mem_filter.mp ha).2
    have hB := (Finset.mem_filter.mp hb).2
    exact boundary_pair_triangle_unique R h hr i hA.1 hA.2 hB.1 hB.2
  obtain ⟨a,ha,hb⟩ := Refinement.positive_pair_retained R h hr (boundary_positive_pair h hr i)
  have hmem : a ∈ boundaryTriangles R i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem_labelSet.mpr ha,mem_labelSet.mpr hb⟩
  have hpos := Finset.card_pos.mpr ⟨a,hmem⟩
  omega

end N11Formalization.ActualRefinementBoundaryCount
#check @N11Formalization.ActualRefinementBoundaryCount.actual_boundary_triangle_count
#print axioms N11Formalization.ActualRefinementBoundaryCount.boundary_positive_pair
#print axioms N11Formalization.ActualRefinementBoundaryCount.actual_boundary_triangle_count
