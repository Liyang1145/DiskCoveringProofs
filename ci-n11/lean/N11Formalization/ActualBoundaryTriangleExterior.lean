import N11Formalization.ActualBoundaryExteriorGeometry
import N11Formalization.ActualBoundaryNeighborTies

/-! Productive exterior-side sign at every ACTUAL boundary nearest switch
and its selected real nearest triangle, including cocircular refinements. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryTriangleExterior
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementSideMultiplicity
open ActualSelectedEdgeOrientation ActualBoundaryExteriorGeometry ActualBoundaryNeighborTies
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open FlashTiling

theorem actual_boundary_triangle_exterior {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (R : Refinement c r) (i : Fin 9) (U : NeighborTie c r i)
    {A : R.Index} {k : Fin 11} (hkp : k ≠ ringSite i) (hkn : k ≠ nextSite i)
    (hAi : ringSite i ∈ labelSet R A) (hAn : nextSite i ∈ labelSet R A)
    (hAk : k ∈ labelSet R A) :
    orient (c (ringSite i)) (c (nextSite i)) (circleMap U.angle) *
      orient (c (ringSite i)) (c (nextSite i)) (c k) < 0 := by
  have hiz := nearest_of_label_mem R hAi
  have hnz := nearest_of_label_mem R hAn
  have hkz := nearest_of_label_mem R hAk
  have hij := (boundary_sites_distinct i).2.1.symm
  exact boundary_point_opposite_third (h.injective.ne hij)
    (h.center_inside _) (h.center_inside _) (circleMap_norm U.angle)
    (Refinement.real_triangle R A).1 U.equidistant
    (le_antisymm (hiz _) (hnz _)) (le_antisymm (hiz k) (hkz _))
    (U.nearest.1 k) (selected_triple_orient_ne h.injective R hij hkp hkn hAi hAn hAk)

end N11Formalization.ActualBoundaryTriangleExterior
#check @N11Formalization.ActualBoundaryTriangleExterior.actual_boundary_triangle_exterior
#print axioms N11Formalization.ActualBoundaryTriangleExterior.actual_boundary_triangle_exterior
