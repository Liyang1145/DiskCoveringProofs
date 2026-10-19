import N11Formalization.ActualRefinementLinkDegrees
import N11Formalization.ActualPuncturedDiskConnected

/-! Every ACTUAL clipped-cell frontier is path connected: compact convex
cell with genuine center interior is sent to the planar unit circle by a
homeomorphism. For a hub, this frontier is wholly insideD and every point
has another true nearest label. No polygonal-cell/Jordan assumption. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualClippedCellFrontiers
open ActualVoronoiCells ActualVoronoiIncidence ActualCoverStructuralReduction
open ActualClippedCellPartition ActualPuncturedDiskConnected

theorem point_rank_gt_one : 1 < Module.rank ℝ Point := by
  rw [← Module.finrank_eq_rank]
  have hd : Module.finrank ℝ Point = 2 := finrank_euclideanSpace_fin
  rw [hd]
  norm_num

theorem actual_clipped_frontier_pathConnected {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (i : Fin 11) :
    IsPathConnected (frontier (ClippedCell c i)) := by
  obtain ⟨e,_,_,he⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (clipped_convex c i) ⟨c i,Representative.clipped_center_interior h i⟩
    (clipped_compact c i).isBounded
  have hcirc : IsPathConnected (Metric.sphere (0 : Point) 1) :=
    isPathConnected_sphere point_rank_gt_one 0 (by norm_num)
  have himage : e.symm '' Metric.sphere (0 : Point) 1 = frontier (ClippedCell c i) := by
    rw [← he]
    exact Set.image_image _ _ _ |>.trans (by simp)
  rw [← himage]
  exact hcirc.image e.symm.continuous

theorem hub_clipped_eq_cell {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) {i : Fin 11} (hi : 9 ≤ i.val) :
    ClippedCell c i = Cell c i := by
  apply Set.inter_eq_right.mpr
  intro x hx
  exact mem_unitDisk.mpr (h.cells.inside i hi x hx).le

theorem actual_hub_frontier_pathConnected {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) {i : Fin 11} (hi : 9 ≤ i.val) :
    IsPathConnected (frontier (Cell c i)) := by
  rw [← hub_clipped_eq_cell h hi]
  exact actual_clipped_frontier_pathConnected h i

theorem cell_frontier_tie {c : Fin 11 → Point} {i : Fin 11} {x : Point}
    (hx : x ∈ frontier (Cell c i)) :
    x ∈ Cell c i ∧ ∃ j : Fin 11, j ≠ i ∧ x ∈ Cell c j := by
  have hxcell : x ∈ Cell c i := by
    have hc := frontier_subset_closure hx
    rwa [(cell_closed c i).closure_eq] at hc
  refine ⟨hxcell,?_⟩
  by_contra hnone
  have hstrict : x ∈ StrictCell c i := by
    intro j hji
    apply lt_of_le_of_ne (hxcell j)
    intro he
    have hxj : x ∈ Cell c j := by intro k; rw [← he]; exact hxcell k
    exact hnone ⟨j,hji,hxj⟩
  have hxint : x ∈ interior (Cell c i) := by
    apply interior_mono (strictCell_subset c i)
    rw [(strictCell_open c i).interior_eq]
    exact hstrict
  exact Set.disjoint_left.mp disjoint_interior_frontier hxint hx

theorem actual_hub_frontier_geometry {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) {i : Fin 11} (hi : 9 ≤ i.val) {x : Point}
    (hx : x ∈ frontier (Cell c i)) :
    ‖x‖ < 1 ∧ dist x (c i) ≤ r ∧ x ∈ Cell c i ∧
      ∃ j : Fin 11, j ≠ i ∧ x ∈ Cell c j := by
  have htie := cell_frontier_tie hx
  have hinside := h.cells.inside i hi x htie.1
  exact ⟨hinside,nearest_le_radius h.cover (mem_unitDisk.mpr hinside.le) htie.1,htie⟩

end N11Formalization.ActualClippedCellFrontiers
#check @N11Formalization.ActualClippedCellFrontiers.actual_clipped_frontier_pathConnected
#check @N11Formalization.ActualClippedCellFrontiers.actual_hub_frontier_geometry
#print axioms N11Formalization.ActualClippedCellFrontiers.actual_clipped_frontier_pathConnected
#print axioms N11Formalization.ActualClippedCellFrontiers.actual_hub_frontier_geometry
