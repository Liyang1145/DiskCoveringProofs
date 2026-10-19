import N11Formalization.ActualRingLinkBoundaryData

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeActualRingCircleControls
open ActualVoronoiCells ActualCoverStructuralReduction ActualRingDirectionOrder
open ActualClippedCellPartition ActualRingLinkBoundaryData

/-- A real private circle point is on the clipped frontier but has no
other nearest site. Ring frontiers cannot use the hub-only tie argument. -/
theorem private_circle_frontier_without_tie {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (i : Fin 9) :
    ∃ x : Point, x ∈ frontier (ClippedCell c (ringSite i)) ∧
      ‖x‖ = 1 ∧ ∀ j : Fin 11, j ≠ ringSite i → x ∉ Cell c j := by
  obtain ⟨x,hxn,hxi,hother⟩ := h.private_circle i
  have hxcell : x ∈ Cell c (ringSite i) := by
    intro j
    by_cases hj : j = ringSite i
    · rw [hj]
    · exact hxi.trans (hother j hj).le
  have hxnot (j : Fin 11) (hj : j ≠ ringSite i) : x ∉ Cell c j := by
    intro hxj
    exact (not_le_of_gt (hother j hj)) ((hxj (ringSite i)).trans hxi)
  have hxdisk : x ∉ interior unitDisk := by
    have hd : unitDisk = Metric.closedBall (0 : Point) 1 := by
      ext y
      simp [unitDisk,Metric.mem_closedBall,dist_zero_right]
    rw [hd,interior_closedBall (0 : Point) (by norm_num : (1 : ℝ) ≠ 0)]
    simp [Metric.mem_ball,dist_zero_right,hxn]
  refine ⟨x,?_,hxn,hxnot⟩
  rw [frontier,(clipped_compact c (ringSite i)).isClosed.closure_eq]
  exact ⟨⟨mem_unitDisk.mpr hxn.le,hxcell⟩,
    fun hx => hxdisk (interior_mono Set.inter_subset_left hx)⟩

theorem ring_frontier_not_everywhere_tied {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (i : Fin 9) :
    ¬ ∀ x ∈ frontier (ClippedCell c (ringSite i)),
      ∃ j : Fin 11, j ≠ ringSite i ∧ x ∈ Cell c j := by
  obtain ⟨x,hx,_,hn⟩ := private_circle_frontier_without_tie h i
  intro hall
  obtain ⟨j,hj,hxj⟩ := hall x hx
  exact hn j hj hxj
end N11Formalization.ProbeActualRingCircleControls
#check @N11Formalization.ProbeActualRingCircleControls.private_circle_frontier_without_tie
#check @N11Formalization.ProbeActualRingCircleControls.ring_frontier_not_everywhere_tied
#print axioms N11Formalization.ProbeActualRingCircleControls.private_circle_frontier_without_tie
#print axioms N11Formalization.ProbeActualRingCircleControls.ring_frontier_not_everywhere_tied
