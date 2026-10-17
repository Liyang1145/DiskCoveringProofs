import N11Formalization.ActualCoverStructuralReduction
import N11Formalization.ActualBoundaryTieUniqueness

/-! ACTUAL clipped nearest-cell disk partition. All11 cells are convex,
compact and have nonempty planar interiors; interiors are pairwise disjoint.
This is not yet a finite embedded dual/refinement/classification theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualClippedCellPartition
open ActualVoronoiCells ActualCoverStructuralReduction ActualHubEdgeGeometry
open ActualVoronoiRadialExit

def ClippedCell (c : Fin 11 → Point) (i : Fin 11) : Set Point := unitDisk ∩ Cell c i

theorem disk_eq_closedBall : unitDisk = Metric.closedBall (0 : Point) 1 := by
  ext x
  simp [unitDisk,Metric.mem_closedBall,dist_zero_right]

theorem clipped_convex (c : Fin 11 → Point) (i : Fin 11) : Convex ℝ (ClippedCell c i) := by
  unfold ClippedCell
  rw [disk_eq_closedBall]
  exact (convex_closedBall (0 : Point) 1).inter (cell_convex c i)

theorem clipped_compact (c : Fin 11 → Point) (i : Fin 11) : IsCompact (ClippedCell c i) := by
  unfold ClippedCell
  rw [disk_eq_closedBall]
  exact (isCompact_closedBall (0 : Point) 1).inter_right (cell_closed c i)

theorem clipped_cover (c : Fin 11 → Point) : (⋃ i : Fin 11, ClippedCell c i) = unitDisk := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact hi.1
  · intro hx
    obtain ⟨i,hi⟩ := exists_nearest c x
    exact Set.mem_iUnion.mpr ⟨i,hx,hi⟩

theorem interior_cell_strict {c : Fin 11 → Point} (hc : Function.Injective c)
    {i : Fin 11} {x : Point} (hx : x ∈ interior (Cell c i)) : x ∈ StrictCell c i := by
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  intro j hji
  have hxcell := interior_subset hx
  have hle := hxcell j
  by_contra hnot
  have heq : dist x (c i) = dist x (c j) := le_antisymm hle (le_of_not_gt hnot)
  let d := c j-c i
  have hd : d ≠ 0 := sub_ne_zero.mpr (fun he => hji (hc he))
  have hn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let t := eps/(2*‖d‖)
  have ht : 0 < t := div_pos heps (by linarith)
  let y := ray x d t
  have hdist : dist y x = eps/2 := by
    change dist (ray x d t) x = eps/2
    rw [dist_eq_norm,ray,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    dsimp [t]
    field_simp
  have hy : y ∈ Cell c i := hball (Metric.mem_ball.mpr (by rw [hdist]; linarith))
  have hX := ActualBoundaryTieUniqueness.bisector_equation heq
  have hY := (dist_le_iff_halfspace y (c i) (c j)).mp (hy j)
  change 2*inner ℝ x d = ‖c j‖^2-‖c i‖^2 at hX
  change 2*inner ℝ (x+t • d) d ≤ ‖c j‖^2-‖c i‖^2 at hY
  rw [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq] at hY
  nlinarith [mul_pos ht (sq_pos_of_pos hn)]

theorem clipped_interiors_disjoint {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j) :
    Disjoint (interior (ClippedCell c i)) (interior (ClippedCell c j)) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hI := interior_cell_strict hc (interior_mono Set.inter_subset_right hi)
  have hJ := interior_cell_strict hc (interior_mono Set.inter_subset_right hj)
  exact (lt_asymm (hI j hij.symm) (hJ i hij)).elim

theorem Representative.clipped_center_interior {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (i : Fin 11) : c i ∈ interior (ClippedCell c i) := by
  rw [ClippedCell,interior_inter]
  refine ⟨?_,center_mem_interior_of_ne (fun j hji he => hji (h.injective he))⟩
  apply interior_mono (show {x : Point | ‖x‖ < 1} ⊆ unitDisk from by
    intro x hx
    change ‖x‖ < 1 at hx
    exact mem_unitDisk.mpr hx.le)
  rw [(isOpen_lt continuous_norm continuous_const).interior_eq]
  exact h.center_inside i

end N11Formalization.ActualClippedCellPartition
#check @N11Formalization.ActualClippedCellPartition.clipped_cover
#check @N11Formalization.ActualClippedCellPartition.Representative.clipped_center_interior
#print axioms N11Formalization.ActualClippedCellPartition.clipped_interiors_disjoint
#print axioms N11Formalization.ActualClippedCellPartition.Representative.clipped_center_interior
