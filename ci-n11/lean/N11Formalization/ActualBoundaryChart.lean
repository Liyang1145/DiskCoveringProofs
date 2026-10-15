import N11Formalization.ActualBoundaryAnchorWidths
import N11Formalization.SourceChartIsometry

/-! Productive actual-cover -> source simplex chart bridge.
All eighteen boundary rows are paid; the SAME rotation acts on all centers
and on any eventual face witnesses. The remaining33 canonical faces are
explicit, not synthesized from the source candidate. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryChart
open DSHTopologyInterior ActualRingDirectionOrder ActualBoundaryArcFrame
open ActualBoundaryCyclicOrder ActualBoundaryAnchorWidths ResumeGlobal
open SourceChartIsometry ResumeNetwork

theorem anchorAngle_eq_actual {c : Fin 11 → Point} {r L D : ℝ}
    {y : Fin 9 → ℝ} (hw : ∀ i, width L D y i = gap c r i) (j : Fin 9) :
    anchorAngle L D y j.val = anchorLift c r j-anchorLift c r 0 := by
  have hall (n : ℕ) (hn : n < 9) :
      anchorAngle L D y n = anchorLift c r ⟨n,hn⟩-anchorLift c r 0 := by
    induction n with
    | zero => simp [anchor_zero]
    | succ n ih =>
      have hn0 : n < 9 := by omega
      let i : Fin 9 := ⟨n,hn0⟩
      have hi8 : i ≠ 8 := by
        intro hi
        have hv := congrArg (fun q : Fin 9 => q.val) hi
        change n = 8 at hv
        omega
      have hnxt : nextRing i = (⟨n+1,hn⟩ : Fin 9) := by
        apply Fin.ext
        exact next_val hi8
      have hrec := anchor_succ_sub L D y i
      change anchorAngle L D y (n+1)-anchorAngle L D y n = width L D y i at hrec
      rw [hw i] at hrec
      simp only [gap,nextShift,if_neg hi8,Int.cast_zero,zero_mul,add_zero,hnxt] at hrec
      have hp := ih hn0
      change anchorAngle L D y n = anchorLift c r i-anchorLift c r 0 at hp
      linarith
  exact hall j.val j.isLt

theorem rotate_anchor_eq_chart {c : Fin 11 → Point} {r : ℝ} {y : Fin 9 → ℝ}
    (hw : ∀ i, width Patch120K5Actual.L Patch120K5Actual.D y i = gap c r i)
    (j : Fin 9) :
    rotation (-anchorLift c r 0) (anchors c r j) = chartAnchors y j := by
  change rotate (-anchorLift c r 0) (circleMap (anchorLift c r j)) =
    circleMap (anchorAngle Patch120K5Actual.L Patch120K5Actual.D y j.val)
  rw [rotate_circle,anchorAngle_eq_actual hw]
  congr 1
  ring

structure BoundaryChart (c : Fin 11 → Point) (r : ℝ) where
  y : Fin 9 → ℝ
  nonneg : ∀ i, 0 ≤ y i
  sum_one : ∑ i, y i = 1
  width_actual : ∀ i, width Patch120K5Actual.L Patch120K5Actual.D y i = gap c r i
  anchor_match : ∀ i, rotation (-anchorLift c r 0) (anchors c r i) = chartAnchors y i
  boundary : ∀ i : Fin 9, ∀ side : Fin 2,
    dist (rotation (-anchorLift c r 0) (c (ringSite i)))
      (chartAnchors y (anchorIndex i side)) ≤ r

/-- An ACTUAL cover produces its simplex point and its18 chart rows. -/
theorem boundaryChart_of_cover {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) : Nonempty (BoundaryChart c r) := by
  obtain ⟨y,hy0,hy1,hw⟩ := actual_simplex hc hr hR ho
    (L := Patch120K5Actual.L) (D := Patch120K5Actual.D) rfl rfl FlashLeafRootChart.D_pos
  have hm := rotate_anchor_eq_chart hw
  refine ⟨⟨y,hy0,hy1,hw,hm,?_⟩⟩
  intro i side
  rw [← hm]
  change dist (rotate (-anchorLift c r 0) (c (ringSite i)))
    (rotate (-anchorLift c r 0) (anchors c r (anchorIndex i side))) ≤ r
  rw [rotate_dist]
  have hb := boundary_rows hc hr hR ho i
  fin_cases side
  · simpa [anchorIndex,dist_comm] using hb.1
  · simpa [anchorIndex,dist_comm] using hb.2

/-- Transparent remaining-face consumer: not a claim of an unconditional
canonical graph. These are the EXACT33 missing geometric inequalities. -/
theorem BoundaryChart.feasible_of_faces {c : Fin 11 → Point} {r : ℝ}
    (b : BoundaryChart c r) (hr : 0 ≤ r) (Z : Fin 11 → Point)
    (hfaces : ∀ f : Fin 11, ∀ v : Fin 3, dist (c (face f v)) (Z f) ≤ r) :
    Feasible (chartAnchors b.y)
      (fun i => rotation (-anchorLift c r 0) (c i))
      (fun f => rotation (-anchorLift c r 0) (Z f)) r := by
  refine ⟨hr,?_⟩
  intro e
  rcases e with ⟨i,side⟩ | ⟨f,v⟩
  · exact b.boundary i side
  · change dist (rotate _ _) (rotate _ _) ≤ r
    rw [rotate_dist]
    exact hfaces f v

end N11Formalization.ActualBoundaryChart
#check @N11Formalization.ActualBoundaryChart.boundaryChart_of_cover
#check @N11Formalization.ActualBoundaryChart.BoundaryChart.feasible_of_faces
#print axioms N11Formalization.ActualBoundaryChart.boundaryChart_of_cover
#print axioms N11Formalization.ActualBoundaryChart.BoundaryChart.feasible_of_faces
