import N11Formalization.ActualBoundaryCyclicOrder
import N11Formalization.ResumeGlobalAnchor

/-! ACTUAL eighteen boundary rows and width data.
These anchors are closed-cap right endpoints, not claimed to be ownership
switches. That is sufficient for the boundary half of the SOC relaxation.
The width at chart slot i belongs to ring i+1 (cyclic), not ring i. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryAnchorWidths
open DSHTopologyInterior ActualRingDirectionOrder ActualBoundaryArcFrame
open ActualBoundaryArcOrder ActualBoundaryCyclicOrder

def anchorLift (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) : ℝ :=
  rightEnd c r i 0
def anchors (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) : Point :=
  circleMap (anchorLift c r i)
def gap (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) : ℝ :=
  anchorLift c r (nextRing i)+((nextShift i):ℝ)*period-anchorLift c r i

theorem rightEnd_shift (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) (n : ℤ) :
    rightEnd c r i n = anchorLift c r i+(n:ℝ)*period := by
  simp only [rightEnd,arcCenter,anchorLift,Int.cast_zero,zero_mul,add_zero]
  ring

theorem halfWidth_nonneg (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) :
    0 ≤ halfWidth c r i := capHalfWidth_nonneg _ _

theorem right_mem_self (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) :
    anchorLift c r i ∈ Arc c r i 0 := by
  change arcCenter c i 0-halfWidth c r i ≤ arcCenter c i 0+halfWidth c r i ∧
    rightEnd c r i 0 ≤ rightEnd c r i 0
  exact ⟨by linarith [halfWidth_nonneg c r i],le_rfl⟩

theorem right_mem_next {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) (i : Fin 9) :
    anchorLift c r i ∈ Arc c r (nextRing i) (nextShift i) := by
  have he := endpoints_ordered hc hr hR (next_ne i) (next_center_gt ho i)
  exact ⟨neighbor_overlap hc hr hR ho i,he.2.le⟩

theorem anchor_self {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) (i : Fin 9) :
    dist (anchors c r i) (c (ringSite i)) ≤ r :=
  (cap_iff_lift hc hr hR i _).mpr ⟨0,right_mem_self c r i⟩

theorem anchor_next {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) (i : Fin 9) :
    dist (anchors c r i) (c (ringSite (nextRing i))) ≤ r :=
  (cap_iff_lift hc hr hR (nextRing i) _).mpr ⟨nextShift i,right_mem_next hc hr hR ho i⟩

theorem next_prev (i : Fin 9) : nextRing (i-1) = i := by
  simp [nextRing]

/-- Exact network boundary indexing: ring i meets anchors i-1 and i. -/
theorem boundary_rows {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) (i : Fin 9) :
    dist (anchors c r (i-1)) (c (ringSite i)) ≤ r ∧
      dist (anchors c r i) (c (ringSite i)) ≤ r := by
  constructor
  · simpa only [next_prev] using anchor_next hc hr hR ho (i-1)
  · exact anchor_self hc hr hR i

theorem gap_positive {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) (i : Fin 9) :
    0 < gap c r i := by
  have he := (endpoints_ordered hc hr hR (next_ne i) (next_center_gt ho i)).2
  rw [rightEnd_shift c r i 0,rightEnd_shift c r (nextRing i) (nextShift i)] at he
  simp only [Int.cast_zero,zero_mul,add_zero] at he
  dsimp [gap]
  linarith

theorem gap_le_two_halfWidth {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) (i : Fin 9) :
    gap c r i ≤ 2*halfWidth c r (nextRing i) := by
  have hm := (right_mem_next hc hr hR ho i).1
  have he := rightEnd_shift c r (nextRing i) (nextShift i)
  dsimp [leftEnd,rightEnd] at hm he
  dsimp [gap]
  linarith

theorem gap_le_L {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) (i : Fin 9) :
    gap c r i ≤ 2*Real.arcsin (19/50) := by
  have hne := ActualInwardNormalization.touching_ne_zero
    (by linarith : r < 1) (hR.ring_meets (i := ringSite (nextRing i)) (nextRing i).isLt)
  have hw : halfWidth c r (nextRing i) ≤ Real.arcsin r :=
    capHalfWidth_le_arcsin hne (Covers.nonneg hc) (by linarith)
  have ha := Real.arcsin_le_arcsin hr.le
  linarith [gap_le_two_halfWidth hc hr hR ho i]

/-- Cyclic telescope, with the one and only wrap at chart slot 8. -/
theorem gap_sum (c : Fin 11 → Point) (r : ℝ) :
    ∑ i : Fin 9, gap c r i = 2*Real.pi := by
  have hperm : (∑ i : Fin 9, anchorLift c r (nextRing i)) =
      ∑ i : Fin 9, anchorLift c r i :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin 9)) (anchorLift c r)
  have hs : (∑ i : Fin 9, ((nextShift i):ℝ)*period) = period := by
    simp [nextShift]
  simp only [gap,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [hperm,hs]
  simp [period]

/-- Genuine Fin9 NONNEGATIVE SUM-ONE chart data, from an arbitrary sorted
actual cover. No source candidate, symmetry or Fin8 sum-one substitution. -/
theorem actual_simplex {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) {L D : ℝ}
    (hL : L = 2*Real.arcsin (19/50)) (hD : D = 9*L-2*Real.pi)
    (hDpos : 0 < D) :
    ∃ y : Fin 9 → ℝ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1 ∧
      ∀ i, ResumeGlobal.width L D y i = gap c r i := by
  apply ResumeGlobal.width_surj L D (gap c r) hDpos hD
  · intro i
    rw [hL]
    exact gap_le_L hc hr hR ho i
  · exact gap_sum c r

end N11Formalization.ActualBoundaryAnchorWidths
#check @N11Formalization.ActualBoundaryAnchorWidths.boundary_rows
#check @N11Formalization.ActualBoundaryAnchorWidths.actual_simplex
#print axioms N11Formalization.ActualBoundaryAnchorWidths.boundary_rows
#print axioms N11Formalization.ActualBoundaryAnchorWidths.actual_simplex
