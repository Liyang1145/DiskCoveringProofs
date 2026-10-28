import N11Formalization.ActualCircleSegmentAlgebra
import N11Formalization.ActualBoundaryAnchorWidths

/-! Exact circular-sector closure for the genuine nine cap-endpoint gaps.

The gaps are the actual cyclic anchor intervals, not nearest ownership
switch widths.  This file records the exact telescope, determinant
identification, and nonnegative circular-segment remainder that can be
consumed by a later clipped-cell area proof.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCircularSectorClosure
open ActualBoundaryAnchorWidths ActualCircleSegmentAlgebra
open ActualRingDirectionOrder ActualBoundaryCyclicOrder ActualBoundaryArcFrame FlashTiling

theorem gap_nonneg {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r)
    (hr : r < 19/50) (i : Fin 9) :
    0 ≤ gap c r i :=
  (gap_positive h.cover hr h.labels h.midpoint_order i).le

theorem gap_lt_two_pi {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r)
    (hr : r < 19/50) (i : Fin 9) :
    gap c r i < 2*Real.pi := by
  have hg := gap_le_L h.cover hr h.labels h.midpoint_order i
  have ha : Real.arcsin (19/50 : ℝ) < Real.pi/2 :=
    (Real.arcsin_lt_pi_div_two).mpr (by norm_num)
  linarith [Real.pi_pos]

theorem anchor_det_gap {c : Fin 11 → Point} {r : ℝ} (i : Fin 9) :
    det2 (anchors c r i) (anchors c r (nextRing i)) =
      Real.sin (gap c r i) := by
  unfold anchors
  rw [← circleMap_periodic (anchorLift c r (nextRing i)) (nextShift i)]
  rw [ActualCircleSegmentAlgebra.circleMap_det_segment]
  rfl

theorem anchor_shoelace_sine {c : Fin 11 → Point} {r : ℝ} :
    ∑ i : Fin 9, det2 (anchors c r i) (anchors c r (nextRing i)) =
      ∑ i : Fin 9, Real.sin (gap c r i) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact anchor_det_gap i

theorem segment_sum_of_actual_gaps {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) :
    ∑ i : Fin 9, segmentTerm (gap c r i) =
      Real.pi - (∑ i : Fin 9, Real.sin (gap c r i))/2 := by
  exact segmentTerm_sum_widths (gap c r) (gap_sum c r)

theorem segment_sum_nonneg_of_actual_gaps
    {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r)
    (hr : r < 19/50) :
    0 ≤ ∑ i : Fin 9, segmentTerm (gap c r i) := by
  apply Finset.sum_nonneg
  intro i hi
  exact segmentTerm_nonneg (gap_nonneg h hr i)
    (gap_lt_two_pi h hr i).le

theorem segmentTerm_pos_of_actual_gap
    {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r)
    (hr : r < 19/50) (i : Fin 9) :
    0 < segmentTerm (gap c r i) := by
  unfold segmentTerm
  have hs := Real.sin_lt (gap_positive h.cover hr h.labels h.midpoint_order i)
  linarith

theorem anchor_sector_identity {c : Fin 11 → Point} {r : ℝ}
    (h : ActualCoverStructuralReduction.Representative c r) :
    Real.pi -
        (∑ i : Fin 9, det2 (anchors c r i) (anchors c r (nextRing i)))/2 =
      ∑ i : Fin 9, segmentTerm (gap c r i) := by
  rw [anchor_shoelace_sine]
  symm
  exact segment_sum_of_actual_gaps h

end N11Formalization.ActualCircularSectorClosure
#check @N11Formalization.ActualCircularSectorClosure.anchor_sector_identity
#check @N11Formalization.ActualCircularSectorClosure.segment_sum_nonneg_of_actual_gaps
#print axioms N11Formalization.ActualCircularSectorClosure.anchor_sector_identity
