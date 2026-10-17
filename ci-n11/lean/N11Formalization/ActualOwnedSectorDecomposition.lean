import N11Formalization.ActualOwnershipSwitchWidths
import N11Formalization.ActualCircleSegmentAlgebra
import N11Formalization.ActualCenterRingShoelace
import N11Formalization.ActualSwitchWedgeArea
import N11Formalization.ActualOwnedChordGeometry

/-! Exact signed disk-area bookkeeping from ACTUAL nearest ownership.

The nine true ownership widths, not SOC cap endpoints, pay the sector
sum. Straight boundary wedges and ownership chord triangles are retained
as their exact signed determinants. Their cancellation with the accepted
selected-center shoelace yields an unconditional scalar identity for
every representative and its actual refinement. This is not yet a
Lebesgue-measure partition theorem or a metric class exclusion.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualOwnedSectorDecomposition
open ActualOwnershipSwitchWidths ActualCircleSegmentAlgebra
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryNineTies ActualBoundaryArcFrame ActualBoundaryCyclicOrder
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualTriangleShoelace
open FlashTiling

def switchPoint {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : Point :=
  circleMap (v.tie i).angle

theorem actual_switch_det_gap {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    det2 (switchPoint v i) (switchPoint v (nextRing i)) =
      Real.sin (switchGap v i) := by
  unfold switchPoint
  rw [← nextLift_circle v i,circleMap_det_segment]
  rfl

theorem actual_switch_sector_identity {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) :
    Real.pi =
      (∑ i : Fin 9, det2 (switchPoint v i) (switchPoint v (nextRing i)))/2 +
        ∑ i : Fin 9, segmentTerm (switchGap v i) := by
  have hs := segmentTerm_sum_widths (switchGap v) (actual_switch_gap_sum v)
  have he : (∑ i : Fin 9, det2 (switchPoint v i) (switchPoint v (nextRing i))) =
      ∑ i : Fin 9, Real.sin (switchGap v i) :=
    Finset.sum_congr rfl (fun i _ => actual_switch_det_gap v i)
  rw [he]
  linarith

theorem actual_owned_segment_positive {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    0 < segmentTerm (switchGap v i) := by
  unfold segmentTerm
  have hs := Real.sin_lt (actual_switch_gap_positive h hr v i)
  linarith

/-- Straight center-to-switch wedges and owner chord triangles cancel
their shared directed spokes, leaving the switch polygon boundary. -/
theorem cyclic_wedge_cancellation (C U : Fin 9 → Point) :
    (∑ i : Fin 9, orient (C i) (U i) (C (nextRing i))) +
        (∑ i : Fin 9, orient (C (nextRing i)) (U i) (U (nextRing i))) =
      (∑ i : Fin 9, det2 (U i) (U (nextRing i))) -
        (∑ i : Fin 9, det2 (C i) (C (nextRing i))) := by
  have hC : (∑ i : Fin 9, det2 (C (nextRing i)) (C i)) =
      -(∑ i : Fin 9, det2 (C i) (C (nextRing i))) := by
    simp only [ActualTriangleShoelace.det2_antisymm (C (nextRing _)) (C _),
      Finset.sum_neg_distrib]
  have hU : (∑ i : Fin 9, det2 (C (nextRing i)) (U i)) =
      -(∑ i : Fin 9, det2 (U i) (C (nextRing i))) := by
    simp only [ActualTriangleShoelace.det2_antisymm (C (nextRing _)) (U _),
      Finset.sum_neg_distrib]
  have hshift : (∑ i : Fin 9, det2 (U (nextRing i)) (C (nextRing i))) =
      -(∑ i : Fin 9, det2 (C i) (U i)) := by
    rw [show (∑ i : Fin 9, det2 (U (nextRing i)) (C (nextRing i))) =
        ∑ i : Fin 9, det2 (U i) (C i) from
      Equiv.sum_comp (Equiv.addRight (1 : Fin 9)) (fun i => det2 (U i) (C i))]
    simp only [ActualTriangleShoelace.det2_antisymm (U _) (C _),Finset.sum_neg_distrib]
  simp only [triangle_orient_shoelace,Finset.sum_add_distrib]
  rw [hC,hU,hshift]
  ring

/-- Productive signed decomposition with all actual selected center
triangles and genuine nearest-switch boundary pieces. No area identity
is an input to this theorem. -/
theorem actual_disk_signed_decomposition {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (R : Refinement c r) (v : NineTies c r) :
    Real.pi =
      (∑ A : R.Index, orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2)))/2 +
      (∑ i : Fin 9, orient (c (ringSite i)) (switchPoint v i) (c (nextSite i)))/2 +
      (∑ i : Fin 9, orient (c (nextSite i)) (switchPoint v i)
        (switchPoint v (nextRing i)))/2 +
      ∑ i : Fin 9, segmentTerm (switchGap v i) := by
  have hc := ActualCenterRingShoelace.actual_center_ring_shoelace h hr R
  have hw := cyclic_wedge_cancellation (fun i => c (ringSite i)) (switchPoint v)
  change (∑ i : Fin 9, orient (c (ringSite i)) (switchPoint v i) (c (nextSite i))) +
      (∑ i : Fin 9, orient (c (nextSite i)) (switchPoint v i)
        (switchPoint v (nextRing i))) =
    (∑ i : Fin 9, det2 (switchPoint v i) (switchPoint v (nextRing i))) -
      (∑ i : Fin 9, det2 (c (ringSite i)) (c (nextSite i))) at hw
  have hs := actual_switch_sector_identity v
  linarith

/-- The straight exterior wedges are exactly the positive switch atoms,
not merely formal signed placeholders. Owner chord triangles remain
nonnegative, including the flat endpoint of the closed metric domain. -/
theorem actual_disk_atom_decomposition {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (R : Refinement c r) (v : NineTies c r) :
    Real.pi =
      (∑ A : R.Index, orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2)))/2 +
      (∑ i : Fin 9, (ActualSwitchAtomAggregate.switchData h hr v i).chord *
        (ActualSwitchAtomAggregate.switchData h hr v i).offset) +
      (∑ i : Fin 9, orient (c (nextSite i)) (switchPoint v i)
        (switchPoint v (nextRing i)))/2 +
      ∑ i : Fin 9, segmentTerm (switchGap v i) := by
  have hw : (∑ i : Fin 9,
      orient (c (ringSite i)) (switchPoint v i) (c (nextSite i)))/2 =
        ∑ i : Fin 9, (ActualSwitchAtomAggregate.switchData h hr v i).chord *
          (ActualSwitchAtomAggregate.switchData h hr v i).offset := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    exact ActualSwitchWedgeArea.actual_switch_wedge_equals_atom h hr R i
      (v.tie i) (ActualSwitchAtomAggregate.switchData h hr v i)
  have hs := actual_disk_signed_decomposition h hr R v
  rwa [hw] at hs

theorem actual_owner_triangle_sum_nonneg {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) :
    0 ≤ (∑ i : Fin 9, orient (c (nextSite i)) (switchPoint v i)
      (switchPoint v (nextRing i)))/2 := by
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  exact ActualOwnedChordGeometry.actual_owned_chord_triangle_nonneg h hr v i

/-- Both the refinement and all nine nearest switches are produced
from the representative; no area or graph realization is a premise. -/
theorem actual_area_data_producer {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) :
    ∃ R : Refinement c r, ∃ v : NineTies c r,
      Real.pi =
        (∑ A : R.Index, orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2)))/2 +
        (∑ i : Fin 9, (ActualSwitchAtomAggregate.switchData h hr v i).chord *
          (ActualSwitchAtomAggregate.switchData h hr v i).offset) +
        (∑ i : Fin 9, orient (c (nextSite i)) (switchPoint v i)
          (switchPoint v (nextRing i)))/2 +
        ∑ i : Fin 9, segmentTerm (switchGap v i) := by
  obtain ⟨R⟩ := actual_refinement h hr
  obtain ⟨v⟩ := nineTies_of_cover h.cover hr h.labels h.midpoint_order
  exact ⟨R,v,actual_disk_atom_decomposition h hr R v⟩

end N11Formalization.ActualOwnedSectorDecomposition
#check @N11Formalization.ActualOwnedSectorDecomposition.actual_disk_signed_decomposition
#check @N11Formalization.ActualOwnedSectorDecomposition.actual_disk_atom_decomposition
#check @N11Formalization.ActualOwnedSectorDecomposition.actual_area_data_producer
#print axioms N11Formalization.ActualOwnedSectorDecomposition.actual_disk_signed_decomposition
#print axioms N11Formalization.ActualOwnedSectorDecomposition.actual_disk_atom_decomposition
#print axioms N11Formalization.ActualOwnedSectorDecomposition.actual_area_data_producer
