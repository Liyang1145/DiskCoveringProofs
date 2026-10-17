import N11Formalization.ActualBoundaryOverlapAdjacency
import N11Formalization.ActualCoverStructuralReduction
import N11Formalization.FlashTilingFan

/-! Real adjacent ring radial determinants are strictly positive.
True cap overlap bounds the cyclic midpoint gap by two actual halfwidths;
no ring-polygon convexity or global disk assertion is needed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRingShoelacePositive
open ActualCoverStructuralReduction ActualRingDirectionOrder ActualBoundaryArcFrame
open ActualBoundaryCyclicOrder ActualBoundaryOverlapAdjacency FlashTiling

def directionGap (c : Fin 11 → Point) (i : Fin 9) : ℝ :=
  arcCenter c (nextRing i) (nextShift i)-midpointAngle c i

theorem actual_direction_gap_bounds {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) :
    0 < directionGap c i ∧ directionGap c i < Real.pi := by
  have hpos := next_center_gt h.midpoint_order i
  have hover := neighbor_overlap h.cover hr h.labels h.midpoint_order i
  have hI := halfWidth_le_small h.cover hr h.labels i
  have hN := halfWidth_le_small h.cover hr h.labels (nextRing i)
  change arcCenter c i 0 < arcCenter c (nextRing i) (nextShift i) at hpos
  have h0 : arcCenter c i 0=midpointAngle c i := by simp [arcCenter]
  rw [h0] at hpos
  change arcCenter c (nextRing i) (nextShift i)-halfWidth c r (nextRing i) ≤
    arcCenter c i 0+halfWidth c r i at hover
  rw [h0] at hover
  unfold directionGap
  constructor <;> linarith [Real.pi_pos]

theorem det_circleMap (a b : ℝ) : det2 (circleMap a) (circleMap b)=Real.sin (b-a) := by
  unfold det2
  change Real.cos a*Real.sin b-Real.sin a*Real.cos b=Real.sin (b-a)
  rw [Real.sin_sub]
  ring

theorem actual_ring_det_positive {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) :
    0 < det2 (c (ringSite i)) (c (ringSite (nextRing i))) := by
  have hne (j : Fin 9) : c (ringSite j) ≠ 0 :=
    ActualInwardNormalization.touching_ne_zero (by linarith : r<1) (h.labels.ring_meets j.isLt)
  have hsite (j : Fin 9) :
      c (ringSite j)=‖c (ringSite j)‖ • circleMap (midpointAngle c j) := by
    rw [midpoint_direction h.cover hr h.labels j]
    exact self_eq_norm_smul_centerDir (hne j)
  have hg := actual_direction_gap_bounds h hr i
  have hs := Real.sin_pos_of_pos_of_lt_pi hg.1 hg.2
  have heq : det2 (c (ringSite i)) (c (ringSite (nextRing i))) =
      ‖c (ringSite i)‖*‖c (ringSite (nextRing i))‖*Real.sin (directionGap c i) := by
    conv_lhs => rw [hsite i,hsite (nextRing i)]
    rw [det2_smul_left,det2_smul]
    rw [← circleMap_periodic (midpointAngle c (nextRing i)) (nextShift i),det_circleMap]
    change ‖c (ringSite i)‖*(‖c (ringSite (nextRing i))‖*
      Real.sin (directionGap c i)) =
      ‖c (ringSite i)‖*‖c (ringSite (nextRing i))‖*Real.sin (directionGap c i)
    ring
  rw [heq]
  exact mul_pos (mul_pos (norm_pos_iff.mpr (hne i))
    (norm_pos_iff.mpr (hne (nextRing i)))) hs

theorem actual_ring_shoelace_positive {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) :
    0 < ∑ i : Fin 9, det2 (c (ringSite i)) (c (ringSite (nextRing i))) := by
  exact Finset.sum_pos (fun i _ => actual_ring_det_positive h hr i) Finset.univ_nonempty

end N11Formalization.ActualRingShoelacePositive
#check @N11Formalization.ActualRingShoelacePositive.actual_ring_shoelace_positive
#print axioms N11Formalization.ActualRingShoelacePositive.actual_ring_det_positive
#print axioms N11Formalization.ActualRingShoelacePositive.actual_ring_shoelace_positive
