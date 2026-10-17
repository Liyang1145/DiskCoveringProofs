import N11Formalization.ActualBoundaryOwnershipIntervals
import N11Formalization.ActualBoundaryNineTies

/-! Actual nearest ownership endpoints and widths.

The endpoints here are genuine `NineTies`, NOT the SOC cap-right anchors.
No ordering of switches, ownership interval endpoints, or sum of widths
is assumed: these are produced from the real cap lifts.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualOwnershipSwitchWidths
open ActualCoverStructuralReduction ActualBoundaryNineTies ActualBoundaryNeighborTies
open ActualBoundaryArcFrame ActualBoundaryArcOrder ActualBoundaryCyclicOrder
open ActualRingDirectionOrder ActualBoundaryOwnershipIntervals ActualVoronoiCells

def nextLift {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  (v.tie (nextRing i)).angle + (nextShift i : ℝ)*period

/-- Width at index i is owned by ring i+1. -/
def switchGap {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ :=
  nextLift v i - (v.tie i).angle

theorem nextLift_mem {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    nextLift v i ∈ Arc c r (nextRing i) (nextShift i) ∧
      nextLift v i ∈ Arc c r (nextRing (nextRing i))
        (nextShift (nextRing i)+nextShift i) := by
  constructor
  · simpa [nextLift] using
      (mem_shift_copy (n := nextShift i) (v.tie (nextRing i)).in_overlap.1)
  · simpa [nextLift,Int.cast_add] using
      (mem_shift_copy (n := nextShift (nextRing i)+nextShift i)
        (v.tie (nextRing i)).in_overlap.2)

theorem successive_centers {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (i : Fin 9) :
    arcCenter c (nextRing i) (nextShift i) <
      arcCenter c (nextRing (nextRing i))
        (nextShift (nextRing i)+nextShift i) := by
  have hh := next_center_gt h.midpoint_order (nextRing i)
  simp only [arcCenter,Int.cast_zero,zero_mul,add_zero,Int.cast_add] at hh ⊢
  nlinarith

/-- Strict cyclic order of actual nearest switches. Reversal would put
the preceding switch in three distinct real caps. -/
theorem actual_switch_gap_positive {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    0 < switchGap v i := by
  have hn := nextLift_mem v i
  have he := endpoints_ordered h.cover hr h.labels (next_ne (nextRing i))
    (successive_centers h i)
  have hfar : i ≠ nextRing (nextRing i) := (next_next_ne i).symm
  by_contra hnot
  have hrev : nextLift v i ≤ (v.tie i).angle := by
    dsimp [switchGap] at hnot
    linarith
  have hthird : (v.tie i).angle ∈ Arc c r (nextRing (nextRing i))
      (nextShift (nextRing i)+nextShift i) :=
    ⟨hn.2.1.trans hrev,(v.tie i).in_overlap.2.2.trans he.2.le⟩
  exact no_triple_lift h.cover hr h.labels (next_ne i) hfar (next_ne (nextRing i))
    0 (nextShift i) (nextShift (nextRing i)+nextShift i)
    ⟨(v.tie i).angle,(v.tie i).in_overlap.1,(v.tie i).in_overlap.2,hthird⟩

theorem actual_switch_gap_le_two_halfWidth {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    switchGap v i ≤ 2*halfWidth c r (nextRing i) := by
  have ha := (v.tie i).in_overlap.2.1
  have hb := (nextLift_mem v i).1.2
  change arcCenter c (nextRing i) (nextShift i)-halfWidth c r (nextRing i) ≤
    (v.tie i).angle at ha
  change nextLift v i ≤
    arcCenter c (nextRing i) (nextShift i)+halfWidth c r (nextRing i) at hb
  dsimp [switchGap]
  linarith

theorem actual_switch_gap_le_two_arcsin {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    switchGap v i ≤ 2*Real.arcsin r := by
  have hne := ActualInwardNormalization.touching_ne_zero
    (by linarith : r < 1)
    (h.labels.ring_meets (i := ringSite (nextRing i)) (nextRing i).isLt)
  have hw := capHalfWidth_le_arcsin hne (Covers.nonneg h.cover) (by linarith : r < 1)
  change halfWidth c r (nextRing i) ≤ Real.arcsin r at hw
  linarith [actual_switch_gap_le_two_halfWidth v i]

theorem actual_switch_gap_sum {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) :
    ∑ i : Fin 9, switchGap v i = 2*Real.pi := by
  have hp : (∑ i : Fin 9, (v.tie (nextRing i)).angle) =
      ∑ i : Fin 9, (v.tie i).angle :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin 9)) (fun i => (v.tie i).angle)
  have hs : (∑ i : Fin 9, (nextShift i : ℝ)*period) = period := by
    simp [nextShift]
  simp only [switchGap,nextLift,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [hp,hs]
  simp [period]

theorem actual_switch_gap_floor {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (i : Fin 9) :
    2*Real.pi - 16*Real.arcsin (19/50) ≤ switchGap v i := by
  classical
  have hu (j : Fin 9) : switchGap v j ≤ 2*Real.arcsin (19/50) := by
    have hj := actual_switch_gap_le_two_arcsin h hr v j
    have ha := Real.arcsin_le_arcsin hr.le
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ.erase i) (fun j _ => hu j)
  have hc : (Finset.univ.erase i : Finset (Fin 9)).card=8 := by simp
  simp only [Finset.sum_const,nsmul_eq_mul,hc] at hs
  have he := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 9)))
    (f := switchGap v) (Finset.mem_univ i)
  rw [actual_switch_gap_sum] at he
  linarith

theorem nextLift_circle {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    circleMap (nextLift v i) = circleMap (v.tie (nextRing i)).angle :=
  circleMap_periodic _ _

theorem switch_endpoints_mem_weak {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) :
    (v.tie i).angle ∈ WeakLift c r (nextRing i) (nextShift i) ∧
      nextLift v i ∈ WeakLift c r (nextRing i) (nextShift i) := by
  refine ⟨⟨(v.tie i).in_overlap.2,(v.tie i).nearest.2⟩,?_,?_⟩
  · exact (nextLift_mem v i).1
  · rw [nextLift_circle]
    exact (v.tie (nextRing i)).nearest.1

/-- The actual weak nearest region in this periodic cap copy is EXACTLY
the interval between its incoming and outgoing genuine switches.
Both closed endpoints are retained; the interior is strictly nearest. -/
theorem actual_weakLift_eq_switch_interval
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) (i : Fin 9) :
    WeakLift c r (nextRing i) (nextShift i) =
      Set.Icc (v.tie i).angle (nextLift v i) := by
  have hend := switch_endpoints_mem_weak v i
  have hgap := actual_switch_gap_positive h hr v i
  have hlt : (v.tie i).angle < nextLift v i := by
    dsimp [switchGap] at hgap
    linarith
  ext t
  constructor
  · intro ht
    constructor
    · by_contra hnot
      have htl : t < (v.tie i).angle := lt_of_not_ge hnot
      have hs := Representative.strict_between_weak h hr ht hend.2 htl hlt
      have hij : ringSite i ≠ ringSite (nextRing i) :=
        fun he => next_ne i (ringSite_inj he)
      have hstrict := hs (ringSite i) hij
      have hweak := (v.tie i).nearest.1 (ringSite (nextRing i))
      linarith
    · by_contra hnot
      have hut : nextLift v i < t := lt_of_not_ge hnot
      have hs := Representative.strict_between_weak h hr hend.1 ht hlt hut
      have hij : ringSite (nextRing (nextRing i)) ≠ ringSite (nextRing i) :=
        fun he => next_ne (nextRing i) (ringSite_inj he).symm
      have hstrict := hs (ringSite (nextRing (nextRing i))) hij
      rw [nextLift_circle] at hstrict
      have hweak := (v.tie (nextRing i)).nearest.2 (ringSite (nextRing i))
      linarith
  · intro ht
    exact (Representative.weakLift_ordConnected h hr (nextRing i) (nextShift i)).out'
      hend.1 hend.2 ht

theorem actual_switch_interval_strict_interior
    {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) (i : Fin 9) {t : ℝ}
    (ht : t ∈ Set.Ioo (v.tie i).angle (nextLift v i)) :
    circleMap t ∈ StrictCell c (ringSite (nextRing i)) :=
  Representative.strict_between_weak h hr
    (switch_endpoints_mem_weak v i).1 (switch_endpoints_mem_weak v i).2 ht.1 ht.2

end N11Formalization.ActualOwnershipSwitchWidths
#check @N11Formalization.ActualOwnershipSwitchWidths.actual_switch_gap_positive
#check @N11Formalization.ActualOwnershipSwitchWidths.actual_switch_gap_sum
#check @N11Formalization.ActualOwnershipSwitchWidths.actual_weakLift_eq_switch_interval
#print axioms N11Formalization.ActualOwnershipSwitchWidths.actual_switch_gap_positive
#print axioms N11Formalization.ActualOwnershipSwitchWidths.actual_switch_gap_sum
#print axioms N11Formalization.ActualOwnershipSwitchWidths.actual_weakLift_eq_switch_interval
