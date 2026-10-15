import N11Formalization.ActualCapClusterCapacity
import N11Formalization.ActualPeriodicMidpointOrder

/-! ACTUAL ring disks at cyclic distance3/4 are disjoint in the whole plane.
No Delaunay/topology premise is used: ordered cap cluster plus mixed circle
capacity prove locality, including artificial common-point refinement edges. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRingLocality
open DSHTopologyInterior ActualRingDirectionOrder ActualBoundaryArcFrame
open ActualBoundaryArcOrder ActualBoundaryCyclicOrder ActualCapClusterLift
open ActualCapClusterCapacity ActualPeriodicMidpointOrder

def Far (i j : Fin 9) : Prop := 3 ≤ (j-i).val ∧ 3 ≤ (i-j).val

theorem Far.symm {i j : Fin 9} (h : Far i j) : Far j i := ⟨h.2,h.1⟩

theorem Far.ne {i j : Fin 9} (h : Far i j) : i ≠ j := by
  intro he
  subst j
  norm_num [Far] at h

theorem Far.base_gap {i j : Fin 9} (h : Far i j) (hij : i ≤ j) :
    i.val+3 ≤ j.val := by
  have hh := h.1
  rw [Fin.sub_val_of_le hij] at hh
  omega

theorem Far.wrap_gap {i j : Fin 9} (h : Far i j) :
    i.val+3 ≤ j.val+9 := by
  have hv := i.isLt
  have hjv := j.isLt
  by_cases hij : i ≤ j
  · have hg := h.base_gap hij
    omega
  · have hh := h.1
    have he := Fin.intCast_val_sub_eq_sub_add_ite j i
    simp only [if_neg hij] at he
    omega

theorem no_long_cluster {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) {p : Point} (hp : p ≠ 0)
    (hm : ∃ y : Point, ‖y‖ = 1 ∧ dist y p ≤ 2*r)
    {a b : ℕ} (hab : a+3 ≤ b) {m : ℤ}
    (hA : Arc c r (slot a) (turn a) ⊆ BigArc p r m)
    (hB : Arc c r (slot b) (turn b) ⊆ BigArc p r m) : False := by
  apply no_four_copies_in_big hc hr hR hp hm (fourSlots a) (fourSlots_card a)
  intro i hi
  obtain ⟨q,_,hqi⟩ := Finset.mem_image.mp hi
  refine ⟨turn (a+q.val),m,?_⟩
  rw [← hqi]
  have hq := q.isLt
  have hleft : liftMidpoint c a ≤ liftMidpoint c (a+q.val) :=
    (liftMidpoint_strictMono ho).monotone (by omega)
  have hright : liftMidpoint c (a+q.val) ≤ liftMidpoint c b :=
    (liftMidpoint_strictMono ho).monotone (by omega)
  have hendsA := ends_in_big hA
  have hendsB := ends_in_big hB
  have heA := ActualBoundaryCyclicOrder.endpoints_monotone hc hr hR hleft
  have heB := ActualBoundaryCyclicOrder.endpoints_monotone hc hr hR hright
  intro t ht
  exact ⟨hendsA.1.trans (heA.1.trans ht.1),ht.2.trans (heB.2.trans hendsB.2)⟩

theorem circle_meets_big_of_ring {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {p : Point} {i : Fin 9} (hpi : dist p (c (ringSite i)) ≤ r) :
    ∃ x : Point, ‖x‖ = 1 ∧ dist x p ≤ 2*r := by
  obtain ⟨x,hx,hxi⟩ := hR.ring_meets (i := ringSite i) i.isLt
  refine ⟨x,hx,?_⟩
  have ht := dist_triangle x (c (ringSite i)) p
  rw [dist_comm (c (ringSite i)) p] at ht
  linarith

theorem disjoint_of_far {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) {i j : Fin 9} (hfar : Far i j)
    {p : Point} (hpi : dist p (c (ringSite i)) ≤ r)
    (hpj : dist p (c (ringSite j)) ≤ r) : False := by
  obtain ⟨hp,m,hI⟩ := copy_in_one_big_copy hc hr hR hpi 0
  obtain ⟨_,k,hJ⟩ := copy_in_one_big_copy hc hr hR hpj 0
  have hm := circle_meets_big_of_ring hc hr hR hpi
  have hAligned := (align_big_copies hI hJ).2
  rcases aligned_shift_range hc hr hp hI hAligned with hn | hn | hn
  · rw [hn] at hAligned
    have hShiftI := shift_subset_big (n := (1:ℤ)) hI
    have hShiftJ : Arc c r j 0 ⊆ BigArc p r (m+1) := by
      intro t ht
      have hs := mem_shift_copy (n := (-1:ℤ)) ht
      have hb := BigArc.shift (n := (1:ℤ)) (hAligned hs)
      norm_num at hb
      exact hb
    apply no_long_cluster hc hr hR ho hp hm (hfar.symm.wrap_gap)
    · simpa only [slot_at,turn_at] using hShiftJ
    · change Arc c r (slot (i.val+9*1)) (turn (i.val+9*1)) ⊆ BigArc p r (m+1)
      rw [slot_period,turn_period,slot_at,turn_at]
      norm_num
      exact hShiftI
  · rw [hn] at hAligned
    rcases le_total i j with hij | hji
    · apply no_long_cluster hc hr hR ho hp hm (hfar.base_gap hij)
      · simpa only [slot_at,turn_at] using hI
      · simpa only [slot_at,turn_at] using hAligned
    · apply no_long_cluster hc hr hR ho hp hm (hfar.symm.base_gap hji)
      · simpa only [slot_at,turn_at] using hAligned
      · simpa only [slot_at,turn_at] using hI
  · rw [hn] at hAligned
    apply no_long_cluster hc hr hR ho hp hm hfar.wrap_gap
    · simpa only [slot_at,turn_at] using hI
    · change Arc c r (slot (j.val+9*1)) (turn (j.val+9*1)) ⊆ BigArc p r m
      rw [slot_period,turn_period,slot_at,turn_at]
      norm_num
      exact hAligned

theorem intersection_local {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) {i j : Fin 9} {p : Point}
    (hpi : dist p (c (ringSite i)) ≤ r) (hpj : dist p (c (ringSite j)) ≤ r) :
    (j-i).val ≤ 2 ∨ (i-j).val ≤ 2 := by
  by_contra hnot
  have hfar : Far i j := by dsimp [Far]; omega
  exact disjoint_of_far hc hr hR ho hfar hpi hpj

end N11Formalization.ActualRingLocality
#check @N11Formalization.ActualRingLocality.disjoint_of_far
#check @N11Formalization.ActualRingLocality.intersection_local
#print axioms N11Formalization.ActualRingLocality.intersection_local
