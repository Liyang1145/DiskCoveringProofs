import N11Formalization.ActualBoundaryCyclicOrder

/-! Actual cap overlap implies cyclic adjacency in the sorted direction order.
All periodic copies, wrap, closed endpoints and unequal cap widths are covered.
This is not a triangulation or a canonical hub-fan assertion. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryOverlapAdjacency
open DSHTopologyInterior ActualRingDirectionOrder ActualBoundaryArcFrame
open ActualBoundaryArcOrder ActualBoundaryCyclicOrder

theorem halfWidth_le_small {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) (i : Fin 9) :
    halfWidth c r i < Real.pi/8 := by
  have hne := ActualInwardNormalization.touching_ne_zero (by linarith : r < 1)
    (hR.ring_meets (i := ringSite i) i.isLt)
  exact (capHalfWidth_le_arcsin hne (Covers.nonneg hc) (by linarith)).trans_lt
    ((Real.arcsin_le_arcsin hr.le).trans_lt arcsin_R0_lt_pi_div_eight)

theorem overlap_zero_lt {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) {i j : Fin 9} (hij : i < j)
    {t : ℝ} (hi : t ∈ Arc c r i 0) (hj : t ∈ Arc c r j 0) :
    j = nextRing i := by
  have hi8 : i ≠ 8 := by
    intro he
    subst i
    have hv := j.isLt
    change 8 < j.val at hij
    omega
  by_contra hnot
  have hnextj : nextRing i < j := by
    have hn := next_val hi8
    have hnv : (nextRing i).val ≠ j.val := fun he => hnot (Fin.ext he).symm
    change i.val < j.val at hij
    change (nextRing i).val < j.val
    omega
  have hijn : i ≠ nextRing i := next_ne i
  have hij' : i ≠ j := ne_of_lt hij
  have hnj : nextRing i ≠ j := ne_of_lt hnextj
  have hcenter1 : arcCenter c i 0 < arcCenter c (nextRing i) 0 := by
    simpa only [center_zero] using ho (show i < nextRing i by
      change i.val < (nextRing i).val; rw [next_val hi8]; omega)
  have hcenter2 : arcCenter c (nextRing i) 0 < arcCenter c j 0 := by
    simpa only [center_zero] using ho hnextj
  exact no_skipped_midpoint_overlap hc hr hR hijn hij' hnj hcenter1 hcenter2 ⟨t,hi,hj⟩

theorem overlap_one {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) {i j : Fin 9} (hij : i ≠ j)
    {t : ℝ} (hi : t ∈ Arc c r i 0) (hj : t ∈ Arc c r j 1) :
    i = 8 ∧ j = 0 := by
  have hwi := halfWidth_le_small hc hr hR i
  have hwj := halfWidth_le_small hc hr hR j
  have hji : j < i := by
    by_contra hnot
    have hm := ho.monotone (le_of_not_gt hnot)
    have hI := hi.2
    have hJ := hj.1
    simp only [leftEnd,rightEnd,arcCenter,period,Int.cast_zero,Int.cast_one,
      zero_mul,one_mul,add_zero] at hI hJ
    linarith [Real.pi_pos]
  have hi8 : i = 8 := by
    by_contra hnot
    have hnval := next_val hnot
    have hin : i < nextRing i := by change i.val < (nextRing i).val; omega
    have hjn : j < nextRing i := hji.trans hin
    have hci : arcCenter c i 0 < arcCenter c (nextRing i) 0 := by
      simpa only [center_zero] using ho hin
    have hcn : arcCenter c (nextRing i) 0 < arcCenter c j 1 := by
      have hbN := midpoint_bounds c (nextRing i)
      have hbJ := midpoint_bounds c j
      simp [arcCenter,period]
      linarith
    exact no_skipped_midpoint_overlap hc hr hR (ne_of_lt hin) hij (ne_of_gt hjn)
      hci hcn ⟨t,hi,hj⟩
  have hj0 : j = 0 := by
    by_contra hnot
    have h0j : (0 : Fin 9) < j := by
      have hz : j.val ≠ 0 := fun he => hnot (Fin.ext he)
      change 0 < j.val
      omega
    have hi0 : i ≠ 0 := by rw [hi8]; decide
    have hci : arcCenter c i 0 < arcCenter c 0 1 := by
      rw [hi8]
      have hn := next_center_gt ho (8 : Fin 9)
      rw [show nextRing 8 = 0 by decide] at hn
      simpa [nextShift] using hn
    have hcj : arcCenter c 0 1 < arcCenter c j 1 := by
      have hm := ho h0j
      dsimp [arcCenter]
      linarith
    exact no_skipped_midpoint_overlap hc hr hR hi0 hij (ne_of_lt h0j)
      hci hcj ⟨t,hi,hj⟩
  exact ⟨hi8,hj0⟩

theorem shift_range_of_overlap {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j : Fin 9} {n : ℤ} {t : ℝ}
    (hi : t ∈ Arc c r i 0) (hj : t ∈ Arc c r j n) :
    n = -1 ∨ n = 0 ∨ n = 1 := by
  have hwi := halfWidth_le_small hc hr hR i
  have hwj := halfWidth_le_small hc hr hR j
  have hbi := midpoint_bounds c i
  have hbj := midpoint_bounds c j
  have hp := Real.pi_pos
  by_contra hnot
  have hn : n ≤ -2 ∨ 2 ≤ n := by omega
  rcases hn with hn | hn
  · have hnR : (n:ℝ) ≤ -2 := by exact_mod_cast hn
    have hI := hi.1
    have hJ := hj.2
    simp only [leftEnd,rightEnd,arcCenter,period,Int.cast_zero,zero_mul,add_zero] at hI hJ
    nlinarith
  · have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hI := hi.2
    have hJ := hj.1
    simp only [leftEnd,rightEnd,arcCenter,period,Int.cast_zero,zero_mul,add_zero] at hI hJ
    nlinarith

theorem overlap_adjacent_base {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) {i j : Fin 9} (hij : i ≠ j)
    {n : ℤ} {t : ℝ} (hi : t ∈ Arc c r i 0) (hj : t ∈ Arc c r j n) :
    j = nextRing i ∨ i = nextRing j := by
  rcases shift_range_of_overlap hc hr hR hi hj with hn | hn | hn
  · subst n
    have hI := mem_shift_copy (n := (1 : ℤ)) hi
    have hJ := mem_shift_copy (n := (0 : ℤ)) hj
    norm_num at hI hJ
    obtain ⟨hj8,hi0⟩ := overlap_one hc hr hR ho hij.symm hJ hI
    right
    rw [hj8,hi0]
    decide
  · subst n
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact Or.inl (overlap_zero_lt hc hr hR ho hij hi hj)
    · exact Or.inr (overlap_zero_lt hc hr hR ho hji hj hi)
  · subst n
    obtain ⟨hi8,hj0⟩ := overlap_one hc hr hR ho hij hi hj
    left
    rw [hi8,hj0]
    decide

theorem overlap_adjacent {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) {i j : Fin 9} (hij : i ≠ j)
    {n m : ℤ} {t : ℝ} (hi : t ∈ Arc c r i n) (hj : t ∈ Arc c r j m) :
    j = nextRing i ∨ i = nextRing j := by
  have hI := mem_shift_copy (n := (0 : ℤ)) hi
  have hJ := mem_shift_copy (n := m-n) hj
  have he : ((m-n-m:ℤ):ℝ) = ((0-n:ℤ):ℝ) := by push_cast; ring
  rw [he] at hJ
  exact overlap_adjacent_base hc hr hR ho hij hI hJ

end N11Formalization.ActualBoundaryOverlapAdjacency
#check @N11Formalization.ActualBoundaryOverlapAdjacency.overlap_adjacent
#print axioms N11Formalization.ActualBoundaryOverlapAdjacency.overlap_adjacent
