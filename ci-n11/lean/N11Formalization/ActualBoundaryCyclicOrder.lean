import N11Formalization.ActualBoundaryArcOrder

/-! Actual cyclic neighbors of sorted cap midpoints, including the wrap.
The full real-line cover produces a nonempty CLOSED overlap for every
neighbor pair. No overlap, switch or lifted cyclic-order premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryCyclicOrder
open DSHTopologyInterior ActualRingDirectionOrder ActualBoundaryArcFrame
open ActualBoundaryArcOrder

def nextRing (i : Fin 9) : Fin 9 := i+1
def nextShift (i : Fin 9) : ℤ := if i = 8 then 1 else 0

theorem next_ne (i : Fin 9) : i ≠ nextRing i := by
  fin_cases i <;> decide

theorem next_val {i : Fin 9} (hi : i ≠ 8) : (nextRing i).val = i.val+1 := by
  have hv := i.isLt
  have h8 : i.val ≠ 8 := fun h => hi (Fin.ext h)
  simp only [nextRing,Fin.val_add,Fin.val_one]
  omega

theorem midpoint_bounds (c : Fin 11 → Point) (i : Fin 9) :
    -Real.pi < midpointAngle c i ∧ midpointAngle c i ≤ Real.pi :=
  circleAngle_mem_Ioc _

theorem center_zero (c : Fin 11 → Point) (i : Fin 9) :
    arcCenter c i 0 = midpointAngle c i := by simp [arcCenter]

theorem next_center_gt {c : Fin 11 → Point}
    (ho : StrictMono (midpointAngle c)) (i : Fin 9) :
    arcCenter c i 0 < arcCenter c (nextRing i) (nextShift i) := by
  by_cases hi : i = 8
  · subst i
    have hb0 := midpoint_bounds c 0
    have hb8 := midpoint_bounds c 8
    rw [show nextRing 8 = 0 by decide]
    norm_num [nextShift,arcCenter,period]
    linarith
  · have hlt : i < nextRing i := by
      change i.val < (nextRing i).val
      rw [next_val hi]
      omega
    simpa [nextShift,hi,center_zero] using ho hlt

/-- No periodic midpoint lies strictly between two sorted cyclic neighbors. -/
theorem center_dichotomy {c : Fin 11 → Point}
    (ho : StrictMono (midpointAngle c)) (i k : Fin 9) (n : ℤ) :
    arcCenter c k n ≤ arcCenter c i 0 ∨
      arcCenter c (nextRing i) (nextShift i) ≤ arcCenter c k n := by
  have hbi := midpoint_bounds c i
  have hbk := midpoint_bounds c k
  have hbn := midpoint_bounds c (nextRing i)
  have hp := Real.pi_pos
  rcases (show n ≤ -1 ∨ n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with hn | hn | hn | hn
  · left
    have hnR : (n:ℝ) ≤ -1 := by exact_mod_cast hn
    simp only [arcCenter,Int.cast_zero,zero_mul,add_zero,period]
    nlinarith
  · subst n
    by_cases hki : k ≤ i
    · left
      simpa only [center_zero] using ho.monotone hki
    · right
      have h8 : i ≠ 8 := by
        intro hi
        subst i
        have hv := k.isLt
        change ¬ k.val ≤ 8 at hki
        omega
      have hnk : nextRing i ≤ k := by
        change (nextRing i).val ≤ k.val
        rw [next_val h8]
        change ¬ k.val ≤ i.val at hki
        omega
      simpa [nextShift,h8,center_zero] using ho.monotone hnk
  · subst n
    right
    by_cases hi : i = 8
    · subst i
      have hk : (0 : Fin 9) ≤ k := by exact Fin.zero_le k
      have hh := ho.monotone hk
      rw [show nextRing 8 = 0 by decide]
      norm_num [nextShift,arcCenter,period]
      linarith
    · simp only [nextShift,if_neg hi,arcCenter,Int.cast_zero,zero_mul,add_zero,
        Int.cast_one,one_mul,period]
      linarith
  · right
    have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hsR : ((nextShift i):ℝ) ≤ 1 := by
      unfold nextShift
      split_ifs <;> norm_num
    simp only [arcCenter,period]
    nlinarith

theorem endpoints_monotone {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j : Fin 9} {n m : ℤ} (hcenter : arcCenter c i n ≤ arcCenter c j m) :
    leftEnd c r i n ≤ leftEnd c r j m ∧
      rightEnd c r i n ≤ rightEnd c r j m := by
  by_cases hij : i = j
  · subst j
    dsimp [leftEnd,rightEnd]
    constructor <;> linarith
  · have hne := copy_centers_ne hc hr hR hij n m
    have he := endpoints_ordered hc hr hR hij (lt_of_le_of_ne hcenter hne)
    exact ⟨he.1.le,he.2.le⟩

theorem neighbor_overlap {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) (i : Fin 9) :
    leftEnd c r (nextRing i) (nextShift i) ≤ rightEnd c r i 0 := by
  by_contra hnot
  have hgap := lt_of_not_ge hnot
  let t := (rightEnd c r i 0+leftEnd c r (nextRing i) (nextShift i))/2
  obtain ⟨k,n,ht⟩ := real_interval_cover hc hr hR t
  rcases center_dichotomy ho i k n with hbefore | hafter
  · have he := (endpoints_monotone hc hr hR hbefore).2
    have hb := ht.2
    dsimp [t] at hb
    linarith
  · have he := (endpoints_monotone hc hr hR hafter).1
    have hb := ht.1
    dsimp [t] at hb
    linarith

/-- The entire overlap is a genuine interval contained in both cap copies. -/
theorem overlap_interval {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) (i : Fin 9) :
    Set.Icc (leftEnd c r (nextRing i) (nextShift i)) (rightEnd c r i 0) =
      Arc c r i 0 ∩ Arc c r (nextRing i) (nextShift i) := by
  have he := endpoints_ordered hc hr hR (next_ne i) (next_center_gt ho i)
  ext t
  constructor
  · intro ht
    exact ⟨⟨he.1.le.trans ht.1,ht.2⟩,⟨ht.1,ht.2.trans he.2.le⟩⟩
  · intro ht
    exact ⟨ht.2.1,ht.1.2⟩

end N11Formalization.ActualBoundaryCyclicOrder
#check @N11Formalization.ActualBoundaryCyclicOrder.neighbor_overlap
#print axioms N11Formalization.ActualBoundaryCyclicOrder.neighbor_overlap
