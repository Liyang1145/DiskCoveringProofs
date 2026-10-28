import N11Formalization.ActualBoundaryArcFrame

/-! Real closed-interval combinatorics paid on ACTUAL periodic caps:
strict endpoint order, no skipped midpoint overlap, and no triple circle
coverage. No cyclic-arc-topology premise is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryArcOrder
open DSHTopologyInterior ActualRingDirectionOrder ActualBoundaryArcFrame

theorem copy_not_subset {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j : Fin 9} (hij : i ≠ j) (n m : ℤ) :
    ¬ Arc c r i n ⊆ Arc c r j m := by
  intro hsub
  obtain ⟨t,ht,hprivate⟩ := private_in_copy hc hr hR i n
  exact hprivate j hij.symm m (hsub ht)

theorem copy_not_subset_union {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j k : Fin 9} (hij : i ≠ j) (hik : i ≠ k) (n m p : ℤ) :
    ¬ Arc c r i n ⊆ Arc c r j m ∪ Arc c r k p := by
  intro hsub
  obtain ⟨t,ht,hprivate⟩ := private_in_copy hc hr hR i n
  rcases hsub ht with h | h
  · exact hprivate j hij.symm m h
  · exact hprivate k hik.symm p h

theorem copy_centers_ne {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j : Fin 9} (hij : i ≠ j) (n m : ℤ) :
    arcCenter c i n ≠ arcCenter c j m := by
  intro heq
  rcases le_total (halfWidth c r i) (halfWidth c r j) with hwidth | hwidth
  · apply copy_not_subset hc hr hR hij n m
    intro t ht
    change leftEnd c r i n ≤ t ∧ t ≤ rightEnd c r i n at ht
    change leftEnd c r j m ≤ t ∧ t ≤ rightEnd c r j m
    dsimp [leftEnd,rightEnd] at ht ⊢
    rw [heq] at ht
    constructor <;> linarith [ht.1,ht.2]
  · apply copy_not_subset hc hr hR hij.symm m n
    intro t ht
    change leftEnd c r j m ≤ t ∧ t ≤ rightEnd c r j m at ht
    change leftEnd c r i n ≤ t ∧ t ≤ rightEnd c r i n
    dsimp [leftEnd,rightEnd] at ht ⊢
    rw [heq]
    constructor <;> linarith [ht.1,ht.2]

theorem endpoints_ordered {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j : Fin 9} (hij : i ≠ j) {n m : ℤ}
    (hcenter : arcCenter c i n < arcCenter c j m) :
    leftEnd c r i n < leftEnd c r j m ∧ rightEnd c r i n < rightEnd c r j m := by
  constructor
  · by_contra hnot
    have hL : leftEnd c r j m ≤ leftEnd c r i n := le_of_not_gt hnot
    have hR' : rightEnd c r i n ≤ rightEnd c r j m := by
      dsimp [leftEnd,rightEnd] at hL ⊢
      linarith
    apply copy_not_subset hc hr hR hij n m
    intro t ht
    exact ⟨hL.trans ht.1,ht.2.trans hR'⟩
  · by_contra hnot
    have hR' : rightEnd c r j m ≤ rightEnd c r i n := le_of_not_gt hnot
    have hL : leftEnd c r i n ≤ leftEnd c r j m := by
      dsimp [leftEnd,rightEnd] at hR' ⊢
      linarith
    apply copy_not_subset hc hr hR hij.symm m n
    intro t ht
    exact ⟨hL.trans ht.1,ht.2.trans hR'⟩

/-- Non-neighbor overlap would cover a whole middle cap by the two end
caps, contradicting its ACTUAL private point. -/
theorem no_skipped_midpoint_overlap {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j k : Fin 9} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {n m p : ℤ} (hijc : arcCenter c i n < arcCenter c j m)
    (hjkc : arcCenter c j m < arcCenter c k p) :
    ¬ (Arc c r i n ∩ Arc c r k p).Nonempty := by
  rintro ⟨x,hxI,hxK⟩
  have hIJ := endpoints_ordered hc hr hR hij hijc
  have hJK := endpoints_ordered hc hr hR hjk hjkc
  have hmeet : leftEnd c r k p ≤ rightEnd c r i n := hxK.1.trans hxI.2
  apply copy_not_subset_union hc hr hR hij.symm hjk m n p
  intro t ht
  by_cases htI : t ≤ rightEnd c r i n
  · exact Or.inl ⟨hIJ.1.le.trans ht.1,htI⟩
  · exact Or.inr ⟨hmeet.trans (lt_of_not_ge htI).le,ht.2.trans hJK.2.le⟩

theorem no_triple_lift {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j k : Fin 9} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n m p : ℤ) :
    ¬ ∃ t : ℝ, t ∈ Arc c r i n ∧ t ∈ Arc c r j m ∧ t ∈ Arc c r k p := by
  rintro ⟨t,hti,htj,htk⟩
  have hIJ := copy_centers_ne hc hr hR hij n m
  have hIK := copy_centers_ne hc hr hR hik n p
  have hJK := copy_centers_ne hc hr hR hjk m p
  rcases lt_or_gt_of_ne hIJ with hIJ | hJI
  · rcases lt_or_gt_of_ne hJK with hJK | hKJ
    · exact no_skipped_midpoint_overlap hc hr hR hij hik hjk hIJ hJK ⟨t,hti,htk⟩
    · rcases lt_or_gt_of_ne hIK with hIK | hKI
      · exact no_skipped_midpoint_overlap hc hr hR hik hij hjk.symm hIK hKJ ⟨t,hti,htj⟩
      · exact no_skipped_midpoint_overlap hc hr hR hik.symm hjk.symm hij hKI hIJ ⟨t,htk,htj⟩
  · rcases lt_or_gt_of_ne hIK with hIK | hKI
    · exact no_skipped_midpoint_overlap hc hr hR hij.symm hjk hik hJI hIK ⟨t,htj,htk⟩
    · rcases lt_or_gt_of_ne hJK with hJK | hKJ
      · exact no_skipped_midpoint_overlap hc hr hR hjk hij.symm hik.symm hJK hKI ⟨t,htj,hti⟩
      · exact no_skipped_midpoint_overlap hc hr hR hjk.symm hik.symm hij.symm hKJ hJI ⟨t,htk,hti⟩

/-- A whole-circle actual statement, including all closed endpoints.
No genericity, zero-overlap or nearest-owner condition is assumed. -/
theorem no_three_ring_caps {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j k : Fin 9} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x : Point} (hx : ‖x‖ = 1)
    (hi : dist x (c (ringSite i)) ≤ r) (hj : dist x (c (ringSite j)) ≤ r)
    (hk : dist x (c (ringSite k)) ≤ r) : False := by
  let t := circleAngle x
  have ht : circleMap t = x := circleMap_circleAngle _ hx
  obtain ⟨n,hn⟩ := (cap_iff_lift hc hr hR i t).mp (by rwa [ht])
  obtain ⟨m,hm⟩ := (cap_iff_lift hc hr hR j t).mp (by rwa [ht])
  obtain ⟨p,hp⟩ := (cap_iff_lift hc hr hR k t).mp (by rwa [ht])
  exact no_triple_lift hc hr hR hij hik hjk n m p ⟨t,hn,hm,hp⟩

end N11Formalization.ActualBoundaryArcOrder
#check @N11Formalization.ActualBoundaryArcOrder.endpoints_ordered
#check @N11Formalization.ActualBoundaryArcOrder.no_skipped_midpoint_overlap
#check @N11Formalization.ActualBoundaryArcOrder.no_three_ring_caps
#print axioms N11Formalization.ActualBoundaryArcOrder.endpoints_ordered
#print axioms N11Formalization.ActualBoundaryArcOrder.no_three_ring_caps
