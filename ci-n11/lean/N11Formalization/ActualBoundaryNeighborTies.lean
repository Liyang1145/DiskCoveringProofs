import N11Formalization.ActualBoundaryCyclicOrder
import N11Formalization.ActualBoundaryNearestPairs
import N11Formalization.ActualBoundaryTieUniqueness

/-! Every sorted cyclic ring-neighbor pair has a genuine nearest tie on S¹.
Closed-endpoint/singleton overlap cases are included by the IVT. Inward
normalization then makes this tie unique, without a genericity assumption. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryNeighborTies
open DSHTopologyInterior ActualRingDirectionOrder ActualBoundaryArcFrame
open ActualBoundaryArcOrder ActualBoundaryCyclicOrder ActualVoronoiCells
open DSHTopologyOwnership DSHTopologyOwnershipSwitches
open ActualCoverStructuralReduction ActualBoundaryTieUniqueness

theorem sqDist_of_endpoint_cos {c : Fin 11 → Point} {r t : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) (i : Fin 9)
    (ht : Real.cos (t-midpointAngle c i) = Real.cos (halfWidth c r i)) :
    sqDist (c (ringSite i)) t = r^2 := by
  have hr0 := Covers.nonneg hc
  have hr1 : r < 1 := by linarith
  have hmeet := hR.ring_meets (i := ringSite i) i.isLt
  have hne := ActualInwardNormalization.touching_ne_zero hr1 hmeet
  have hn := norm_pos_iff.mpr hne
  have hlo : -1 ≤ (1+‖c (ringSite i)‖^2-r^2)/(2*‖c (ringSite i)‖) := by
    rw [le_div_iff₀ (by linarith : 0 < 2*‖c (ringSite i)‖)]
    nlinarith
  have hcos : Real.cos (halfWidth c r i) =
      (1+‖c (ringSite i)‖^2-r^2)/(2*‖c (ringSite i)‖) :=
    Real.cos_arccos hlo (cap_threshold_le_one_of_meets hne hr0 hmeet)
  have hinner : inner ℝ (circleMap t) (centerDir (c (ringSite i))) =
      Real.cos (halfWidth c r i) := by
    rw [← midpoint_direction hc hr hR i,inner_circleMap,ht]
  have hi : inner ℝ (circleMap t) (c (ringSite i)) =
      ‖c (ringSite i)‖*Real.cos (halfWidth c r i) := by
    conv_lhs => rw [self_eq_norm_smul_centerDir hne]
    rw [real_inner_smul_right,hinner]
  rw [sqDist_eq_dist_sq,dist_eq_norm,norm_sub_sq_real,circleMap_norm,hi,hcos]
  field_simp
  <;> ring

theorem sqDist_leftEnd {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) (i : Fin 9) (n : ℤ) :
    sqDist (c (ringSite i)) (leftEnd c r i n) = r^2 := by
  apply sqDist_of_endpoint_cos hc hr hR i
  have he : leftEnd c r i n-midpointAngle c i =
      -halfWidth c r i+(n:ℝ)*(2*Real.pi) := by
    dsimp [leftEnd,arcCenter,period]
    ring
  rw [he,Real.cos_add_int_mul_two_pi,Real.cos_neg]

theorem sqDist_rightEnd {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) (i : Fin 9) (n : ℤ) :
    sqDist (c (ringSite i)) (rightEnd c r i n) = r^2 := by
  apply sqDist_of_endpoint_cos hc hr hR i
  have he : rightEnd c r i n-midpointAngle c i =
      halfWidth c r i+(n:ℝ)*(2*Real.pi) := by
    dsimp [rightEnd,arcCenter,period]
    ring
  rw [he,Real.cos_add_int_mul_two_pi]

theorem nearest_of_two_caps_tie {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {i j : Fin 9} (hij : i ≠ j) {x : Point} (hx : ‖x‖ = 1)
    (hi : dist x (c (ringSite i)) ≤ r)
    (htie : dist x (c (ringSite i)) = dist x (c (ringSite j))) :
    x ∈ Cell c (ringSite i) ∩ Cell c (ringSite j) := by
  have hj : dist x (c (ringSite j)) ≤ r := by rwa [← htie]
  have hfirst : x ∈ Cell c (ringSite i) := by
    intro k
    by_cases hki : k = ringSite i
    · rw [hki]
    by_cases hkj : k = ringSite j
    · rw [hkj,htie]
    have hkr : r < dist x (c k) := by
      by_contra hnot
      have hk : dist x (c k) ≤ r := le_of_not_gt hnot
      have hk9 : k.val < 9 := (hR k).mp ⟨x,hx,hk⟩
      let K : Fin 9 := ⟨k.val,hk9⟩
      have hiK : i ≠ K := by
        intro he
        apply hki
        apply Fin.ext
        exact (congrArg (fun q : Fin 9 => q.val) he).symm
      have hjK : j ≠ K := by
        intro he
        apply hkj
        apply Fin.ext
        exact (congrArg (fun q : Fin 9 => q.val) he).symm
      exact no_three_ring_caps hc hr hR hij hiK hjK hx hi hj hk
    exact hi.trans hkr.le
  exact ⟨hfirst,fun k => by rw [← htie]; exact hfirst k⟩

structure NeighborTie (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) where
  angle : ℝ
  in_overlap : angle ∈ Arc c r i 0 ∩ Arc c r (nextRing i) (nextShift i)
  equidistant : dist (circleMap angle) (c (ringSite i)) =
    dist (circleMap angle) (c (ringSite (nextRing i)))
  nearest : circleMap angle ∈ Cell c (ringSite i) ∩ Cell c (ringSite (nextRing i))
  radius : dist (circleMap angle) (c (ringSite i)) ≤ r

theorem neighbor_tie {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) (i : Fin 9) : Nonempty (NeighborTie c r i) := by
  let a := leftEnd c r (nextRing i) (nextShift i)
  let b := rightEnd c r i 0
  let f := fun t : ℝ => sqDist (c (ringSite (nextRing i))) t-sqDist (c (ringSite i)) t
  have hab : a ≤ b := neighbor_overlap hc hr hR ho i
  have ha : a ∈ Arc c r i 0 ∩ Arc c r (nextRing i) (nextShift i) := by
    rw [← overlap_interval hc hr hR ho i]
    exact ⟨le_rfl,hab⟩
  have hb : b ∈ Arc c r i 0 ∩ Arc c r (nextRing i) (nextShift i) := by
    rw [← overlap_interval hc hr hR ho i]
    exact ⟨hab,le_rfl⟩
  have hda := (cap_iff_lift hc hr hR i a).mpr ⟨0,ha.1⟩
  have hdb := (cap_iff_lift hc hr hR (nextRing i) b).mpr ⟨nextShift i,hb.2⟩
  have hfa : 0 ≤ f a := by
    dsimp [f,a]
    rw [sqDist_leftEnd hc hr hR, sqDist_eq_dist_sq]
    nlinarith [Covers.nonneg hc,dist_nonneg (x := circleMap a) (y := c (ringSite i))]
  have hfb : f b ≤ 0 := by
    dsimp [f,b]
    rw [sqDist_rightEnd hc hr hR,sqDist_eq_dist_sq]
    nlinarith [Covers.nonneg hc,
      dist_nonneg (x := circleMap b) (y := c (ringSite (nextRing i)))]
  have hcont : Continuous f :=
    (continuous_sqDist _).sub (continuous_sqDist _)
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc' hab hcont.continuousOn ⟨hfb,hfa⟩
  have hmem : t ∈ Arc c r i 0 ∩ Arc c r (nextRing i) (nextShift i) := by
    rw [← overlap_interval hc hr hR ho i]
    exact ht
  have hrad := (cap_iff_lift hc hr hR i t).mpr ⟨0,hmem.1⟩
  have heq : dist (circleMap t) (c (ringSite i)) =
      dist (circleMap t) (c (ringSite (nextRing i))) := by
    dsimp [f] at hft
    rw [sqDist_eq_dist_sq,sqDist_eq_dist_sq] at hft
    nlinarith [dist_nonneg (x := circleMap t) (y := c (ringSite i)),
      dist_nonneg (x := circleMap t) (y := c (ringSite (nextRing i)))]
  exact ⟨⟨t,hmem,heq,nearest_of_two_caps_tie hc hr hR (next_ne i)
    (circleMap_norm t) hrad heq,hrad⟩⟩

theorem circleMap_inj_of_short {s t : ℝ} (hlo : -(2*Real.pi) < s-t)
    (hhi : s-t < 2*Real.pi) (heq : circleMap s = circleMap t) : s = t := by
  have hc : Real.cos (s-t) = 1 := by
    rw [← inner_circleMap,heq,real_inner_self_eq_norm_sq,circleMap_norm]
    norm_num
  have hz := (Real.cos_eq_one_iff_of_lt_of_lt hlo hhi).mp hc
  linarith

theorem NeighborTie.unique_angle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i : Fin 9}
    (v w : NeighborTie c r i) : v.angle = w.angle := by
  have he := ActualBoundaryTieUniqueness.Representative.unique_ring_cap_tie h
    (by linarith : r < 1) (next_ne i)
    (circleMap_norm v.angle) (circleMap_norm w.angle)
    v.equidistant w.equidistant v.radius w.radius
  have hne := ActualInwardNormalization.touching_ne_zero (by linarith : r < 1)
    (h.labels.ring_meets (i := ringSite i) i.isLt)
  have hw : halfWidth c r i ≤ Real.arcsin r :=
    capHalfWidth_le_arcsin hne (Covers.nonneg h.cover) (by linarith)
  have harc := (Real.arcsin_le_arcsin hr.le).trans arcsin_R0_lt_pi_div_eight.le
  have hv := v.in_overlap.1
  have hw' := w.in_overlap.1
  change arcCenter c i 0-halfWidth c r i ≤ v.angle ∧
    v.angle ≤ arcCenter c i 0+halfWidth c r i at hv
  change arcCenter c i 0-halfWidth c r i ≤ w.angle ∧
    w.angle ≤ arcCenter c i 0+halfWidth c r i at hw'
  apply circleMap_inj_of_short (heq := he)
  · linarith [hv.1,hv.2,hw'.1,hw'.2,Real.pi_pos]
  · linarith [hv.1,hv.2,hw'.1,hw'.2,Real.pi_pos]

end N11Formalization.ActualBoundaryNeighborTies
#check @N11Formalization.ActualBoundaryNeighborTies.neighbor_tie
#check @N11Formalization.ActualBoundaryNeighborTies.NeighborTie.unique_angle
#print axioms N11Formalization.ActualBoundaryNeighborTies.neighbor_tie
#print axioms N11Formalization.ActualBoundaryNeighborTies.NeighborTie.unique_angle
