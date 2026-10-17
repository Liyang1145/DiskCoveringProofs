import N11Formalization.ActualBoundaryNeighborTies
import N11Formalization.ActualBoundaryOverlapAdjacency
import N11Formalization.ActualBoundaryTransversality
import N11Formalization.DSHTopologyOwnershipLedger

/-! Connected ACTUAL boundary nearest regions in every short periodic cap
lift. Inward unique-cap-tie rules out a dip between two nearest endpoints,
without a circle-minus-finite-set or ownership-connectedness premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryOwnershipIntervals
open ActualCoverStructuralReduction ActualBoundaryArcFrame ActualRingDirectionOrder
open ActualBoundaryNeighborTies ActualBoundaryOverlapAdjacency ActualVoronoiCells
open DSHTopologyOwnership DSHTopologyOwnershipSwitches
open ActualBoundaryTransversality
open DSHTopologyInterior DSHTopologyOwnershipLedger MeasureTheory

def WeakLift (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) (n : ℤ) : Set ℝ :=
  {t | t ∈ Arc c r i n ∧ circleMap t ∈ Cell c (ringSite i)}

theorem arc_between {c : Fin 11 → Point} {r : ℝ} {i : Fin 9} {n : ℤ}
    {a b t : ℝ} (ha : a ∈ Arc c r i n) (hb : b ∈ Arc c r i n)
    (ht : t ∈ Set.Icc a b) : t ∈ Arc c r i n :=
  ⟨ha.1.trans ht.1,ht.2.trans hb.2⟩

theorem arc_circle_injective {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i : Fin 9} {n : ℤ}
    {a b : ℝ} (ha : a ∈ Arc c r i n) (hb : b ∈ Arc c r i n)
    (he : circleMap a = circleMap b) : a = b := by
  have hw := halfWidth_le_small h.cover hr h.labels i
  change arcCenter c i n-halfWidth c r i ≤ a ∧ a ≤ arcCenter c i n+halfWidth c r i at ha
  change arcCenter c i n-halfWidth c r i ≤ b ∧ b ≤ arcCenter c i n+halfWidth c r i at hb
  apply circleMap_inj_of_short (heq := he)
  · linarith [ha.1,ha.2,hb.1,hb.2,Real.pi_pos]
  · linarith [ha.1,ha.2,hb.1,hb.2,Real.pi_pos]

theorem gap_zero_tie {a b : Point} {t : ℝ}
    (he : sqDist b t-sqDist a t = 0) : dist (circleMap t) a = dist (circleMap t) b := by
  rw [sqDist_eq_dist_sq,sqDist_eq_dist_sq] at he
  nlinarith [dist_nonneg (x := circleMap t) (y := a),dist_nonneg (x := circleMap t) (y := b)]

theorem Representative.weakLift_ordConnected {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) (n : ℤ) :
    (WeakLift c r i n).OrdConnected := by
  refine ⟨?_⟩
  intro a ha b hb t ht
  have htArc := arc_between ha.1 hb.1 ht
  refine ⟨htArc,?_⟩
  intro j
  by_contra hnot
  have hcloser : dist (circleMap t) (c j) < dist (circleMap t) (c (ringSite i)) :=
    lt_of_not_ge hnot
  have hiRad := (cap_iff_lift h.cover hr h.labels i t).mpr ⟨n,htArc⟩
  have hjRing : j.val < 9 := (h.labels j).mp
    ⟨circleMap t,circleMap_norm t,hcloser.le.trans hiRad⟩
  let J : Fin 9 := ⟨j.val,hjRing⟩
  have hIJ : i ≠ J := by
    intro he
    have hsite : ringSite i = j := by rw [he]; rfl
    rw [hsite] at hcloser
    exact (lt_irrefl _) hcloser
  let f := fun s : ℝ => sqDist (c (ringSite J)) s-sqDist (c (ringSite i)) s
  have hfa : 0 ≤ f a := by
    dsimp [f]
    rw [sqDist_eq_dist_sq,sqDist_eq_dist_sq]
    have hd := ha.2 j
    change dist (circleMap a) (c (ringSite i)) ≤ dist (circleMap a) (c (ringSite J)) at hd
    nlinarith [dist_nonneg (x := circleMap a) (y := c (ringSite i))]
  have hfb : 0 ≤ f b := by
    dsimp [f]
    rw [sqDist_eq_dist_sq,sqDist_eq_dist_sq]
    have hd := hb.2 j
    change dist (circleMap b) (c (ringSite i)) ≤ dist (circleMap b) (c (ringSite J)) at hd
    nlinarith [dist_nonneg (x := circleMap b) (y := c (ringSite i))]
  have hft : f t < 0 := by
    dsimp [f]
    rw [sqDist_eq_dist_sq,sqDist_eq_dist_sq]
    change dist (circleMap t) (c (ringSite J)) < dist (circleMap t) (c (ringSite i)) at hcloser
    nlinarith [dist_nonneg (x := circleMap t) (y := c (ringSite J))]
  have hcont : Continuous f := (continuous_sqDist _).sub (continuous_sqDist _)
  obtain ⟨s,hs,hfs⟩ := intermediate_value_Icc' ht.1 hcont.continuousOn ⟨hft.le,hfa⟩
  obtain ⟨u,hu,hfu⟩ := intermediate_value_Icc ht.2 hcont.continuousOn ⟨hft.le,hfb⟩
  have hsArc := arc_between ha.1 hb.1 (show s ∈ Set.Icc a b from ⟨hs.1,hs.2.trans ht.2⟩)
  have huArc := arc_between ha.1 hb.1 (show u ∈ Set.Icc a b from ⟨ht.1.trans hu.1,hu.2⟩)
  have hstie := gap_zero_tie hfs
  have hutie := gap_zero_tie hfu
  have hsrad := (cap_iff_lift h.cover hr h.labels i s).mpr ⟨n,hsArc⟩
  have hurad := (cap_iff_lift h.cover hr h.labels i u).mpr ⟨n,huArc⟩
  have hpoints := ActualBoundaryTieUniqueness.Representative.unique_ring_cap_tie h
    (by linarith : r < 1) hIJ (circleMap_norm s) (circleMap_norm u) hstie hutie hsrad hurad
  have he := arc_circle_injective h hr hsArc huArc hpoints
  have hsu : s = t := by linarith [hs.2,hu.1]
  rw [hsu] at hfs
  linarith

theorem Representative.weakLift_preconnected {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) (n : ℤ) :
    IsPreconnected (WeakLift c r i n) :=
  (Representative.weakLift_ordConnected h hr i n).isPreconnected

theorem Representative.strict_between_weak {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i : Fin 9} {n : ℤ}
    {a b t : ℝ} (ha : a ∈ WeakLift c r i n) (hb : b ∈ WeakLift c r i n)
    (hat : a < t) (htb : t < b) : circleMap t ∈ StrictCell c (ringSite i) := by
  have hinterval := (Representative.weakLift_ordConnected h hr i n).out' ha hb
  have htweak := hinterval ⟨hat.le,htb.le⟩
  intro j hji
  by_contra hnot
  have heq : dist (circleMap t) (c (ringSite i)) = dist (circleMap t) (c j) :=
    le_antisymm (htweak.2 j) (le_of_not_gt hnot)
  have hiRad := (cap_iff_lift h.cover hr h.labels i t).mpr ⟨n,htweak.1⟩
  have hjRing : j.val < 9 := (h.labels j).mp
    ⟨circleMap t,circleMap_norm t,by rwa [← heq]⟩
  let J : Fin 9 := ⟨j.val,hjRing⟩
  have hsites : ringSite i ≠ ringSite J := by
    intro he
    exact hji he.symm
  change dist (circleMap t) (c (ringSite i)) = dist (circleMap t) (c (ringSite J)) at heq
  obtain ⟨x,hx,hxi,hxo⟩ := h.private_circle i
  obtain ⟨y,hy,hyj,hyo⟩ := h.private_circle J
  have hn := gapDerivative_ne_zero hx hy
    (hxi.trans_lt (hxo _ hsites.symm)) (hyj.trans_lt (hyo _ hsites)) heq
  let g := fun s : ℝ => sqDist (c (ringSite J)) s-sqDist (c (ringSite i)) s
  have hg0 : g t = 0 := by
    dsimp [g]
    rw [sqDist_eq_dist_sq,sqDist_eq_dist_sq,heq,sub_self]
  have hmin : IsLocalMin g t := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨min (t-a) (b-t),lt_min (by linarith) (by linarith),?_⟩
    intro s hs
    rw [Real.dist_eq] at hs
    have hbounds := abs_lt.mp hs
    have hleft := min_le_left (t-a) (b-t)
    have hright := min_le_right (t-a) (b-t)
    have hsmem : s ∈ Set.Icc a b := ⟨by linarith [hbounds.1],by linarith [hbounds.2]⟩
    have hsweak := hinterval hsmem
    have hd := hsweak.2 j
    rw [hg0]
    dsimp [g]
    rw [sqDist_eq_dist_sq,sqDist_eq_dist_sq]
    change dist (circleMap s) (c (ringSite i)) ≤ dist (circleMap s) (c (ringSite J)) at hd
    nlinarith [dist_nonneg (x := circleMap s) (y := c (ringSite i))]
  exact hn (hmin.hasDerivAt_eq_zero (hasDerivAt_gap _ _ t))

def OwnedLift (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) (n : ℤ) : Set ℝ :=
  {t | t ∈ Arc c r i n ∧ OwnsPt c (ringSite i) (circleMap t)}

theorem Representative.ownedLift_ordConnected {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) (n : ℤ) :
    (OwnedLift c r i n).OrdConnected := by
  refine ⟨?_⟩
  intro a ha b hb t ht
  by_cases hta : t = a
  · rwa [hta]
  by_cases htb : t = b
  · rwa [htb]
  have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
  have htb' : t < b := lt_of_le_of_ne ht.2 htb
  have haW : a ∈ WeakLift c r i n := ⟨ha.1,ha.2.1⟩
  have hbW : b ∈ WeakLift c r i n := ⟨hb.1,hb.2.1⟩
  have hs := Representative.strict_between_weak h hr haW hbW hat htb'
  refine ⟨arc_between ha.1 hb.1 ht,?_,?_⟩
  · exact strictCell_subset c _ hs
  · intro j hj
    exact hs j (ne_of_lt hj)

theorem Representative.ownedLift_connected {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) (n : ℤ) :
    IsConnected (OwnedLift c r i n) := by
  have hpre := (Representative.ownedLift_ordConnected h hr i n).isPreconnected
  obtain ⟨x,hx,hxi,hother⟩ := h.private_circle i
  let t := circleAngle x
  have hpoint : circleMap t = x := circleMap_circleAngle _ hx
  obtain ⟨k,hk⟩ := (cap_iff_lift h.cover hr h.labels i t).mp (by rwa [hpoint])
  let a := t+((n-k:ℤ):ℝ)*period
  have ha : a ∈ Arc c r i n := mem_shift_copy hk
  have hp : circleMap a = x := by rw [circleMap_periodic,hpoint]
  refine ⟨⟨a,ha,?_,?_⟩,hpre⟩
  · intro j
    rw [hp]
    by_cases hji : j = ringSite i
    · rw [hji]
    · exact hxi.trans (hother j hji).le
  · intro j hj
    rw [hp]
    exact hxi.trans_lt (hother j (ne_of_lt hj))

theorem card_boundary_of_labels {c : Fin 11 → Point} {r : ℝ} (hR : RingLabels c r) :
    Fintype.card (BoundaryIdx c r) = 9 := by
  let e : BoundaryIdx c r ≃ Fin 9 :=
    { toFun := fun j => ⟨j.val.val,(hR j.val).mp j.property⟩
      invFun := fun i => ⟨ringSite i,hR.ring_meets (i := ringSite i) i.isLt⟩
      left_inv := by intro j; apply Subtype.ext; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  simpa only [Fintype.card_fin] using Fintype.card_congr e

/-- The old actual ownership ledger's cardinality premise is PAID here by
real labels. No source candidate or nine-owner premise is assumed. -/
theorem Representative.positive_owned_measures {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : BoundaryIdx c r) :
    0 < volume.real (ownerSetB c r i) ∧
      volume.real (ownerSetB c r i) ≤ 2*Real.arcsin r :=
  ownership_ledger_actual_R0 (Covers.nonneg h.cover) hr h.cover (card_boundary_of_labels h.labels) i

def CircleOwned (c : Fin 11 → Point) (i : Fin 9) : Set Point :=
  {x | ‖x‖ = 1 ∧ OwnsPt c (ringSite i) x}

theorem circleMap_continuous : Continuous circleMap := by
  have hcoord : Continuous (fun t : ℝ => (![Real.cos t,Real.sin t] : Fin 2 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using (show Continuous (fun t : ℝ => Real.cos t) from Real.continuous_cos)
    · simpa using (show Continuous (fun t : ℝ => Real.sin t) from Real.continuous_sin)
  change Continuous (fun t : ℝ => WithLp.toLp 2 (![Real.cos t,Real.sin t] : Fin 2 → ℝ))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp hcoord

theorem Representative.circleOwned_eq_image {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) (n : ℤ) :
    CircleOwned c i = circleMap '' OwnedLift c r i n := by
  ext x
  constructor
  · rintro ⟨hx,hown⟩
    let t := circleAngle x
    have hp : circleMap t = x := circleMap_circleAngle _ hx
    have hrad := ownsPt_dist_le_of_covers h.cover (mem_unitDisk.mpr hx.le) hown
    obtain ⟨k,hk⟩ := (cap_iff_lift h.cover hr h.labels i t).mp (by rwa [hp])
    let a := t+((n-k:ℤ):ℝ)*period
    have hpoint : circleMap a = x := by rw [circleMap_periodic,hp]
    exact ⟨a,⟨mem_shift_copy hk,by rwa [hpoint]⟩,hpoint⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨circleMap_norm t,ht.2⟩

/-- The ACTUAL owned point-set on S¹ is nonempty and connected, not only
an abstract periodic parameter interval. -/
theorem Representative.circleOwned_connected {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) :
    IsConnected (CircleOwned c i) := by
  rw [Representative.circleOwned_eq_image h hr i 0]
  exact (Representative.ownedLift_connected h hr i 0).image circleMap circleMap_continuous.continuousOn

end N11Formalization.ActualBoundaryOwnershipIntervals
#check @N11Formalization.ActualBoundaryOwnershipIntervals.Representative.weakLift_ordConnected
#print axioms N11Formalization.ActualBoundaryOwnershipIntervals.Representative.weakLift_preconnected
#check @N11Formalization.ActualBoundaryOwnershipIntervals.Representative.ownedLift_connected
#print axioms N11Formalization.ActualBoundaryOwnershipIntervals.Representative.ownedLift_connected
#check @N11Formalization.ActualBoundaryOwnershipIntervals.Representative.positive_owned_measures
#print axioms N11Formalization.ActualBoundaryOwnershipIntervals.Representative.positive_owned_measures
#check @N11Formalization.ActualBoundaryOwnershipIntervals.Representative.circleOwned_connected
#print axioms N11Formalization.ActualBoundaryOwnershipIntervals.Representative.circleOwned_connected
