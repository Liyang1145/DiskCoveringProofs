import N11Formalization.ActualCapClusterLift

/-! Four ACTUAL complete ring caps cannot lie in one radius2r test cap.
The big cap meeting S¹ is explicit, because an abstract arccos interval
can be spuriously nonempty when its threshold>1. Actual intersection
producers pay this premise; no spurious cap is used. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCapClusterCapacity
open DSHTopologyInterior ActualRingDirectionOrder ActualBoundaryArcFrame
open ActualCapClusterLift ActualMixedCircleCapacity

theorem cap_in_big_of_copy {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {p : Point} (hp : p ≠ 0)
    (hm : ∃ y : Point, ‖y‖ = 1 ∧ dist y p ≤ 2*r) {i : Fin 9} {n m : ℤ}
    (hsub : Arc c r i n ⊆ BigArc p r m) {x : Point} (hx : ‖x‖ = 1)
    (hi : dist x (c (ringSite i)) ≤ r) : dist x p ≤ 2*r := by
  let t := circleAngle x
  have hpoint : circleMap t = x := circleMap_circleAngle _ hx
  obtain ⟨k,hk⟩ := (cap_iff_lift hc hr hR i t).mp (by rwa [hpoint])
  let a := t+((n-k:ℤ):ℝ)*period
  have ha : a ∈ BigArc p r m := hsub (mem_shift_copy hk)
  have hpnt : circleMap a = x := by
    rw [circleMap_periodic,hpoint]
  have hd := (big_cap_iff hp (Covers.nonneg hc) hr hm a).mpr ⟨m,ha⟩
  rwa [hpnt] at hd

theorem no_four_cap_cluster {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (p : Point) (s : Finset (Fin 9)) (hs : s.card = 4)
    (hcluster : ∀ i ∈ s, ∀ x : Point, ‖x‖ = 1 →
      dist x (c (ringSite i)) ≤ r → dist x p ≤ 2*r) : False := by
  classical
  let T := {i : Fin 9 // i ∉ s}
  have hcard : Fintype.card T = 5 := by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,hs]
  let e : T ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
  let d : Fin 5 → Point := fun j => c (ringSite (e.symm j).val)
  apply not_big_and_five_small (Covers.nonneg hc) hr p d
  intro x hx
  obtain ⟨j,hj⟩ := hc x (mem_unitDisk.mpr hx.le)
  have hj9 : j.val < 9 := (hR j).mp ⟨x,hx,hj⟩
  let i : Fin 9 := ⟨j.val,hj9⟩
  have hi : dist x (c (ringSite i)) ≤ r := hj
  by_cases his : i ∈ s
  · exact Or.inl (hcluster i his x hx hi)
  · right
    let a : T := ⟨i,his⟩
    refine ⟨e a,?_⟩
    change dist x (c (ringSite (e.symm (e a)).val)) ≤ r
    rw [e.symm_apply_apply]
    exact hi

theorem no_four_copies_in_big {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {p : Point} (hp : p ≠ 0)
    (hm : ∃ y : Point, ‖y‖ = 1 ∧ dist y p ≤ 2*r)
    (s : Finset (Fin 9)) (hs : s.card = 4)
    (hcopies : ∀ i ∈ s, ∃ n m : ℤ, Arc c r i n ⊆ BigArc p r m) : False := by
  apply no_four_cap_cluster hc hr hR p s hs
  intro i hi x hx hxi
  obtain ⟨n,m,hsub⟩ := hcopies i hi
  exact cap_in_big_of_copy hc hr hR hp hm hsub hx hxi

end N11Formalization.ActualCapClusterCapacity
#check @N11Formalization.ActualCapClusterCapacity.no_four_cap_cluster
#print axioms N11Formalization.ActualCapClusterCapacity.no_four_cap_cluster
