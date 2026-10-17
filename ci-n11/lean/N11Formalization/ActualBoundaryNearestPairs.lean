import N11Formalization.ActualBoundaryArcOrder
import N11Formalization.DSHTopologyOwnershipSwitchCount
import N11Formalization.ActualVoronoiCells

/-! Genuine boundary nearest pairs: no third site is weakly nearest.
This is derived from actual closed-cap multiplicity, not from genericity. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryNearestPairs
open DSHTopologyInterior ActualVoronoiCells ActualRingDirectionOrder
open ActualBoundaryArcOrder DSHTopologyOwnership DSHTopologyOwnershipSwitches
open DSHTopologyOwnershipSwitchCount

theorem nearest_ring {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hR : RingLabels c r) {x : Point} (hx : ‖x‖ = 1) {i : Fin 11}
    (hi : x ∈ Cell c i) : i.val < 9 :=
  (hR i).mp ⟨x,hx,nearest_le_radius hc (mem_unitDisk.mpr hx.le) hi⟩

theorem nearest_one_of_pair {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {x : Point} (hx : ‖x‖ = 1) {i j k : Fin 11} (hij : i ≠ j)
    (hi : x ∈ Cell c i) (hj : x ∈ Cell c j) (hk : x ∈ Cell c k) :
    k = i ∨ k = j := by
  by_contra hno
  have hki : k ≠ i := fun h => hno (Or.inl h)
  have hkj : k ≠ j := fun h => hno (Or.inr h)
  let I : Fin 9 := ⟨i.val,nearest_ring hc hR hx hi⟩
  let J : Fin 9 := ⟨j.val,nearest_ring hc hR hx hj⟩
  let K : Fin 9 := ⟨k.val,nearest_ring hc hR hx hk⟩
  have hIJ : I ≠ J := by
    intro h
    exact hij (Fin.ext (congrArg (fun q : Fin 9 => q.val) h))
  have hIK : I ≠ K := by
    intro h
    have hval : i.val = k.val := congrArg (fun q : Fin 9 => q.val) h
    have he : i = k := Fin.ext hval
    exact hki he.symm
  have hJK : J ≠ K := by
    intro h
    have hval : j.val = k.val := congrArg (fun q : Fin 9 => q.val) h
    have he : j = k := Fin.ext hval
    exact hkj he.symm
  exact no_three_ring_caps hc hr hR hIJ hIK hJK hx
    (nearest_le_radius hc (mem_unitDisk.mpr hx.le) hi)
    (nearest_le_radius hc (mem_unitDisk.mpr hx.le) hj)
    (nearest_le_radius hc (mem_unitDisk.mpr hx.le) hk)

theorem other_strictly_farther {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {x : Point} (hx : ‖x‖ = 1) {i j : Fin 11} (hij : i ≠ j)
    (hi : x ∈ Cell c i) (hj : x ∈ Cell c j) :
    ∀ k : Fin 11, k ≠ i → k ≠ j → dist x (c i) < dist x (c k) := by
  intro k hki hkj
  by_contra hnot
  have heq : dist x (c k) = dist x (c i) :=
    le_antisymm (le_of_not_gt hnot) (hi k)
  have hk : x ∈ Cell c k := by
    intro l
    rw [heq]
    exact hi l
  rcases nearest_one_of_pair hc hr hR hx hij hi hj hk with h | h
  · exact hki h
  · exact hkj h

end N11Formalization.ActualBoundaryNearestPairs
#check @N11Formalization.ActualBoundaryNearestPairs.nearest_one_of_pair
#check @N11Formalization.ActualBoundaryNearestPairs.other_strictly_farther
#print axioms N11Formalization.ActualBoundaryNearestPairs.nearest_one_of_pair
#print axioms N11Formalization.ActualBoundaryNearestPairs.other_strictly_farther
