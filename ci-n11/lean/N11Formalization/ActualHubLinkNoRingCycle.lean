import N11Formalization.ActualHubNeighborCoverage

/-! A three-ring cycle in an actual hub link is impossible.
Degree2 would make it a closed component, but the real hub link is
connected and contains the other hub. No global Euler/disk premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubLinkNoRingCycle
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementLocalLinks ActualRefinementVertexLinks ActualHubLinkCycles
open ActualHubLinkConnected ActualSelectedEarRemoval ActualRefinementTriangleUniqueness

theorem two_neighbors_exhaust {G : SimpleGraph (Fin 11)} {x y z : Fin 11}
    (hyz : y ≠ z) (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hd : (G.neighborSet x).ncard = 2) :
    G.neighborSet x = ({y,z} : Set (Fin 11)) := by
  apply Eq.symm
  apply Set.eq_of_subset_of_ncard_le
  · intro k hk
    rcases hk with rfl | hk
    · exact hxy
    · have he : k = z := hk
      exact he ▸ hxz
  · rw [hd,Set.ncard_pair hyz]
  · exact Set.toFinite _

theorem actual_hub_no_three_ring_cycle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i u : Fin 11} (hh : (i = 9 ∧ u = 10) ∨ (i = 10 ∧ u = 9))
    {a b k : Fin 11} (ha : a.val < 9) (hb : b.val < 9) (hk : k.val < 9)
    (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (hAB : (linkGraph R i).Adj a b)
    (hBK : (linkGraph R i).Adj b k)
    (hKA : (linkGraph R i).Adj k a) : False := by
  have hi : 9 ≤ i.val := by rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  have hna := neighbor_of_link_adj R hAB
  have hnb := neighbor_of_link_adj R hBK
  have hnk := neighbor_of_link_adj R hKA
  have hA := two_neighbors_exhaust hkb.symm hAB hKA.symm
    (actual_hub_link_degree_two h hr R hi hna)
  have hB := two_neighbors_exhaust hka.symm hAB.symm hBK
    (actual_hub_link_degree_two h hr R hi hnb)
  have hK := two_neighbors_exhaust hab hKA hBK.symm
    (actual_hub_link_degree_two h hr R hi hnk)
  have hclosed : ∀ x ∈ ({a,b,k} : Set (Fin 11)), ∀ y,
      (linkGraph R i).Adj x y → y ∈ ({a,b,k} : Set (Fin 11)) := by
    intro x hx y hxy
    rcases hx with rfl | hx
    · have hy : y ∈ ({b,k} : Set (Fin 11)) := hA ▸ hxy
      exact Or.inr hy
    rcases hx with rfl | hx
    · have hy : y ∈ ({a,k} : Set (Fin 11)) := hB ▸ hxy
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (Or.inr hy)
    · have he : x = k := hx
      subst x
      have hy : y ∈ ({a,b} : Set (Fin 11)) := hK ▸ hxy
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (Or.inl hy)
  obtain ⟨T,_,_,_,hT9,hT10,_,_⟩ :=
    ActualRefinementFacetRetention.Refinement.hub_edge_two_retained R h hr
  have hnu : Neighbor R i u := by
    rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨by decide,T,mem_labelSet.mpr hT9,mem_labelSet.mpr hT10⟩
    · exact ⟨by decide,T,mem_labelSet.mpr hT10,mem_labelSet.mpr hT9⟩
  have hum := reachable_mem_closed hclosed (Or.inl rfl)
    (actual_hub_link_reachable h hr R hi hna hnu)
  have hun : 9 ≤ u.val := by rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  rcases hum with he | he | he <;> subst u <;> omega

end N11Formalization.ActualHubLinkNoRingCycle
#check @N11Formalization.ActualHubLinkNoRingCycle.actual_hub_no_three_ring_cycle
#print axioms N11Formalization.ActualHubLinkNoRingCycle.actual_hub_no_three_ring_cycle
