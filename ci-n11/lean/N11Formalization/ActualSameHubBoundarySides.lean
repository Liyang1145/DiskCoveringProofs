import N11Formalization.ActualQ0BoundaryFans

/-! Two adjacent actual boundary triangles with the SAME hub cannot have
another hub neighbor at their common ring site. Produced by real link
connectedness and degree2, not a drawn two-fan assumption. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSameHubBoundarySides
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementVertexLinks ActualRefinementLocalLinks
open ActualRefinementSideMultiplicity ActualRefinementLinkDegrees ActualHubLinkCycles
open ActualHubLinkNoRingCycle ActualSelectedEarRemoval ActualRingLinkConnected
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualRefinementInteriorFacetCount ActualBoundaryChainConservation
open ActualSelectedSkipChordEar ActualQ0BoundaryFans

theorem actual_same_hub_boundary_neighbors {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    {u : Fin 11} (hu : 9 ≤ u.val) {D E : R.Index}
    (hD : labelSet R D = {prevSite i,ringSite i,u})
    (hE : labelSet R E = {ringSite i,nextSite i,u}) :
    ∀ j : Fin 11, Neighbor R (ringSite i) j →
      j = prevSite i ∨ j = nextSite i ∨ j = u := by
  have hd := boundary_sites_distinct i
  have hpU : prevSite i ≠ u := (hub_ne_ring hu (i-1).isLt).symm
  have hmU : ringSite i ≠ u := (hub_ne_ring hu i.isLt).symm
  have hnU : nextSite i ≠ u := (hub_ne_ring hu (nextRing i).isLt).symm
  have hprev : (linkGraph R (ringSite i)).Adj (prevSite i) u := by
    refine ⟨hpU,hd.1,hmU.symm,D,?_,?_,?_⟩ <;> rw [hD] <;> simp
  have hnext : (linkGraph R (ringSite i)).Adj (nextSite i) u := by
    refine ⟨hnU,hd.2.1,hmU.symm,E,?_,?_,?_⟩ <;> rw [hE] <;> simp
  have hnu : Neighbor R (ringSite i) u := by
    exact ⟨hmU.symm,D,by rw [hD]; simp,by rw [hD]; simp⟩
  have hdeg : ((linkGraph R (ringSite i)).neighborSet u).ncard = 2 := by
    rw [link_neighborSet_eq R hmU,Set.ncard_coe_finset]
    have hc := actual_link_degree h hr R hmU
      (show ringSite i ∈ labelSet R D by rw [hD]; simp)
      (show u ∈ labelSet R D by rw [hD]; simp)
    have hb : ¬ BoundaryLabels (ringSite i) u := by
      rw [boundary_labels_at_ring]
      intro hh
      rcases hh with he | he
      · exact hpU he.symm
      · exact hnU he.symm
    rwa [if_neg hb] at hc
  have hU := two_neighbors_exhaust hd.2.2 hprev.symm hnext.symm hdeg
  have hprevOnly {j : Fin 11} (hj : (linkGraph R (ringSite i)).Adj (prevSite i) j) : j = u := by
    obtain ⟨A,hAi,hAp,hAj⟩ := hj.2.2.2
    have hn : nextRing (i-1) = i := by change i-1+1=i; exact sub_add_cancel _ _
    have hAD : A = D := boundary_pair_triangle_unique R h hr (i-1) hAp
      (by simpa only [hn] using hAi) (by rw [hD]; simp [prevSite])
      (by rw [hn,hD]; simp)
    rw [hAD,hD] at hAj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hAj
    rcases hAj with he | he | he
    · exact (hj.1 he.symm).elim
    · exact (hj.2.2.1 he).elim
    · exact he
  have hnextOnly {j : Fin 11} (hj : (linkGraph R (ringSite i)).Adj (nextSite i) j) : j = u := by
    obtain ⟨A,hAi,hAn,hAj⟩ := hj.2.2.2
    have hAE : A = E := boundary_pair_triangle_unique R h hr i hAi hAn
      (by rw [hE]; simp) (by rw [hE]; simp [nextSite])
    rw [hAE,hE] at hAj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hAj
    rcases hAj with he | he | he
    · exact (hj.2.2.1 he).elim
    · exact (hj.1 he.symm).elim
    · exact he
  have hclosed : ∀ j ∈ ({prevSite i,nextSite i,u} : Set (Fin 11)), ∀ k,
      (linkGraph R (ringSite i)).Adj j k →
        k ∈ ({prevSite i,nextSite i,u} : Set (Fin 11)) := by
    intro j hj k hjk
    rcases hj with rfl | hj
    · exact Or.inr (Or.inr (hprevOnly hjk))
    rcases hj with rfl | hj
    · exact Or.inr (Or.inr (hnextOnly hjk))
    · have he : j = u := hj
      subst j
      have hk : k ∈ ({prevSite i,nextSite i} : Set (Fin 11)) := hU ▸ hjk
      rcases hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
  have hnprev := (actual_boundary_neighbors h hr R i).1
  intro j hj
  exact reachable_mem_closed hclosed (Or.inl rfl)
    (actual_all_site_links_reachable h hr R (ringSite i) hnprev hj)

theorem actual_same_hub_boundary_no_other {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    {u v : Fin 11} (hu : 9 ≤ u.val) (hv : 9 ≤ v.val) (hvu : v ≠ u)
    {D E : R.Index}
    (hD : labelSet R D = {prevSite i,ringSite i,u})
    (hE : labelSet R E = {ringSite i,nextSite i,u}) :
    ¬ Neighbor R (ringSite i) v := by
  intro hn
  have hh := actual_same_hub_boundary_neighbors h hr R i hu hD hE v hn
  rcases hh with he | he | he
  · have hh : v.val = (i-1).val := congrArg Fin.val he
    omega
  · have hh : v.val = (nextRing i).val := congrArg Fin.val he
    omega
  · exact hvu he

end N11Formalization.ActualSameHubBoundarySides
#check @N11Formalization.ActualSameHubBoundarySides.actual_same_hub_boundary_no_other
#print axioms N11Formalization.ActualSameHubBoundarySides.actual_same_hub_boundary_no_other
