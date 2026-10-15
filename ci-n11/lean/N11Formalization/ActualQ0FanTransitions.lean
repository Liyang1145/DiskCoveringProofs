import N11Formalization.ActualSameHubBoundarySides

/-! Actual q0 boundary fan owner changes occur EXACTLY at the two
actual central ring labels. No interval/order premise or canonicalcut. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ0FanTransitions
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualHubTriangleCensus ActualHubPathCounts
open ActualRefinementVertexLinks ActualHubNeighborCoverage ActualHubRingPaths
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualQ0BoundaryFans ActualSameHubBoundarySides

theorem FanData.ring_to_hub_neighbors {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (F : FanData R) (i : Fin 9) :
    Neighbor R (ringSite i) (hubSite (F.colors i)) ∧
      Neighbor R (ringSite i) (hubSite (F.colors (i-1))) := by
  have hne (b : Bool) : hubSite b ≠ ringSite i :=
    ActualSelectedSkipChordEar.hub_ne_ring (hubSite_hub b) i.isLt
  exact ⟨⟨hne _,F.faces i,by rw [F.labels]; simp,by rw [F.labels]; simp⟩,
    ⟨hne _,F.faces (i-1),by rw [F.previous_labels]; simp,by rw [F.previous_labels]; simp⟩⟩

theorem FanData.transition_iff_two_hub_neighbors {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (F : FanData R) (i : Fin 9) :
    F.colors (i-1) ≠ F.colors i ↔
      Neighbor R (ringSite i) 9 ∧ Neighbor R (ringSite i) 10 := by
  have hn := FanData.ring_to_hub_neighbors F i
  constructor
  · intro hchange
    cases hL : F.colors (i-1) <;> cases hR : F.colors i
    · exact (hchange (hL.trans hR.symm)).elim
    · have hn' := hn
      simp only [hL,hR,hubSite,Bool.false_eq_true,if_false,if_true] at hn'
      exact hn'
    · have hn' := hn
      simp only [hL,hR,hubSite,Bool.false_eq_true,if_false,if_true] at hn'
      exact ⟨hn'.2,hn'.1⟩
    · exact (hchange (hL.trans hR.symm)).elim
  · rintro ⟨h9,h10⟩ he
    have hD : labelSet R (F.faces (i-1)) = {prevSite i,ringSite i,hubSite (F.colors i)} := by
      rw [F.previous_labels,he]
    have hno := actual_same_hub_boundary_no_other h hr R i
      (hubSite_hub (F.colors i)) (hubSite_hub (!F.colors i))
      (hubSite_not_other (F.colors i)) hD (F.labels i)
    cases hB : F.colors i
    · exact hno (by simpa only [hB,hubSite,Bool.not_false,if_true] using h9)
    · exact hno (by simpa only [hB,hubSite,Bool.not_true,Bool.false_eq_true,if_false] using h10)

theorem FanData.transition_iff_common_ring {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (F : FanData R) (i : Fin 9) :
    F.colors (i-1) ≠ F.colors i ↔ ringSite i ∈ ringNeighbors R 9 ∩ ringNeighbors R 10 := by
  rw [FanData.transition_iff_two_hub_neighbors h hr F i]
  simp only [Finset.mem_inter,mem_ringNeighbors]
  exact ⟨fun ⟨h9,h10⟩ => ⟨⟨neighbor_symm h9,i.isLt⟩,⟨neighbor_symm h10,i.isLt⟩⟩,
    fun ⟨⟨h9,_⟩,⟨h10,_⟩⟩ => ⟨neighbor_symm h9,neighbor_symm h10⟩⟩

theorem FanData.exactly_two_actual_transitions {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (F : FanData R) (P : RingPath R 9 10) :
    ∃ a b : Fin 9, a ≠ b ∧ ringSite a = P.first ∧ ringSite b = P.last ∧
      ∀ i : Fin 9, F.colors (i-1) ≠ F.colors i ↔ i = a ∨ i = b := by
  let a : Fin 9 := ⟨P.first.val,P.ring_vertices _ P.walk.start_mem_support⟩
  let b : Fin 9 := ⟨P.last.val,P.ring_vertices _ P.walk.end_mem_support⟩
  have ha : ringSite a = P.first := Fin.ext rfl
  have hb : ringSite b = P.last := Fin.ext rfl
  have hab : a ≠ b := fun he => P.endpoints_ne (by rw [← ha,← hb,he])
  refine ⟨a,b,hab,ha,hb,?_⟩
  intro i
  rw [FanData.transition_iff_common_ring h hr F i,actual_common_neighbors_are_endpoints h hr R P,
    ← ha,← hb]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  have hinj : Function.Injective ringSite := fun i j he =>
    Fin.ext (congrArg (fun k : Fin 11 => k.val) he)
  exact ⟨fun hh => hh.imp (fun he => hinj he) (fun he => hinj he),
    fun hh => hh.imp (congrArg ringSite) (congrArg ringSite)⟩

end N11Formalization.ActualQ0FanTransitions
#check @N11Formalization.ActualQ0FanTransitions.FanData.exactly_two_actual_transitions
#print axioms N11Formalization.ActualQ0FanTransitions.FanData.transition_iff_two_hub_neighbors
#print axioms N11Formalization.ActualQ0FanTransitions.FanData.exactly_two_actual_transitions
