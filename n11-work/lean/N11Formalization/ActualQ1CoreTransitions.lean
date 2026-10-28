import N11Formalization.ActualQ1CoreFans
import N11Formalization.ActualHubPathCounts

/-! Actual q1 core fan owner changes occur exactly at the two genuine
central labels. Same-color core faces plus a central face would put
three distinct triangles at one real hub spoke, contradicting incidence2.
No ordered core-fan hypothesis or metric class is inserted. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualQ1CoreTransitions
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementVertexLinks
open ActualHubTriangleCensus ActualHubPathCounts ActualHubRingPaths ActualHubNeighborCoverage
open ActualQ1CoreFans ActualQ1CoreCycle ActualQ0BoundaryFans
open ActualRingDirectionOrder ActualRefinementInteriorFacetCount ActualSelectedEdgeIncidence
open ActualSelectedEarRemoval

theorem boundary_labels_right_ring : ∀ i j : Fin 11, BoundaryLabels i j → j.val < 9 := by
  decide +kernel

theorem core_triangle_not_central : ∀ e : Fin 9, ∀ i : Fin 8, ∀ b : Bool,
    ¬ ((9 : Fin 11) ∈ ({ringSite (coreSite e i),ringSite (coreSite e (coreNext i)),hubSite b} :
      Finset (Fin 11)) ∧ (10 : Fin 11) ∈
        ({ringSite (coreSite e i),ringSite (coreSite e (coreNext i)),hubSite b} : Finset (Fin 11))) := by
  decide +kernel

theorem CoreFans.faces_injective {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (F : CoreFans R) : Function.Injective F.faces := by
  intro i j he
  have hs := congrArg (labelSet R) he
  rw [F.labels,F.labels] at hs
  exact (core_ring_pair_hub_unique F.ear.center i j _ _ hs).1

theorem actual_common_ring_has_central_triangle {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {k : Fin 11} (hk : k ∈ ringNeighbors R 9 ∩ ringNeighbors R 10) :
    ∃ A : R.Index, 9 ∈ labelSet R A ∧ 10 ∈ labelSet R A ∧ k ∈ labelSet R A := by
  obtain ⟨P⟩ := (actual_two_ring_paths h hr R).1
  rw [actual_common_neighbors_are_endpoints h hr R P] at hk
  rcases Finset.mem_insert.mp hk with he | hk
  · obtain ⟨A,h9,h10,hf⟩ := P.first_central
    exact ⟨A,h9,h10,he ▸ hf⟩
  · have he := Finset.mem_singleton.mp hk
    obtain ⟨A,h9,h10,hl⟩ := P.last_central
    exact ⟨A,h9,h10,he ▸ hl⟩

theorem pair_three_distinct_false {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {i j : Fin 11} {A B C : R.Index}
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hA : A ∈ pairTriangles R i j) (hB : B ∈ pairTriangles R i j)
    (hC : C ∈ pairTriangles R i j) (hc : (pairTriangles R i j).card=2) : False := by
  classical
  have hs : ({A,B,C} : Finset R.Index) ⊆ pairTriangles R i j := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hC
  have hh := Finset.card_le_card hs
  rw [hc] at hh
  simp [hAB,hAC,hBC] at hh

theorem CoreFans.ring_to_hub_neighbors {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (F : CoreFans R) (i : Fin 8) :
    Neighbor R (ringSite (coreSite F.ear.center i)) (hubSite (F.colors i)) ∧
      Neighbor R (ringSite (coreSite F.ear.center i)) (hubSite (F.colors (i-1))) := by
  have hn : coreNext (i-1)=i := by unfold coreNext; rw [sub_add_cancel]
  have hprev := F.labels (i-1)
  rw [hn] at hprev
  have hne (b : Bool) : hubSite b ≠ ringSite (coreSite F.ear.center i) :=
    ActualSelectedSkipChordEar.hub_ne_ring (hubSite_hub b) (coreSite F.ear.center i).isLt
  exact ⟨⟨hne _,F.faces i,by rw [F.labels]; simp,by rw [F.labels]; simp⟩,
    ⟨hne _,F.faces (i-1),by rw [hprev]; simp,by rw [hprev]; simp⟩⟩

theorem CoreFans.transition_iff_common_ring {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (F : CoreFans R) (i : Fin 8) :
    F.colors (i-1) ≠ F.colors i ↔
      ringSite (coreSite F.ear.center i) ∈ ringNeighbors R 9 ∩ ringNeighbors R 10 := by
  classical
  have hn := CoreFans.ring_to_hub_neighbors F i
  constructor
  · intro hc
    have hh : Neighbor R (ringSite (coreSite F.ear.center i)) 9 ∧
        Neighbor R (ringSite (coreSite F.ear.center i)) 10 := by
      cases hL : F.colors (i-1) <;> cases hR : F.colors i
      · exact (hc (hL.trans hR.symm)).elim
      · have hh := hn
        simp only [hL,hR,hubSite,Bool.false_eq_true,if_false,if_true] at hh
        exact hh
      · have hh := hn
        simp only [hL,hR,hubSite,Bool.false_eq_true,if_false,if_true] at hh
        exact ⟨hh.2,hh.1⟩
      · exact (hc (hL.trans hR.symm)).elim
    exact Finset.mem_inter.mpr ⟨(mem_ringNeighbors R).mpr
      ⟨neighbor_symm hh.1,(coreSite F.ear.center i).isLt⟩,
      (mem_ringNeighbors R).mpr ⟨neighbor_symm hh.2,(coreSite F.ear.center i).isLt⟩⟩
  · intro hc he
    obtain ⟨A,hA9,hA10,hAS⟩ := actual_common_ring_has_central_triangle h hr R hc
    let S := ringSite (coreSite F.ear.center i)
    let U := hubSite (F.colors i)
    have hSnU : S ≠ U := (ActualSelectedSkipChordEar.hub_ne_ring (hubSite_hub (F.colors i))
      (coreSite F.ear.center i).isLt).symm
    have hD := F.labels (i-1)
    have hE := F.labels i
    have hnxt : coreNext (i-1)=i := by unfold coreNext; rw [sub_add_cancel]
    rw [hnxt,he] at hD
    have hDS : S ∈ labelSet R (F.faces (i-1)) := by rw [hD]; simp [S]
    have hDU : U ∈ labelSet R (F.faces (i-1)) := by rw [hD]; simp [U]
    have hES : S ∈ labelSet R (F.faces i) := by rw [hE]; simp [S]
    have hEU : U ∈ labelSet R (F.faces i) := by rw [hE]; simp [U]
    have hAU : U ∈ labelSet R A := by
      dsimp [U]
      cases hB : F.colors i
      · exact hA10
      · exact hA9
    have hDEA : F.faces (i-1) ≠ F.faces i := by
      intro hh
      have hh' := (CoreFans.faces_injective F) hh
      have hi : coreNext (i-1) ≠ i-1 := core_next_ne (i-1)
      rw [hnxt] at hi
      exact hi hh'.symm
    have hDA : F.faces (i-1) ≠ A := by
      intro hh
      have hc : 9 ∈ labelSet R (F.faces (i-1)) ∧ 10 ∈ labelSet R (F.faces (i-1)) := by
        rw [hh]; exact ⟨hA9,hA10⟩
      rw [F.labels] at hc
      exact core_triangle_not_central F.ear.center (i-1) (F.colors (i-1)) hc
    have hEA : F.faces i ≠ A := by
      intro hh
      have hc : 9 ∈ labelSet R (F.faces i) ∧ 10 ∈ labelSet R (F.faces i) := by
        rw [hh]; exact ⟨hA9,hA10⟩
      rw [F.labels] at hc
      exact core_triangle_not_central F.ear.center i (F.colors i) hc
    have hnon : ¬ BoundaryLabels S U := by
      intro hh
      have hb := boundary_labels_right_ring S U hh
      have hhub := hubSite_hub (F.colors i)
      change 9 ≤ U.val at hhub
      omega
    have hcard := actual_selected_edge_incidence h hr R hSnU hDS hDU
    rw [if_neg hnon] at hcard
    exact pair_three_distinct_false R hDEA hDA hEA
      (mem_pairTriangles.mpr ⟨hDS,hDU⟩) (mem_pairTriangles.mpr ⟨hES,hEU⟩)
      (mem_pairTriangles.mpr ⟨hAS,hAU⟩) hcard

end N11Formalization.ActualQ1CoreTransitions
#check @N11Formalization.ActualQ1CoreTransitions.CoreFans.transition_iff_common_ring
#print axioms N11Formalization.ActualQ1CoreTransitions.CoreFans.transition_iff_common_ring
