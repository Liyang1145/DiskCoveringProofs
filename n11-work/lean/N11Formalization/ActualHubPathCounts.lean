import N11Formalization.ActualRefinementEulerCount

/-! Exact actual hub path counts and endpoint-only overlap.
This does not choose canonical0/4 or pay metric exclusions. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubPathCounts
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualHubTriangleCensus
open ActualRefinementEulerCount ActualHubNeighborCoverage ActualRefinementEarCount
open ActualHubRingPaths ActualCentralRingEndpoints ActualRefinementVertexLinks

theorem actual_common_ring_neighbors_card {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (ringNeighbors R 9 ∩ ringNeighbors R 10).card = 2 := by
  have hf := actual_faces_eq_nine_add_common_neighbors h hr R
  rw [actual_faces_eleven h hr R] at hf
  omega

theorem central_ring_in_both_paths {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {a : R.Index} {k : Fin 11} (hk : k.val < 9)
    (h9 : 9 ∈ labelSet R a) (h10 : 10 ∈ labelSet R a) (hK : k ∈ labelSet R a) :
    k ∈ ringNeighbors R 9 ∩ ringNeighbors R 10 := by
  have hk9 : k ≠ (9 : Fin 11) := by intro he; subst k; norm_num at hk
  have hk10 : k ≠ (10 : Fin 11) := by intro he; subst k; norm_num at hk
  exact Finset.mem_inter.mpr ⟨(mem_ringNeighbors R).mpr ⟨⟨hk9,a,h9,hK⟩,hk⟩,
    (mem_ringNeighbors R).mpr ⟨⟨hk10,a,h10,hK⟩,hk⟩⟩

theorem actual_common_neighbors_are_endpoints {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (P : RingPath R 9 10) :
    ringNeighbors R 9 ∩ ringNeighbors R 10 = {P.first,P.last} := by
  classical
  obtain ⟨A,hA9,hA10,hAf⟩ := P.first_central
  obtain ⟨B,hB9,hB10,hBl⟩ := P.last_central
  have hf := central_ring_in_both_paths R (P.ring_vertices _ P.walk.start_mem_support) hA9 hA10 hAf
  have hl := central_ring_in_both_paths R (P.ring_vertices _ P.walk.end_mem_support) hB9 hB10 hBl
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    rcases Finset.mem_insert.mp hk with he | hk
    · exact he ▸ hf
    · exact Finset.mem_singleton.mp hk ▸ hl
  · rw [actual_common_ring_neighbors_card h hr R]
    simp [P.endpoints_ne]

theorem actual_ring_path_vertex_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (P : RingPath R 9 10) (Q : RingPath R 10 9) :
    P.walk.support.toFinset.card + Q.walk.support.toFinset.card +
      (ringOnlyTriangles R).card = 11 := by
  classical
  rw [ring_path_vertices_eq R (Or.inl ⟨rfl,rfl⟩) P,
    ring_path_vertices_eq R (Or.inr ⟨rfl,rfl⟩) Q]
  have hf := actual_ring_neighbor_face_census h hr R
  rw [actual_faces_eleven h hr R] at hf
  omega

theorem actual_ring_path_edge_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (P : RingPath R 9 10) (Q : RingPath R 10 9) :
    P.walk.length + Q.walk.length + (ringOnlyTriangles R).card = 9 := by
  classical
  have hp : P.walk.support.toFinset.card = P.walk.length+1 := by
    rw [List.toFinset_card_of_nodup P.simple.support_nodup,SimpleGraph.Walk.length_support]
  have hq : Q.walk.support.toFinset.card = Q.walk.length+1 := by
    rw [List.toFinset_card_of_nodup Q.simple.support_nodup,SimpleGraph.Walk.length_support]
  have hh := actual_ring_path_vertex_count h hr R P Q
  rw [hp,hq] at hh
  omega

theorem actual_hub_degree_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) :
    (neighbors R 9).card + (neighbors R 10).card + (ringOnlyTriangles R).card = 13 := by
  have hf := actual_total_face_census h hr R
  rw [actual_faces_eleven h hr R] at hf
  omega

end N11Formalization.ActualHubPathCounts
#check @N11Formalization.ActualHubPathCounts.actual_common_neighbors_are_endpoints
#check @N11Formalization.ActualHubPathCounts.actual_ring_path_edge_count
#check @N11Formalization.ActualHubPathCounts.actual_hub_degree_sum
#print axioms N11Formalization.ActualHubPathCounts.actual_common_neighbors_are_endpoints
#print axioms N11Formalization.ActualHubPathCounts.actual_ring_path_edge_count
