import N11Formalization.ActualRingLinkSimplePaths
import N11Formalization.ActualCentralRingEndpoints
import N11Formalization.ActualRefinementEarCount

/-! Productive ACTUAL local-surface data of the same-radius arbitrary-cover
representative. Every displayed condition is derived from the real cover.
This deliberately does NOT assert global disk topology, Euler F=11,
complementary two-fan boundary order/lengths, metric exclusions or canonical33. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualLocalSurfaceData
open ActualVoronoiCells ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementInteriorFacetCount
open ActualSelectedEdgeIncidence ActualRefinementDoubleCounting
open ActualRefinementEarCount ActualRefinementHubCount ActualRefinementBoundaryCount
open ActualRefinementLocalLinks ActualRefinementVertexLinks ActualRingLinkConnected
open ActualRingLinkSimplePaths ActualHubLinkCycles ActualHubRingPaths ActualCentralRingEndpoints

structure LocalData (c : Fin 11 → Point) (r : ℝ) where
  refinement : Refinement c r
  real_triangles : ∀ a : refinement.Index,
    ‖refinement.witness a‖ < 1 ∧
      ∀ v : Fin 3, refinement.witness a ∈ Cell c (refinement.labels a v) ∧
        dist (refinement.witness a) (c (refinement.labels a v)) ≤ r
  distinct_triangles : Function.Injective (labelSet refinement)
  interior_disjoint : ∀ a b : refinement.Index, a ≠ b →
    Disjoint (interior (refinement.hull a)) (interior (refinement.hull b))
  all_links_connected : ∀ i j k : Fin 11, Neighbor refinement i j →
    Neighbor refinement i k → (linkGraph refinement i).Reachable j k
  ring_link_paths : ∀ i : Fin 9, Nonempty (LinkPath refinement i)
  hub_link_cycles :
    (∃ p : (linkGraph refinement 9).Walk 10 10, p.IsCycle ∧
      p.toSubgraph.verts = {j : Fin 11 | Neighbor refinement 9 j}) ∧
    (∃ p : (linkGraph refinement 10).Walk 9 9, p.IsCycle ∧
      p.toSubgraph.verts = {j : Fin 11 | Neighbor refinement 10 j})
  hub_ring_paths : ∃ (P : RingPath refinement 9 10) (Q : RingPath refinement 10 9),
    ({P.first,P.last} : Finset (Fin 11)) = {Q.first,Q.last}
  edge_incidence : ∀ i j : Fin 11, i ≠ j → ∀ a : refinement.Index,
    i ∈ labelSet refinement a → j ∈ labelSet refinement a →
      (pairTriangles refinement i j).card = if BoundaryLabels i j then 1 else 2
  ear_count : (ringOnlyTriangles refinement).card ≤ 1
  central_count : (hubTriangles refinement).card = 2
  boundary_count : ∀ i : Fin 9, (boundaryTriangles refinement i).card = 1
  double_count : 3*Fintype.card refinement.Index+9 = 2*(edges refinement).card

theorem actual_local_data {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) : Nonempty (LocalData c r) := by
  obtain ⟨R⟩ := actual_refinement h hr
  refine ⟨⟨R,?_,labelSet_injective h.injective R,?_,?_,?_,
    actual_hub_cycle_through_other_hub h hr R,actual_two_paths_common_endpoints h hr R,
    ?_,actual_selected_ear_count h hr R,actual_hub_triangle_count h hr R,
    actual_boundary_triangle_count h hr R,actual_triangle_edge_double_count h hr R⟩⟩
  · intro a
    exact ⟨(Refinement.real_triangle R a).1,(Refinement.real_triangle R a).2.1⟩
  · intro a b hab
    exact Refinement.triangles_interior_disjoint R hab
  · intro i j k hj hk
    exact actual_all_site_links_reachable h hr R i hj hk
  · intro i
    exact actual_ring_link_simple_path h hr R i
  · intro i j hij a hai haj
    exact actual_selected_edge_incidence h hr R hij hai haj

end N11Formalization.ActualLocalSurfaceData
#print N11Formalization.ActualLocalSurfaceData.LocalData
#check @N11Formalization.ActualLocalSurfaceData.actual_local_data
#print axioms N11Formalization.ActualLocalSurfaceData.actual_local_data
