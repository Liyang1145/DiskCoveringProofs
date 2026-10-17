import N11Formalization.ActualPuncturedDiskConnected
import N11Formalization.ActualClippedDualSkeleton

/-! The ACTUAL positive clipped-facet graph on all11 sites is connected.
Every proper nonempty site cut has a positive facet across it: otherwise
closed unions of cells separate the genuinely path-connected punctured open
disk. No graph-connectedness/Euler/planarity input is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualPositiveFacetGraph
open ActualVoronoiCells ActualVoronoiIncidence ActualClippedFacetIntervals
open ActualClippedCellPartition ActualPuncturedDiskConnected ActualCoverStructuralReduction
open ActualIncidentFacetGerms ActualVoronoiRadialExit ActualHubEdgeGeometry

def PositivePair (c : Fin 11 → Point) (i j : Fin 11) : Prop :=
  i ≠ j ∧ ∃ x ∈ ClippedCommon c i j, ∃ y ∈ ClippedCommon c i j, x ≠ y

theorem PositivePair.symm {c : Fin 11 → Point} {i j : Fin 11}
    (hij : PositivePair c i j) : PositivePair c j i := by
  obtain ⟨hij,x,hx,y,hy,hxy⟩ := hij
  exact ⟨hij.symm,x,⟨hx.1,hx.2.2,hx.2.1⟩,y,⟨hy.1,hy.2.2,hy.2.1⟩,hxy⟩

def graph (c : Fin 11 → Point) : SimpleGraph (Fin 11) where
  Adj := PositivePair c
  symm := ⟨fun _ _ h => PositivePair.symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem center_not_vertex {c : Fin 11 → Point} (hc : Function.Injective c)
    (i : Fin 11) : c i ∉ Vertices c := by
  intro hx
  obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp ha
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hb
  have hxnear := hk.2.2.2
  have hA : c i = c a := dist_eq_zero.mp (le_antisymm
    (by simpa only [dist_self] using hxnear.1.1 i) dist_nonneg)
  have hB : c i = c b := dist_eq_zero.mp (le_antisymm
    (by simpa only [dist_self] using hxnear.1.2 i) dist_nonneg)
  exact hk.1 (hc (hA.symm.trans hB))

theorem vertex_free_pair_positive {c : Fin 11 → Point} {r : ℝ}
    (hc : Function.Injective c) (hcover : Covers c r) {i j : Fin 11}
    (hij : i ≠ j) {x : Point} (hx : ‖x‖ < 1) (hxv : x ∉ ClippedVertices c)
    (hpair : x ∈ Cell c i ∩ Cell c j) : PositivePair c i j := by
  let d := perp (c j-c i)
  have hd : d ≠ 0 := perp_ne (sub_ne_zero.mpr (fun he => hij (hc he).symm))
  have hcone : d ∈ PairCone c x i j := by
    refine ⟨perp_inner _,?_⟩
    intro k hk hki hkj
    exact (hxv ⟨mem_unitDisk.mpr hx.le,triple_mem_vertices hij hki hkj
      hpair.1 hpair.2 (mem_incident.mp hk)⟩).elim
  obtain ⟨g⟩ := facetGerm_of_pairCone hcover hx (mem_incident.mpr hpair.1)
    (mem_incident.mpr hpair.2) hcone hd
  have hhalf : 0 < g.time/2 := by linarith [g.positive]
  have hle : g.time/2 ≤ g.time := by linarith [g.positive]
  exact ⟨hij,ray x g.direction (g.time/2),
    ⟨mem_unitDisk.mpr (g.inside _ hhalf hle).le,g.nearest _ hhalf hle⟩,
    ray x g.direction g.time,
    ⟨mem_unitDisk.mpr (g.inside _ g.positive le_rfl).le,g.nearest _ g.positive le_rfl⟩,
    ActualIncidentFacetGerms.FacetGerm.positive_segment g⟩

def CellUnion (c : Fin 11 → Point) (s : Finset (Fin 11)) : Set Point :=
  ⋃ i ∈ s, Cell c i

theorem cellUnion_closed (c : Fin 11 → Point) (s : Finset (Fin 11)) :
    IsClosed (CellUnion c s) := isClosed_biUnion_finset (fun i _ => cell_closed c i)

theorem positive_cut_edge {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (s : Finset (Fin 11)) (hs : s.Nonempty)
    (hproper : ∃ j : Fin 11, j ∉ s) :
    ∃ i ∈ s, ∃ j : Fin 11, j ∉ s ∧ PositivePair c i j := by
  classical
  by_contra hnone
  let A := CellUnion c s
  let B := CellUnion c (Finset.univ \ s)
  let X := OpenDisk \ ClippedVertices c
  have hconn : IsPreconnected X :=
    (actual_punctured_disk_pathConnected h.injective).isConnected.isPreconnected
  have hcover : X ⊆ A ∪ B := by
    intro x hx
    obtain ⟨i,hi⟩ := exists_nearest c x
    by_cases his : i ∈ s
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨his,hi⟩⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,his⟩,hi⟩⟩)
  have hdis : X ∩ (A ∩ B) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hA,hB⟩
    obtain ⟨i,hI⟩ := Set.mem_iUnion.mp hA
    obtain ⟨his,hi⟩ := Set.mem_iUnion.mp hI
    obtain ⟨j,hJ⟩ := Set.mem_iUnion.mp hB
    obtain ⟨hjs,hj⟩ := Set.mem_iUnion.mp hJ
    have hnot := (Finset.mem_sdiff.mp hjs).2
    have hij : i ≠ j := fun he => hnot (he ▸ his)
    exact hnone ⟨i,his,j,hnot,vertex_free_pair_positive h.injective h.cover hij
      (mem_openDisk.mp hx.1) hx.2 ⟨hi,hj⟩⟩
  have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp hconn A B
    (cellUnion_closed c s) (cellUnion_closed c (Finset.univ \ s)) hcover hdis
  have hcenterX (i : Fin 11) : c i ∈ X :=
    ⟨mem_openDisk.mpr (h.center_inside i),fun hi => center_not_vertex h.injective i hi.2⟩
  have hcenterLabels (i : Fin 11) {j : Fin 11} (hj : c i ∈ Cell c j) : i = j := by
    apply h.injective
    apply dist_eq_zero.mp
    apply le_antisymm
    · simpa only [dist_self] using hj i
    · exact dist_nonneg
  rcases hsplit with hA | hB
  · obtain ⟨j,hjnot⟩ := hproper
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hA (hcenterX j))
    obtain ⟨his,hi⟩ := Set.mem_iUnion.mp hi
    have he := hcenterLabels j hi
    exact hjnot (he ▸ his)
  · obtain ⟨i,his⟩ := hs
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hB (hcenterX i))
    obtain ⟨hjs,hj⟩ := Set.mem_iUnion.mp hj
    have he := hcenterLabels i hj
    exact (Finset.mem_sdiff.mp hjs).2 (he ▸ his)

theorem actual_graph_connected {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) : (graph c).Connected := by
  classical
  refine ⟨?_⟩
  intro u v
  by_contra hnot
  let s := Finset.univ.filter (fun i => (graph c).Reachable u i)
  have hus : u ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,SimpleGraph.Reachable.rfl⟩
  have hvnot : v ∉ s := by intro hv; exact hnot (Finset.mem_filter.mp hv).2
  obtain ⟨i,his,j,hjnot,hij⟩ := positive_cut_edge h s ⟨u,hus⟩ ⟨v,hvnot⟩
  have hreach := (Finset.mem_filter.mp his).2
  have hAdj : (graph c).Adj i j := hij
  exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hreach.trans hAdj.reachable⟩)

end N11Formalization.ActualPositiveFacetGraph
#check @N11Formalization.ActualPositiveFacetGraph.positive_cut_edge
#check @N11Formalization.ActualPositiveFacetGraph.actual_graph_connected
#print axioms N11Formalization.ActualPositiveFacetGraph.vertex_free_pair_positive
#print axioms N11Formalization.ActualPositiveFacetGraph.positive_cut_edge
#print axioms N11Formalization.ActualPositiveFacetGraph.actual_graph_connected
