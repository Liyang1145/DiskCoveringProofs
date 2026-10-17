import N11Formalization.ActualBoundaryFacets

/-! Each boundary neighbor facet has a REAL third-site nearest endpoint
strictly inside D, with distance<=the ORIGINAL r. Compact clipping pays
first-exit/maximality; ring-cap tie uniqueness rules out a second boundary
endpoint. The third label is produced, NOT asserted to be a hub. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryFacetEndpoints
open ActualBoundaryFacets ActualCoverStructuralReduction ActualBoundaryNeighborTies
open ActualRingDirectionOrder ActualBoundaryCyclicOrder ActualVoronoiCells
open ActualVoronoiRadialExit ActualHubEdgeGeometry

structure BoundaryVertex (c : Fin 11 → Point) (r : ℝ) (i : Fin 9) where
  point : Point
  third : Fin 11
  third_ne_left : third ≠ ringSite i
  third_ne_right : third ≠ ringSite (nextRing i)
  inside : ‖point‖ < 1
  nearest : point ∈ Cell c (ringSite i) ∩ Cell c (ringSite (nextRing i))
  third_tie : dist point (c third) = dist point (c (ringSite i))
  radius : dist point (c (ringSite i)) ≤ r

theorem boundary_vertex_of_start {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) (v : NeighborTie c r i)
    (f : FacetStart c (circleMap v.angle) (ringSite i) (ringSite (nextRing i))) :
    Nonempty (BoundaryVertex c r i) := by
  classical
  let x := circleMap v.angle
  let S : Set ℝ := {t | 0 ≤ t ∧ ‖ray x f.direction t‖ ≤ 1 ∧
    ray x f.direction t ∈ Cell c (ringSite i) ∩ Cell c (ringSite (nextRing i))}
  have hRay : Continuous (ray x f.direction) := by
    change Continuous (fun t : ℝ => x+t • f.direction)
    fun_prop
  have hclosed : IsClosed S := by
    have hn : IsClosed {t : ℝ | ‖ray x f.direction t‖ ≤ 1} :=
      isClosed_le hRay.norm continuous_const
    have hp : IsClosed {t : ℝ | ray x f.direction t ∈
        Cell c (ringSite i) ∩ Cell c (ringSite (nextRing i))} :=
      ((cell_closed c (ringSite i)).inter (cell_closed c (ringSite (nextRing i)))).preimage
        hRay
    exact isClosed_Ici.inter (hn.inter hp)
  have hsub : S ⊆ Set.Icc 0 2 := by
    intro t ht
    refine ⟨ht.1,?_⟩
    have hdist := dist_le_norm_add_norm (ray x f.direction t) x
    rw [ray_dist _ _ _ f.unit,abs_of_nonneg ht.1] at hdist
    have hx : ‖x‖ = 1 := circleMap_norm v.angle
    linarith [ht.2.1]
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed hsub
  have hftime : f.time ∈ S := ⟨f.positive.le,f.inside.le,f.nearest⟩
  obtain ⟨t,ht,hmax⟩ := hcompact.exists_isMaxOn ⟨f.time,hftime⟩ continuous_id.continuousOn
  have htpos : 0 < t := f.positive.trans_le (hmax hftime)
  let y := ray x f.direction t
  have hy : y ∈ Cell c (ringSite i) ∩ Cell c (ringSite (nextRing i)) := ht.2.2
  have hyr : dist y (c (ringSite i)) ≤ r :=
    nearest_le_radius h.cover (mem_unitDisk.mpr ht.2.1) hy.1
  have hyeq : dist y (c (ringSite i)) = dist y (c (ringSite (nextRing i))) :=
    le_antisymm (hy.1 (ringSite (nextRing i))) (hy.2 (ringSite i))
  have hyinside : ‖y‖ < 1 := by
    by_contra hnot
    have hynorm : ‖y‖ = 1 := le_antisymm ht.2.1 (le_of_not_gt hnot)
    have he := ActualBoundaryTieUniqueness.Representative.unique_ring_cap_tie h
      (by linarith : r < 1) (next_ne i) (circleMap_norm v.angle) hynorm
      v.equidistant hyeq v.radius hyr
    have hdist : dist y x = t := by
      rw [ray_dist _ _ _ f.unit,abs_of_pos htpos]
    have hyx : y = x := he.symm
    rw [hyx,dist_self] at hdist
    linarith
  have hthird : ∃ k : Fin 11, k ≠ ringSite i ∧ k ≠ ringSite (nextRing i) ∧
      dist y (c k) = dist y (c (ringSite i)) := by
    by_contra hnone
    have hs : y ∈ PairStrict c (ringSite i) (ringSite (nextRing i)) := by
      intro k hki hkj
      have hle := hy.1 k
      have hne : dist y (c k) ≠ dist y (c (ringSite i)) := fun he => hnone ⟨k,hki,hkj,he⟩
      exact lt_of_le_of_ne hle hne.symm
    let O := {z : Point | ‖z‖ < 1} ∩ PairStrict c (ringSite i) (ringSite (nextRing i))
    have hopen : IsOpen O := (isOpen_lt (by fun_prop) continuous_const).inter (pairStrict_open _ _ _)
    obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp hopen y ⟨hyinside,hs⟩
    let z := ray y f.direction (eps/2)
    have hzO : z ∈ O := by
      apply hball
      apply Metric.mem_ball.mpr
      rw [ray_dist _ _ _ f.unit,abs_of_pos (by linarith : 0 < eps/2)]
      linarith
    have heq : dist z (c (ringSite i)) = dist z (c (ringSite (nextRing i))) :=
      shifted_equidistant hyeq f.orthogonal
    have hzpair := pair_nearest_of_strict heq hzO.2
    have hz : z = ray x f.direction (t+eps/2) := by
      dsimp [z,y,ray]
      rw [add_smul]
      abel
    have hmem : t+eps/2 ∈ S := by
      refine ⟨by linarith,?_,?_⟩
      · rw [← hz]
        exact hzO.1.le
      · rw [← hz]
        exact hzpair
    have hle := hmax hmem
    change t+eps/2 ≤ t at hle
    linarith
  obtain ⟨k,hki,hkj,hktie⟩ := hthird
  exact ⟨⟨y,k,hki,hkj,hyinside,hy,hktie,hyr⟩⟩

theorem Representative.boundary_vertex {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (i : Fin 9) (v : NeighborTie c r i) :
    Nonempty (BoundaryVertex c r i) := by
  obtain ⟨f⟩ := ActualBoundaryFacets.Representative.boundary_facet_start h hr i v
  exact boundary_vertex_of_start h hr i v f

end N11Formalization.ActualBoundaryFacetEndpoints
#check @N11Formalization.ActualBoundaryFacetEndpoints.Representative.boundary_vertex
#print axioms N11Formalization.ActualBoundaryFacetEndpoints.Representative.boundary_vertex
