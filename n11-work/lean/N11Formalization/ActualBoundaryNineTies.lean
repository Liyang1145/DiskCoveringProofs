import N11Formalization.ActualBoundaryNeighborTies
import N11Formalization.ActualBoundaryOverlapAdjacency

/-! Exactly NINE distinct genuine nearest-tie POINTS on the whole circle.
They are constructed from the actual cover, with no switch-count or
circle-minus-finite-set assumption. The claim that each is an ownership
switch is a separate subsequent theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryNineTies
open DSHTopologyInterior ActualRingDirectionOrder ActualBoundaryArcFrame
open ActualBoundaryCyclicOrder ActualBoundaryNeighborTies ActualBoundaryNearestPairs
open ActualBoundaryOverlapAdjacency ActualCoverStructuralReduction ActualVoronoiCells

theorem ringSite_inj {i j : Fin 9} (he : ringSite i = ringSite j) : i = j :=
  Fin.ext (congrArg (fun k : Fin 11 => k.val) he)

theorem next_inj {i j : Fin 9} (he : nextRing i = nextRing j) : i = j :=
  add_right_cancel he

theorem next_next_ne (i : Fin 9) : nextRing (nextRing i) ≠ i := by
  fin_cases i <;> decide

theorem pair_index_unique {i j : Fin 9}
    (h1 : i = j ∨ i = nextRing j) (h2 : nextRing i = j ∨ nextRing i = nextRing j) :
    i = j := by
  rcases h1 with he | he
  · exact he
  rcases h2 with hn | hn
  · rw [he] at hn
    exact False.elim (next_next_ne j hn)
  · exact next_inj hn

theorem tie_points_injective {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (v : ∀ i : Fin 9, NeighborTie c r i) :
    Function.Injective (fun i => circleMap (v i).angle) := by
  intro i j heq
  change circleMap (v i).angle = circleMap (v j).angle at heq
  have hi : circleMap (v j).angle ∈ Cell c (ringSite i) := by rw [← heq]; exact (v i).nearest.1
  have hin : circleMap (v j).angle ∈ Cell c (ringSite (nextRing i)) := by
    rw [← heq]
    exact (v i).nearest.2
  have hjn : ringSite j ≠ ringSite (nextRing j) := fun h => next_ne j (ringSite_inj h)
  have h1 := nearest_one_of_pair hc hr hR (circleMap_norm (v j).angle) hjn
    (v j).nearest.1 (v j).nearest.2 hi
  have h2 := nearest_one_of_pair hc hr hR (circleMap_norm (v j).angle) hjn
    (v j).nearest.1 (v j).nearest.2 hin
  exact pair_index_unique (h1.imp ringSite_inj ringSite_inj) (h2.imp ringSite_inj ringSite_inj)

structure NineTies (c : Fin 11 → Point) (r : ℝ) where
  tie : ∀ i : Fin 9, NeighborTie c r i
  injective : Function.Injective (fun i => circleMap (tie i).angle)

theorem nineTies_of_cover {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) : Nonempty (NineTies c r) := by
  classical
  let v : ∀ i : Fin 9, NeighborTie c r i := fun i => Classical.choice (neighbor_tie hc hr hR ho i)
  exact ⟨⟨v,tie_points_injective hc hr hR v⟩⟩

def BoundaryTie (c : Fin 11 → Point) (x : Point) : Prop :=
  ‖x‖ = 1 ∧ ∃ i j : Fin 11, i ≠ j ∧ x ∈ Cell c i ∩ Cell c j

theorem nearest_ring_pair_adjacent {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (ho : StrictMono (midpointAngle c)) {i j : Fin 9} (hij : i ≠ j)
    {x : Point} (hx : ‖x‖ = 1)
    (hi : x ∈ Cell c (ringSite i)) (hj : x ∈ Cell c (ringSite j)) :
    j = nextRing i ∨ i = nextRing j := by
  let t := circleAngle x
  have hp : circleMap t = x := circleMap_circleAngle _ hx
  have hri := nearest_le_radius hc (mem_unitDisk.mpr hx.le) hi
  have hrj := nearest_le_radius hc (mem_unitDisk.mpr hx.le) hj
  rw [← hp] at hri hrj
  obtain ⟨n,hn⟩ := (cap_iff_lift hc hr hR i t).mp hri
  obtain ⟨m,hm⟩ := (cap_iff_lift hc hr hR j t).mp hrj
  exact overlap_adjacent hc hr hR ho hij hn hm

/-- The full actual tie set equals the nine produced points, not merely
a finite upper bound or a conditional switch-count assertion. -/
theorem NineTies.tie_set_eq_range {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) :
    {x : Point | BoundaryTie c x} = Set.range (fun i => circleMap (v.tie i).angle) := by
  ext x
  constructor
  · rintro ⟨hx,i,j,hij,hxi,hxj⟩
    let I : Fin 9 := ⟨i.val,nearest_ring h.cover h.labels hx hxi⟩
    let J : Fin 9 := ⟨j.val,nearest_ring h.cover h.labels hx hxj⟩
    have hIJ : I ≠ J := by
      intro he
      exact hij (Fin.ext (congrArg (fun k : Fin 9 => k.val) he))
    have hxI : x ∈ Cell c (ringSite I) := hxi
    have hxJ : x ∈ Cell c (ringSite J) := hxj
    have hrad := nearest_le_radius h.cover (mem_unitDisk.mpr hx.le) hxI
    have heq : dist x (c (ringSite I)) = dist x (c (ringSite J)) :=
      le_antisymm (hxI (ringSite J)) (hxJ (ringSite I))
    rcases nearest_ring_pair_adjacent h.cover hr h.labels h.midpoint_order hIJ hx hxI hxJ with hn | hn
    · refine ⟨I,?_⟩
      have he := ActualBoundaryTieUniqueness.Representative.unique_ring_cap_tie h
        (by linarith : r < 1) (next_ne I) hx (circleMap_norm (v.tie I).angle)
        (by simpa only [← hn] using heq) (v.tie I).equidistant hrad (v.tie I).radius
      exact he.symm
    · refine ⟨J,?_⟩
      have hradJ := nearest_le_radius h.cover (mem_unitDisk.mpr hx.le) hxJ
      have he := ActualBoundaryTieUniqueness.Representative.unique_ring_cap_tie h
        (by linarith : r < 1) (next_ne J) hx (circleMap_norm (v.tie J).angle)
        (by simpa only [← hn] using heq.symm) (v.tie J).equidistant hradJ (v.tie J).radius
      exact he.symm
  · rintro ⟨i,rfl⟩
    exact ⟨circleMap_norm _,ringSite i,ringSite (nextRing i),
      fun he => next_ne i (ringSite_inj he),(v.tie i).nearest⟩

theorem NineTies.tie_set_card {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) :
    {x : Point | BoundaryTie c x}.ncard = 9 := by
  rw [v.tie_set_eq_range h hr]
  simpa using Set.ncard_range_of_injective v.injective

end N11Formalization.ActualBoundaryNineTies
#check @N11Formalization.ActualBoundaryNineTies.nineTies_of_cover
#check @N11Formalization.ActualBoundaryNineTies.NineTies.tie_set_card
#print axioms N11Formalization.ActualBoundaryNineTies.nineTies_of_cover
#print axioms N11Formalization.ActualBoundaryNineTies.NineTies.tie_set_card
