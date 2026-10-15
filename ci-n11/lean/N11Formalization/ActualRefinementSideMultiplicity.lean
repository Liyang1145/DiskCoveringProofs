import N11Formalization.ActualRefinementFacetRetention
import N11Formalization.ActualRefinementTriangleUniqueness

/-! At a fixed true primal endpoint, each positive facet side occurs in
exactly one selected local fan triangle. Together with complete clipped
facet endpoints, this pays actual boundary-pair one-face and hub-pair
two-witness incidence without an Euler/disk hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementSideMultiplicity
open ActualVoronoiCells ActualVoronoiIncidence ActualCoverStructuralReduction
open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualIncidentFanRefinement ActualIncidentPolygonOrder ActualClippedFacetIntervals
open ActualClippedFacetInterior ActualIncidentFacetAdjacency ActualRefinementFacetRetention
open ActualBoundaryFacetUniqueness ActualHubFacetComplete ActualVoronoiRadialExit
open ActualRingDirectionOrder ActualBoundaryCyclicOrder ActualBoundaryNeighborTies

theorem selected_side_unique {n : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≤ 5) :
    ∀ i k l : Fin n, FanIndex k → FanIndex l →
      i ∈ indexTriangle (by omega : 0 < n) k →
      finRotate n i ∈ indexTriangle (by omega : 0 < n) k →
      i ∈ indexTriangle (by omega : 0 < n) l →
      finRotate n i ∈ indexTriangle (by omega : 0 < n) l → k = l := by
  interval_cases n <;> decide +revert

theorem local_label_mem {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (v : R.vertices)
    (k : {k : Fin (incident c (R.face v).point).card // FanIndex k})
    (i : Fin (incident c (R.face v).point).card) :
    ((R.order v).order i).val ∈ labelSet R ⟨v,k⟩ ↔
      i ∈ indexTriangle (by have h := (R.face v).at_least_three; omega) k.val := by
  rw [local_labelSet_image]
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
    have hji := (ActualIncidentFacetAdjacency.OrderedCircle.label_injective (R.order v)) he
    rwa [hji] at hj
  · intro hi
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩

theorem same_witness_positive_side_unique {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (hc : Function.Injective c) {i j : Fin 11} (hij : i ≠ j)
    (f : FacetInterval c i j) (hpos : f.lo < f.hi) {a b : R.Index}
    (haend : R.witness a = ray f.base f.direction f.lo ∨
      R.witness a = ray f.base f.direction f.hi)
    (hw : R.witness a = R.witness b)
    (hai : i ∈ labelSet R a) (haj : j ∈ labelSet R a)
    (hbi : i ∈ labelSet R b) (hbj : j ∈ labelSet R b) : a = b := by
  have hv : a.1 = b.1 := by
    apply Subtype.ext
    simpa only [Refinement.witness,R.base] using hw
  rcases a with ⟨v,k⟩
  rcases b with ⟨w,l⟩
  dsimp only at hv
  subst w
  let F := R.face v
  let o := R.order v
  have hn : 0 < (incident c (R.face v).point).card :=
    lt_of_lt_of_le (by decide : 0 < 3) (R.face v).at_least_three
  have hnear (z : Fin 11) (hz : z ∈ labelSet R ⟨v,k⟩) : z ∈ incident c F.point := by
    obtain ⟨q,hq⟩ := mem_labelSet.mp hz
    rw [← hq]
    exact mem_incident.mpr ((Refinement.real_triangle R ⟨v,k⟩).2.1 q).1
  let I := o.order.symm ⟨i,hnear i hai⟩
  let J := o.order.symm ⟨j,hnear j haj⟩
  have hI : (o.order I).val = i :=
    congrArg Subtype.val (o.order.apply_symm_apply ⟨i,hnear i hai⟩)
  have hJ : (o.order J).val = j :=
    congrArg Subtype.val (o.order.apply_symm_apply ⟨j,hnear j haj⟩)
  have hendpoint : F.point = ray f.base f.direction f.lo ∨
      F.point = ray f.base f.direction f.hi := haend
  have hadj := FacetInterval.endpoint_polygon_adjacent hc hij f hpos F o hendpoint hI hJ
  have hik : I ∈ indexTriangle hn k.val := by
    apply (local_label_mem R v k I).mp
    rwa [hI]
  have hjk : J ∈ indexTriangle hn k.val := by
    apply (local_label_mem R v k J).mp
    rwa [hJ]
  have hil : I ∈ indexTriangle hn l.val := by
    apply (local_label_mem R v l I).mp
    rwa [hI]
  have hjl : J ∈ indexTriangle hn l.val := by
    apply (local_label_mem R v l J).mp
    rwa [hJ]
  have hkl : k.val = l.val := by
    rcases hadj with he | he
    · have hjk' : finRotate (incident c F.point).card I ∈ indexTriangle hn k.val := he ▸ hjk
      have hjl' : finRotate (incident c F.point).card I ∈ indexTriangle hn l.val := he ▸ hjl
      exact selected_side_unique F.at_least_three F.at_most_five I k.val l.val
        k.property l.property hik hjk' hil hjl'
    · have hik' : finRotate (incident c F.point).card J ∈ indexTriangle hn k.val := he ▸ hik
      have hil' : finRotate (incident c F.point).card J ∈ indexTriangle hn l.val := he ▸ hil
      exact selected_side_unique F.at_least_three F.at_most_five J k.val l.val
        k.property l.property hjk hik' hjl hil'
  have he : k = l := Subtype.ext hkl
  rw [he]

theorem nearest_of_label_mem {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {a : R.Index} {i : Fin 11} (hi : i ∈ labelSet R a) : R.witness a ∈ Cell c i := by
  obtain ⟨v,hv⟩ := mem_labelSet.mp hi
  rw [← hv]
  exact ((Refinement.real_triangle R a).2.1 v).1

theorem boundary_pair_triangle_unique {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (h : Representative c r) (hr : r < 19/50)
    (i : Fin 9) {a b : R.Index}
    (hai : ringSite i ∈ labelSet R a) (haj : ringSite (nextRing i) ∈ labelSet R a)
    (hbi : ringSite i ∈ labelSet R b) (hbj : ringSite (nextRing i) ∈ labelSet R b) : a = b := by
  have hna : R.witness a ∈ Cell c (ringSite i) ∩ Cell c (ringSite (nextRing i)) :=
    ⟨nearest_of_label_mem R hai,nearest_of_label_mem R haj⟩
  have hnb : R.witness b ∈ Cell c (ringSite i) ∩ Cell c (ringSite (nextRing i)) :=
    ⟨nearest_of_label_mem R hbi,nearest_of_label_mem R hbj⟩
  have hva := Refinement.witness_exact_vertex R a
  have hvb := Refinement.witness_exact_vertex R b
  have hw := neighbor_nearest_vertex_unique h hr i hva hvb hna hnb
  obtain ⟨z⟩ := neighbor_tie h.cover hr h.labels h.midpoint_order i
  have hij : ringSite i ≠ ringSite (nextRing i) := by
    intro he
    exact next_ne i (Fin.ext (congrArg (fun q : Fin 11 => q.val) he))
  have hx : circleMap z.angle ∈ ClippedCommon c (ringSite i) (ringSite (nextRing i)) :=
    ⟨mem_unitDisk.mpr (circleMap_norm z.angle).le,z.nearest⟩
  have hy : R.witness a ∈ ClippedCommon c (ringSite i) (ringSite (nextRing i)) := ⟨hva.1,hna⟩
  obtain ⟨f⟩ := clippedCommon_interval h.injective hij ⟨circleMap z.angle,hx⟩
  have hxy : circleMap z.angle ≠ R.witness a := by
    intro he
    have hh := (Refinement.real_triangle R a).1
    rw [← he,circleMap_norm] at hh
    exact lt_irrefl 1 hh
  have hpos := (FacetInterval.positive_iff f).mpr ⟨_,hx,_,hy,hxy⟩
  have haend := FacetInterval.vertex_is_endpoint h hr hij f hva hy
  exact same_witness_positive_side_unique R h.injective hij f hpos haend hw hai haj hbi hbj

end N11Formalization.ActualRefinementSideMultiplicity
#check @N11Formalization.ActualRefinementSideMultiplicity.same_witness_positive_side_unique
#print axioms N11Formalization.ActualRefinementSideMultiplicity.selected_side_unique
#print axioms N11Formalization.ActualRefinementSideMultiplicity.same_witness_positive_side_unique
