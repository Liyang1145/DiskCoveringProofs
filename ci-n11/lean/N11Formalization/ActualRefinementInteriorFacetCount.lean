import N11Formalization.ActualRefinementBoundaryCount
import N11Formalization.ActualRefinementHubCount

/-! Every true positive clipped facet which is NOT a boundary-ring cycle
pair occurs in exactly TWO actual selected triangles. All endpoint,
retention and local multiplicity inputs are produced. No interior-edge
two-face, genericity, Euler, cellular disk or canonical-label assumption. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementInteriorFacetCount
open ActualVoronoiCells ActualVoronoiIncidence ActualCoverStructuralReduction
open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualRefinementSideMultiplicity ActualRefinementFacetRetention ActualClippedFacetIntervals
open ActualClippedMeshVertices ActualBoundaryFacetUniqueness ActualPositiveFacetGraph
open ActualRingDirectionOrder ActualBoundaryCyclicOrder ActualBoundaryNineTies
open ActualBoundaryNearestPairs ActualVoronoiRadialExit

def BoundaryLabels (i j : Fin 11) : Prop :=
  ∃ a : Fin 9, (i = ringSite a ∧ j = ringSite (nextRing a)) ∨
    (j = ringSite a ∧ i = ringSite (nextRing a))

theorem circle_pair_boundary_labels {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {i j : Fin 11} (hij : i ≠ j)
    {x : Point} (hx : ‖x‖ = 1) (hpair : x ∈ Cell c i ∩ Cell c j) : BoundaryLabels i j := by
  let I : Fin 9 := ⟨i.val,nearest_ring h.cover h.labels hx hpair.1⟩
  let J : Fin 9 := ⟨j.val,nearest_ring h.cover h.labels hx hpair.2⟩
  have hI : ringSite I = i := Fin.ext rfl
  have hJ : ringSite J = j := Fin.ext rfl
  have hIJ : I ≠ J := by
    intro he
    apply hij
    rw [← hI,← hJ,he]
  have hcases := nearest_ring_pair_adjacent h.cover hr h.labels h.midpoint_order hIJ hx
    (by rw [hI]; exact hpair.1) (by rw [hJ]; exact hpair.2)
  rcases hcases with hn | hn
  · exact ⟨I,Or.inl ⟨hI.symm,by rw [← hn]; exact hJ.symm⟩⟩
  · exact ⟨J,Or.inr ⟨hJ.symm,by rw [← hn]; exact hI.symm⟩⟩

def pairTriangles {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (i j : Fin 11) : Finset R.Index := by
  classical
  exact Finset.univ.filter (fun a => i ∈ labelSet R a ∧ j ∈ labelSet R a)

theorem mem_pairTriangles {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    {i j : Fin 11} {a : R.Index} :
    a ∈ pairTriangles R i j ↔ i ∈ labelSet R a ∧ j ∈ labelSet R a := by
  classical
  simp [pairTriangles]

theorem actual_positive_interior_pair_count {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) {i j : Fin 11}
    (hp : PositivePair c i j) (hnobound : ¬ BoundaryLabels i j) :
    (pairTriangles R i j).card = 2 := by
  classical
  obtain ⟨hij,x,hx,y,hy,hxy⟩ := hp
  obtain ⟨f⟩ := clippedCommon_interval h.injective hij ⟨x,hx⟩
  have hpos := (FacetInterval.positive_iff f).mpr ⟨x,hx,y,hy,hxy⟩
  have hleft : ray f.base f.direction f.lo ∈ ClippedVertices c := by
    rcases f.left_endpoint with hcircle | hv
    · exact (hnobound (circle_pair_boundary_labels h hr hij hcircle f.left_mem.2)).elim
    · exact hv
  have hright : ray f.base f.direction f.hi ∈ ClippedVertices c := by
    rcases f.right_endpoint with hcircle | hv
    · exact (hnobound (circle_pair_boundary_labels h hr hij hcircle f.right_mem.2)).elim
    · exact hv
  obtain ⟨a,ha,hai,haj⟩ := Refinement.facet_at_endpoint_retained R h.injective hij f hpos
    hleft (Or.inl rfl)
  obtain ⟨b,hb,hbi,hbj⟩ := Refinement.facet_at_endpoint_retained R h.injective hij f hpos
    hright (Or.inr rfl)
  have hA : a ∈ pairTriangles R i j := mem_pairTriangles.mpr ⟨mem_labelSet.mpr hai,mem_labelSet.mpr haj⟩
  have hB : b ∈ pairTriangles R i j := mem_pairTriangles.mpr ⟨mem_labelSet.mpr hbi,mem_labelSet.mpr hbj⟩
  have hab : a ≠ b := by
    intro he
    have hw : R.witness a = R.witness b := congrArg R.witness he
    rw [ha,hb] at hw
    exact ActualClippedFacetInterior.FacetInterval.endpoints_ne f hpos hw
  have hset : pairTriangles R i j = {a,b} := by
    ext k
    constructor
    · intro hk
      have hK := mem_pairTriangles.mp hk
      have hv := Refinement.witness_exact_vertex R k
      have hpK : R.witness k ∈ ClippedCommon c i j :=
        ⟨hv.1,nearest_of_label_mem R hK.1,nearest_of_label_mem R hK.2⟩
      have hkends := ActualBoundaryFacetUniqueness.FacetInterval.vertex_is_endpoint h hr hij f hv hpK
      rcases hkends with hkl | hkr
      · have he : k = a := same_witness_positive_side_unique R h.injective hij f hpos
          (Or.inl hkl) (hkl.trans ha.symm) hK.1 hK.2
          (mem_pairTriangles.mp hA).1 (mem_pairTriangles.mp hA).2
        exact Finset.mem_insert.mpr (Or.inl he)
      · have he : k = b := same_witness_positive_side_unique R h.injective hij f hpos
          (Or.inr hkr) (hkr.trans hb.symm) hK.1 hK.2
          (mem_pairTriangles.mp hB).1 (mem_pairTriangles.mp hB).2
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
    · intro hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hA
      · have he := Finset.mem_singleton.mp hk
        subst k
        exact hB
  rw [hset]
  simp [hab]

end N11Formalization.ActualRefinementInteriorFacetCount
#check @N11Formalization.ActualRefinementInteriorFacetCount.actual_positive_interior_pair_count
#print axioms N11Formalization.ActualRefinementInteriorFacetCount.circle_pair_boundary_labels
#print axioms N11Formalization.ActualRefinementInteriorFacetCount.actual_positive_interior_pair_count
