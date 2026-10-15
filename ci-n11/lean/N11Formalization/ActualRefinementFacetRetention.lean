import N11Formalization.ActualFiniteNearestRefinement
import N11Formalization.ActualPositiveFacetGraph
import N11Formalization.ActualHubFacetComplete

/-! Every positive ACTUAL facet is retained by the produced finite
refinement at each interior endpoint. In particular the true hub edge is
retained without prescribing its two unknown ring labels or canonical cut.
No additional realization or positive-facet-retention premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementFacetRetention
open ActualVoronoiCells ActualVoronoiIncidence ActualClippedFacetIntervals
open ActualClippedFacetInterior ActualClippedMeshVertices ActualCoverStructuralReduction
open ActualFiniteNearestRefinement ActualIncidentFanRefinement ActualIncidentPolygonOrder
open ActualIncidentFacetAdjacency ActualPositiveFacetGraph ActualHubFacetComplete
open ActualVoronoiRadialExit

theorem Refinement.facet_at_endpoint_retained {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j) (f : FacetInterval c i j) (hpos : f.lo < f.hi)
    {x : Point} (hx : x ∈ ClippedVertices c)
    (hxend : x = ray f.base f.direction f.lo ∨ x = ray f.base f.direction f.hi) :
    ∃ a : R.Index, R.witness a = x ∧
      i ∈ Set.range (R.labels a) ∧ j ∈ Set.range (R.labels a) := by
  let V : R.vertices := ⟨x,(R.exact_vertices x).mpr hx⟩
  let F := R.face V
  let o := R.order V
  have hFx : F.point = x := R.base V
  have hxpair : x ∈ ClippedCommon c i j := by
    rcases hxend with he | he
    · rw [he]; exact f.left_mem
    · rw [he]; exact f.right_mem
  have hi : i ∈ incident c F.point := by rw [hFx]; exact mem_incident.mpr hxpair.2.1
  have hj : j ∈ incident c F.point := by rw [hFx]; exact mem_incident.mpr hxpair.2.2
  let I : Fin (incident c F.point).card := o.order.symm ⟨i,hi⟩
  let J : Fin (incident c F.point).card := o.order.symm ⟨j,hj⟩
  have hI : (o.order I).val = i := congrArg Subtype.val (o.order.apply_symm_apply ⟨i,hi⟩)
  have hJ : (o.order J).val = j := congrArg Subtype.val (o.order.apply_symm_apply ⟨j,hj⟩)
  have hFFend : F.point = ray f.base f.direction f.lo ∨
      F.point = ray f.base f.direction f.hi := by rwa [hFx]
  have hadj := FacetInterval.endpoint_polygon_adjacent hc hij f hpos F o hFFend hI hJ
  rcases hadj with hjnext | hinext
  · obtain ⟨k,hk,hiK,hjK⟩ := ActualIncidentFanRefinement.OrderedCircle.side_retained o I
    refine ⟨⟨V,⟨k,hk⟩⟩,hFx,?_,?_⟩
    · change i ∈ Set.range (triangleLabels o k)
      rwa [hI] at hiK
    · change j ∈ Set.range (triangleLabels o k)
      have he : finRotate (incident c F.point).card I = J := hjnext.symm
      rwa [he,hJ] at hjK
  · obtain ⟨k,hk,hjK,hiK⟩ := ActualIncidentFanRefinement.OrderedCircle.side_retained o J
    refine ⟨⟨V,⟨k,hk⟩⟩,hFx,?_,?_⟩
    · change i ∈ Set.range (triangleLabels o k)
      have he : finRotate (incident c F.point).card J = I := hinext.symm
      rwa [he,hI] at hiK
    · change j ∈ Set.range (triangleLabels o k)
      rwa [hJ] at hjK

theorem Refinement.positive_pair_retained {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (h : Representative c r) (hr : r < 19/50)
    {i j : Fin 11} (hpos : PositivePair c i j) :
    ∃ a : R.Index, i ∈ Set.range (R.labels a) ∧ j ∈ Set.range (R.labels a) := by
  obtain ⟨hij,x,hx,y,hy,hxy⟩ := hpos
  obtain ⟨f⟩ := clippedCommon_interval h.injective hij ⟨x,hx⟩
  have hfpos := (FacetInterval.positive_iff f).mpr ⟨x,hx,y,hy,hxy⟩
  rcases FacetInterval.positive_has_interior_vertex h hr hij f hfpos with hleft | hright
  · obtain ⟨a,_,hi,hj⟩ := Refinement.facet_at_endpoint_retained R h.injective hij f hfpos
      hleft (Or.inl rfl)
    exact ⟨a,hi,hj⟩
  · obtain ⟨a,_,hi,hj⟩ := Refinement.facet_at_endpoint_retained R h.injective hij f hfpos
      hright (Or.inr rfl)
    exact ⟨a,hi,hj⟩

/-- The hub edge has triangles at BOTH true endpoints, produced separately
and necessarily distinct because their primal witnesses differ. -/
theorem Refinement.hub_edge_two_retained {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (h : Representative c r) (hr : r < 19/50) :
    ∃ a b : R.Index, a ≠ b ∧ R.witness a ≠ R.witness b ∧
      9 ∈ Set.range (R.labels a) ∧ 10 ∈ Set.range (R.labels a) ∧
      9 ∈ Set.range (R.labels b) ∧ 10 ∈ Set.range (R.labels b) := by
  obtain ⟨F⟩ := ActualHubFacetComplete.Representative.hubFacet h hr
  obtain ⟨a,ha,ha9,ha10⟩ := Refinement.facet_at_endpoint_retained R h.injective (by decide)
    F.interval F.positive F.left_vertex (Or.inl rfl)
  obtain ⟨b,hb,hb9,hb10⟩ := Refinement.facet_at_endpoint_retained R h.injective (by decide)
    F.interval F.positive F.right_vertex (Or.inr rfl)
  have hne : R.witness a ≠ R.witness b := by
    rw [ha,hb]
    exact FacetInterval.endpoints_ne F.interval F.positive
  exact ⟨a,b,fun he => hne (congrArg R.witness he),hne,ha9,ha10,hb9,hb10⟩

end N11Formalization.ActualRefinementFacetRetention
#check @N11Formalization.ActualRefinementFacetRetention.Refinement.positive_pair_retained
#check @N11Formalization.ActualRefinementFacetRetention.Refinement.hub_edge_two_retained
#print axioms N11Formalization.ActualRefinementFacetRetention.Refinement.positive_pair_retained
#print axioms N11Formalization.ActualRefinementFacetRetention.Refinement.hub_edge_two_retained
