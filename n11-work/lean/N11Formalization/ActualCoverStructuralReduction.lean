import N11Formalization.ActualRingDirectionOrder
import N11Formalization.ActualHubPositiveEdge

/-! Productive arbitrary-cover structural reduction.
The representative is constructed from the original cover, not assumed.
Original r and actual circle caps are retained through a finite permutation.
Owned-arc connectedness, Delaunay refinement, metric classification and
canonical51 witnesses are NOT fields asserted by this reduction. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualCoverStructuralReduction
open DSHTopologyInterior ActualHubEssentiality ActualVoronoiCells
open ActualRingEssentiality ActualInwardNormalization ActualRingDirectionOrder
open ActualHubEdgeGeometry ActualHubPositiveEdge

structure Representative (c : Fin 11 → Point) (r : ℝ) : Prop where
  cover : Covers c r
  labels : RingLabels c r
  midpoint_order : StrictMono (midpointAngle c)
  inward : ∀ i : Fin 11, i.val < 9 → ‖c i‖ ≤ Real.sqrt (1-r^2)
  private_points : ∀ i : Fin 11, PrivatePoint c r i
  private_circle : ∀ i : Fin 9, PrivateCirclePoint c r (ringSite i)
  injective : Function.Injective c
  hubs : HubStructure c r
  cells : HubCellStructure c r
  hub_edge : HubEdge c
  center_inside : ∀ i : Fin 11, ‖c i‖ < 1

/-- SAME-root threshold and arbitrary original Fin11 cover.
The only certificate input is the genuine C450 source obligation. -/
theorem representative_of_source (hs : C450NormalizedInterface.SourceObligation)
    {c : Fin 11 → Point} {r : ℝ} (hr : r < SourceExactRoot.sourceRadius)
    (hc : Covers c r) :
    ∃ (p : Equiv.Perm (Fin 11)) (d : Fin 11 → Point),
      Representative d r ∧
      (∀ i : Fin 11, ∀ x : Point, ‖x‖ = 1 →
        (dist x (d i) ≤ r ↔ dist x (c (p i)) ≤ r)) ∧
      (∀ i : Fin 11, 9 ≤ i.val → d i = c (p i)) := by
  obtain ⟨rho,hcov,hlabels,_,_,hbound,hkeep⟩ := normalized_structure_of_source hs hr hc
  let pc : Fin 11 → Point := fun i => c (rho i)
  let b : Fin 11 → Point := normalize pc r
  change Covers b r at hcov
  change RingLabels b r at hlabels
  change (∀ i : Fin 11, i.val < 9 → ‖b i‖ ≤ Real.sqrt (1-r^2)) at hbound
  change (∀ i : Fin 11, 9 ≤ i.val → b i = pc i) at hkeep
  have hrR0 : r < 19/50 := hr.trans
    (SourceExactRoot.sourceRadius_mem_box.2.trans_lt boxHiCert_six_lt_R0_real)
  have hr1 : r < 1 := by linarith
  have hrpos := covers_pos hc hr1
  obtain ⟨q,hcq,hRq,ho⟩ := exists_ordered_cover hcov hrR0 hlabels
  let sigma := extendRingPerm q
  let d : Fin 11 → Point := fun i => b (sigma i)
  let p : Equiv.Perm (Fin 11) := sigma.trans rho
  change Covers d r at hcq
  change RingLabels d r at hRq
  change StrictMono (midpointAngle d) at ho
  have h450 := C450NormalizedInterface.atom_of_source hs
  have hdBound (i : Fin 11) (hi : i.val < 9) : ‖d i‖ ≤ Real.sqrt (1-r^2) :=
    hbound (sigma i) ((extendRingPerm_ring_iff q i).mpr hi)
  have hpriv := all_private_and_injective h450 hcq hrR0 hRq
  have hHubs := structure_of_atom h450 hrR0.le hcq hRq
  have hCells := hubCells_of_atom h450 hrR0.le hcq hRq
  have hEdge := hub_edge_of_source hs hcq hrR0 hRq
  have hsqrt : Real.sqrt (1-r^2) < 1 := by
    have hsquare : Real.sqrt (1-r^2)^2 = 1-r^2 := Real.sq_sqrt (by nlinarith)
    nlinarith [Real.sqrt_nonneg (1-r^2),sq_pos_of_pos hrpos]
  have hinside (i : Fin 11) : ‖d i‖ < 1 := by
    by_cases hi : i.val < 9
    · exact (hdBound i hi).trans_lt hsqrt
    · have hm := (hHubs.1 i (show 9 ≤ i.val by omega)).2.1
      linarith [Covers.nonneg hc]
  refine ⟨p,d,⟨hcq,hRq,ho,hdBound,hpriv.1,?_,hpriv.2,hHubs,hCells,hEdge,hinside⟩,?_,?_⟩
  · intro i
    exact private_circle_point hcq hrR0 hRq i
  · intro i x hx
    change dist x (normalize pc r (sigma i)) ≤ r ↔ dist x (pc (sigma i)) ≤ r
    exact normalized_circle_caps (covers_relabel rho hc) hr1 (sigma i) hx
  · intro i hi
    have hsigma : 9 ≤ (sigma i).val := by
      by_contra h
      have hlt : (sigma i).val < 9 := by omega
      have hit := (extendRingPerm_ring_iff q i).mp hlt
      omega
    exact hkeep (sigma i) hsigma

/-- A positive Euclidean segment of genuinely common nearest points,
inside D and within the ORIGINAL radius of both hubs. -/
theorem Representative.hub_segment {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) :
    ∃ x y : Point, 0 < dist x y ∧
      ∀ z ∈ segment ℝ x y, ‖z‖ < 1 ∧ dist z (c 9) = dist z (c 10) ∧
        dist z (c 9) ≤ r ∧ ∀ i : Fin 11, dist z (c 9) ≤ dist z (c i) := by
  obtain ⟨x,y,hx,hy,hne⟩ := h.hub_edge
  have hseg := ((cell_convex c 9).inter (cell_convex c 10)).segment_subset hx hy
  refine ⟨x,y,dist_pos.mpr hne,?_⟩
  intro z hz
  have hmem := hseg hz
  have hzin := h.cells.inside 9 (by decide) z hmem.1
  exact ⟨hzin,le_antisymm (hmem.1 10) (hmem.2 9),
    nearest_le_radius h.cover (mem_unitDisk.mpr hzin.le) hmem.1,hmem.1⟩

end N11Formalization.ActualCoverStructuralReduction
#check @N11Formalization.ActualCoverStructuralReduction.representative_of_source
#check @N11Formalization.ActualCoverStructuralReduction.Representative.hub_segment
#print axioms N11Formalization.ActualCoverStructuralReduction.representative_of_source
#print axioms N11Formalization.ActualCoverStructuralReduction.Representative.hub_segment
