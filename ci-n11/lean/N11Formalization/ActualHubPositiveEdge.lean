import N11Formalization.ActualHubAdjacency
import N11Formalization.ActualHubEdgeGeometry

/-! Positive-length ACTUAL hub adjacency without genericity.
If a common hub point has no active ring, finite strict inequalities give
a genuine segment. Otherwise the active ring replaces a degenerate hub
facet in the radial proof. The core cannot contain such a ring tie.
Thus no punctured-disk connectivity or unproved polygon/refinement input
is needed. The actual source C450 inequalities remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubPositiveEdge
open DSHTopologyInterior ActualHubEssentiality ActualVoronoiCells
open ActualHubCoreSupport ActualVoronoiRadialExit ActualTwoCircleCapacity
open ActualHubAdjacency ActualHubEdgeGeometry

theorem ring_far_from_core {c : Fin 11 → Point} {r : ℝ} (hR : RingLabels c r)
    {x : Point} (hx : ‖x‖ < 1-2*r) {i : Fin 11} (hi : i.val < 9) :
    r < dist x (c i) := by
  have hn := one_sub_le_norm_of_meetsCircle (hR.ring_meets hi)
  have ht := norm_le_norm_add_norm_sub x (c i)
  rw [← dist_eq_norm x (c i)] at ht
  linarith

theorem no_edge_core_disjoint {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hR : RingLabels c r) (hne : c 9 ≠ c 10)
    (hno : ¬ HubEdge c) :
    Metric.ball (0 : Point) (1-2*r) ∩ (Cell c 9 ∩ Cell c 10) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxn : ‖x‖ < 1-2*r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx.1
  obtain ⟨i,hi,heq⟩ := ring_tie_of_no_edge hne hno hx.2
  have hd := nearest_le_radius hc
    (mem_unitDisk.mpr (by linarith [Covers.nonneg hc])) hx.2.1
  have hfar := ring_far_from_core hR hxn hi
  rw [heq] at hfar
  linarith

theorem ring_exit_of_no_edge {c : Fin 11 → Point} {j : Fin 11} {u : Point} {r : ℝ}
    (hj : 9 ≤ j.val) (hne : c 9 ≠ c 10) (hno : ¬ HubEdge c)
    (hsite : ∀ k : Fin 11, k ≠ j → c k ≠ c j) (e : Exit c j u r) :
    ∃ e' : Exit c j u r, e'.site.val < 9 := by
  by_cases hir : e.site.val < 9
  · exact ⟨e,hir⟩
  · have hjc : j = (9 : Fin 11) ∨ j = 10 := by
      have hv := j.isLt
      have : j.val = 9 ∨ j.val = 10 := by omega
      exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    have hic : e.site = (9 : Fin 11) ∨ e.site = 10 := by
      have hv := e.site.isLt
      have : e.site.val = 9 ∨ e.site.val = 10 := by omega
      exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    let x := ray (c j) u e.time
    have hSelf : x ∈ Cell c j := e.nearest
    have hiCell : x ∈ Cell c e.site := by
      intro k
      rw [exit_equidistant e]
      exact e.nearest k
    have hcommon : x ∈ Cell c 9 ∩ Cell c 10 := by
      rcases hjc with hj9 | hj10 <;> rcases hic with hi9 | hi10
      · exact (e.different (hi9.trans hj9.symm)).elim
      · exact ⟨by simpa only [hj9] using hSelf, by simpa only [hi10] using hiCell⟩
      · exact ⟨by simpa only [hi9] using hiCell, by simpa only [hj10] using hSelf⟩
      · exact (e.different (hi10.trans hj10.symm)).elim
    obtain ⟨k,hk,hktie⟩ := ring_tie_of_no_edge hne hno hcommon
    have hkj : k ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      omega
    have hxd : dist x (c j) = dist x (c 9) := by
      rcases hjc with hj9 | hj10
      · rw [hj9]
      · rw [hj10]
        exact le_antisymm (hcommon.2 9) (hcommon.1 10)
    have hktie' : dist (ray (c j) u e.time) (c k) =
        dist (ray (c j) u e.time) (c j) := hktie.trans hxd.symm
    have hd := ray_difference (c j) (c k) u e.time
    rw [hktie',sub_self] at hd
    have hactive : 2*e.time*inner ℝ u (c k-c j) = ‖c k-c j‖^2 := by linarith
    have hn : 0 < ‖c k-c j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hsite k hkj))
    have hf : 0 < inner ℝ u (c k-c j) := by
      by_contra hnot
      have hm := mul_nonpos_of_nonneg_of_nonpos
        (by linarith [e.positive] : 0 ≤ 2*e.time) (le_of_not_gt hnot)
      rw [hactive] at hm
      exact not_le_of_gt (sq_pos_of_pos hn) hm
    exact ⟨⟨e.time,k,e.positive,e.radius,hkj,hf,e.nearest,hactive⟩,hk⟩

theorem hub_edge_of_source (hs : C450NormalizedInterface.SourceObligation)
    {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hr : r < 19/50) (hR : RingLabels c r) : HubEdge c := by
  classical
  by_contra hno
  have h450 := C450NormalizedInterface.atom_of_source hs
  have hstruct := structure_of_atom h450 hr.le hc hR
  have hdis := no_edge_core_disjoint hc hR hstruct.2 hno
  obtain ⟨j,hj,hcore,hoff,he7⟩ := disjoint_core_small_hub h450 hc hr.le hR hdis
  have hCells := hubCells_of_atom h450 hr.le hc hR
  let d : Fin 10 → Point := fun k => c (ringCopyIndex k)
  have hnorm (k : Fin 10) : 1-19/50 ≤ ‖d k‖ ∧ ‖d k‖ ≤ 1+19/50 := by
    have hm := (hR.ring_meets (ringCopyIndex_lt k)).mono hr.le
    exact ⟨one_sub_le_norm_of_meetsCircle hm, norm_le_one_add_of_meetsCircle hm⟩
  apply two_circles_impossible hs d (c j) he7 hnorm
  · intro x hx
    obtain ⟨i,hi⟩ := hc x (mem_unitDisk.mpr hx.le)
    have hir : i.val < 9 := (hR i).mp ⟨x,hx,hi⟩
    obtain ⟨k,hk⟩ := ringCopyIndex_surjective hir
    exact ⟨k,by simpa only [d,hk] using hi.trans hr.le⟩
  · intro x hx
    have hn : ‖x-c j‖ = (19/50:ℝ) := by rwa [dist_eq_norm] at hx
    have hne : x-c j ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hn]
      norm_num
    let u : Point := centerDir (x-c j)
    have hu : ‖u‖ = 1 := centerDir_norm hne
    have hxu : x-c j = (19/50:ℝ) • u := by
      calc
        x-c j = ‖x-c j‖ • centerDir (x-c j) := self_eq_norm_smul_centerDir hne
        _ = (19/50:ℝ) • u := by rw [hn]
    have hsite (k : Fin 11) (hk : k ≠ j) : c k ≠ c j :=
      (private_point_ne (private_point_of_atom h450 hr.le hc hR hj) hk.symm).symm
    obtain ⟨e⟩ := exists_radial_exit hu (Covers.nonneg hc) hsite (hCells.radius j hj)
    obtain ⟨e',hir⟩ := ring_exit_of_no_edge hj hstruct.2 hno hsite e
    obtain ⟨k,hk⟩ := ringCopyIndex_surjective hir
    have hdist := enlarged_ray_covered e' hu hr.le
    have hxeq : ray (c j) u (19/50:ℝ) = x := by rw [ray,← hxu]; abel
    rw [hxeq] at hdist
    exact ⟨k,by simpa only [d,hk] using hdist⟩

end N11Formalization.ActualHubPositiveEdge
#check @N11Formalization.ActualHubPositiveEdge.hub_edge_of_source
#print axioms N11Formalization.ActualHubPositiveEdge.no_edge_core_disjoint
#print axioms N11Formalization.ActualHubPositiveEdge.ring_exit_of_no_edge
#print axioms N11Formalization.ActualHubPositiveEdge.hub_edge_of_source
