import N11Formalization.ActualHubCoreSupport
import N11Formalization.ActualVoronoiRadialExit
import N11Formalization.ActualTwoCircleCapacity

/-! Genuine hub-cell adjacency for an arbitrary ACTUAL nine-ring cover.
The source per-disk continuous inequalities remain explicit; no hub-edge
existence, facet, optimizer, first-exit or two-fan premise is assumed.
This file first proves nonempty adjacency. Positive-length adjacency is a
separate obligation, not inferred from a common point. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubAdjacency
open DSHTopologyInterior ActualHubEssentiality ActualVoronoiCells
open ActualHubCoreSupport ActualVoronoiRadialExit ActualTwoCircleCapacity

def ringCopyIndex (i : Fin 10) : Fin 11 :=
  if h : i.val < 9 then ⟨i.val, by omega⟩ else 0

theorem ringCopyIndex_lt (i : Fin 10) : (ringCopyIndex i).val < 9 := by
  unfold ringCopyIndex
  split_ifs <;> simp_all

theorem ringCopyIndex_surjective {i : Fin 11} (hi : i.val < 9) :
    ∃ k : Fin 10, ringCopyIndex k = i := by
  refine ⟨⟨i.val, by omega⟩, ?_⟩
  simp only [ringCopyIndex, dif_pos hi]

theorem exit_site_ring {c : Fin 11 → Point} {j : Fin 11} {u : Point} {r : ℝ}
    (hj : 9 ≤ j.val) (e : Exit c j u r)
    (hnone : ¬ (Cell c 9 ∩ Cell c 10).Nonempty) : e.site.val < 9 := by
  by_contra hnot
  have heh : 9 ≤ e.site.val := by omega
  have hjc : j = (9 : Fin 11) ∨ j = 10 := by
    have hv := j.isLt
    have : j.val = 9 ∨ j.val = 10 := by omega
    exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  have hic : e.site = (9 : Fin 11) ∨ e.site = 10 := by
    have hv := e.site.isLt
    have : e.site.val = 9 ∨ e.site.val = 10 := by omega
    exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  have hiCell : ray (c j) u e.time ∈ Cell c e.site := by
    intro k
    rw [exit_equidistant e]
    exact e.nearest k
  rcases hjc with hj9 | hj10 <;> rcases hic with hi9 | hi10
  · exact e.different (hi9.trans hj9.symm)
  · apply hnone
    exact ⟨ray (c j) u e.time, by simpa only [hj9] using e.nearest,
      by simpa only [hi10] using hiCell⟩
  · apply hnone
    exact ⟨ray (c j) u e.time, by simpa only [hi9] using hiCell,
      by simpa only [hj10] using e.nearest⟩
  · exact e.different (hi10.trans hj10.symm)

theorem hub_cells_intersect (hs : C450NormalizedInterface.SourceObligation)
    {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hr : r < 19/50) (hR : RingLabels c r) :
    (Cell c 9 ∩ Cell c 10).Nonempty := by
  classical
  by_contra hnone
  have h450 := C450NormalizedInterface.atom_of_source hs
  have hdis : Metric.ball (0 : Point) (1-2*r) ∩ (Cell c 9 ∩ Cell c 10) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hnone ⟨x, hx.2⟩
  obtain ⟨j, hj, hcore, hoff, he7⟩ := disjoint_core_small_hub h450 hc hr.le hR hdis
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
    refine ⟨k, ?_⟩
    change dist x (c (ringCopyIndex k)) ≤ 19/50
    rw [hk]
    exact hi.trans hr.le
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
    obtain ⟨e⟩ := exists_radial_exit hu (Covers.nonneg hc)
      (fun k hk => (private_point_ne (private_point_of_atom h450 hr.le hc hR hj) hk.symm).symm)
      (hCells.radius j hj)
    have hir := exit_site_ring hj e hnone
    obtain ⟨k,hk⟩ := ringCopyIndex_surjective hir
    have hdist := enlarged_ray_covered e hu hr.le
    have hxeq : ray (c j) u (19/50:ℝ) = x := by
      rw [ray, ← hxu]
      abel
    rw [hxeq] at hdist
    exact ⟨k, by simpa only [d,hk] using hdist⟩

theorem hub_common_nearest_point (hs : C450NormalizedInterface.SourceObligation)
    {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hr : r < 19/50) (hR : RingLabels c r) :
    ∃ x : Point, ‖x‖ < 1 ∧ dist x (c 9) = dist x (c 10) ∧
      dist x (c 9) ≤ r ∧ ∀ i : Fin 11, dist x (c 9) ≤ dist x (c i) := by
  obtain ⟨x,h9,h10⟩ := hub_cells_intersect hs hc hr hR
  have hCells := hubCells_of_atom (C450NormalizedInterface.atom_of_source hs) hr.le hc hR
  have hx := hCells.inside 9 (by decide) x h9
  exact ⟨x,hx,le_antisymm (h9 10) (h10 9),
    nearest_le_radius hc (mem_unitDisk.mpr hx.le) h9,h9⟩

end N11Formalization.ActualHubAdjacency
#check @N11Formalization.ActualHubAdjacency.hub_cells_intersect
#check @N11Formalization.ActualHubAdjacency.hub_common_nearest_point
#print axioms N11Formalization.ActualHubAdjacency.hub_cells_intersect
#print axioms N11Formalization.ActualHubAdjacency.hub_common_nearest_point
