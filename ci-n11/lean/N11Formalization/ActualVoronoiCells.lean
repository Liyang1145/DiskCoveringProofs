import N11Formalization.ActualHubEssentiality
import N11Formalization.FlashCoverReductionWitness

/-! Full, untruncated nearest-site cells of the ACTUAL cover.
No Delaunay realization, cyclic order, face witness or genericity is assumed.
The C450 input remains explicit; this is not the unconditional main theorem. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualVoronoiCells
open DSHTopologyInterior ActualHubEssentiality

def Cell (c : Fin 11 → Point) (j : Fin 11) : Set Point :=
  {x | ∀ i : Fin 11, dist x (c j) ≤ dist x (c i)}

def StrictCell (c : Fin 11 → Point) (j : Fin 11) : Set Point :=
  {x | ∀ i : Fin 11, i ≠ j → dist x (c j) < dist x (c i)}

theorem center_mem (c : Fin 11 → Point) (j : Fin 11) : c j ∈ Cell c j := by
  intro i
  simpa only [dist_self] using dist_nonneg (x := c j) (y := c i)

theorem exists_nearest (c : Fin 11 → Point) (x : Point) :
    ∃ j : Fin 11, x ∈ Cell c j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin 11 => dist x (c i)) Finset.univ_nonempty
  exact ⟨j, fun i => hj i (Finset.mem_univ i)⟩

theorem cell_closed (c : Fin 11 → Point) (j : Fin 11) : IsClosed (Cell c j) := by
  have he : Cell c j = ⋂ i : Fin 11, {x : Point | dist x (c j) ≤ dist x (c i)} := by
    ext x
    simp only [Cell, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop)

theorem dist_le_iff_halfspace (x a b : Point) :
    dist x a ≤ dist x b ↔
      2 * inner ℝ x (b - a) ≤ ‖b‖ ^ 2 - ‖a‖ ^ 2 := by
  have ha : 0 ≤ dist x a := dist_nonneg
  have hb : 0 ≤ dist x b := dist_nonneg
  have he : dist x a ^ 2 - dist x b ^ 2 =
      ‖a‖ ^ 2 - ‖b‖ ^ 2 + 2 * inner ℝ x (b - a) := by
    simp only [dist_eq_norm, norm_sub_sq_real, inner_sub_right]
    ring
  constructor
  · intro h
    have hs : dist x a ^ 2 ≤ dist x b ^ 2 := by nlinarith
    linarith
  · intro h
    have hs : dist x a ^ 2 ≤ dist x b ^ 2 := by linarith
    nlinarith

theorem cell_convex (c : Fin 11 → Point) (j : Fin 11) : Convex ℝ (Cell c j) := by
  intro x hx y hy a b ha hb hab i
  rw [dist_le_iff_halfspace]
  have hxi := (dist_le_iff_halfspace x (c j) (c i)).mp (hx i)
  have hyi := (dist_le_iff_halfspace y (c j) (c i)).mp (hy i)
  simp only [inner_add_left, real_inner_smul_left]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hxi),
    mul_nonneg hb (sub_nonneg.mpr hyi)]

theorem strictCell_open (c : Fin 11 → Point) (j : Fin 11) :
    IsOpen (StrictCell c j) := by
  classical
  have he : StrictCell c j =
      ⋂ i : {i : Fin 11 // i ≠ j}, {x : Point | dist x (c j) < dist x (c i.1)} := by
    ext x
    simp only [StrictCell, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hx i
      exact hx i.1 i.2
    · intro hx i hi
      exact hx ⟨i, hi⟩
  rw [he]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) (by fun_prop)

theorem strictCell_subset (c : Fin 11 → Point) (j : Fin 11) :
    StrictCell c j ⊆ Cell c j := by
  intro x hx i
  by_cases hi : i = j
  · subst i
    exact le_rfl
  · exact (hx i hi).le

theorem center_mem_interior_of_ne {c : Fin 11 → Point} {j : Fin 11}
    (hne : ∀ i : Fin 11, i ≠ j → c i ≠ c j) :
    c j ∈ interior (Cell c j) := by
  apply interior_mono (strictCell_subset c j)
  rw [(strictCell_open c j).interior_eq]
  intro i hi
  rw [dist_self]
  exact dist_pos.mpr (hne i hi).symm

theorem privatePoint_strictCell {c : Fin 11 → Point} {r : ℝ} {j : Fin 11}
    (hp : PrivatePoint c r j) :
    ∃ x : Point, x ∈ unitDisk ∧ x ∈ StrictCell c j := by
  obtain ⟨x, hx, hj, hother⟩ := hp
  exact ⟨x, hx, fun i hi => hj.trans_lt (hother i hi)⟩

theorem nearest_le_radius {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    {x : Point} (hx : x ∈ unitDisk) {j : Fin 11} (hj : x ∈ Cell c j) :
    dist x (c j) ≤ r :=
  nearest_site_le_radius hc hx hj

theorem hub_cell_no_circle {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hR : RingLabels c r) {j : Fin 11} (hj : 9 ≤ j.val) :
    ∀ x ∈ Cell c j, ‖x‖ ≠ 1 := by
  intro x hx hn
  exact (hR.hub_not_meets hj)
    ⟨x, hn, nearest_le_radius hc (mem_unitDisk.mpr hn.le) hx⟩

theorem hub_cell_inside {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hR : RingLabels c r) {j : Fin 11} (hj : 9 ≤ j.val)
    (hcenter : ‖c j‖ < 1) : ∀ x ∈ Cell c j, ‖x‖ < 1 :=
  convex_closed_norm_lt_one (cell_convex c j) (center_mem c j) hcenter
    (hub_cell_no_circle hc hR hj)

theorem hub_cell_radius {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hR : RingLabels c r) {j : Fin 11} (hj : 9 ≤ j.val)
    (hcenter : ‖c j‖ < 1) : Cell c j ⊆ Metric.closedBall (c j) r := by
  intro x hx
  exact Metric.mem_closedBall.mpr
    (nearest_le_radius hc (mem_unitDisk.mpr (hub_cell_inside hc hR hj hcenter x hx).le) hx)

theorem hub_cell_compact {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hR : RingLabels c r) {j : Fin 11} (hj : 9 ≤ j.val)
    (hcenter : ‖c j‖ < 1) : IsCompact (Cell c j) :=
  (isCompact_closedBall (c j) r).of_isClosed_subset (cell_closed c j)
    (hub_cell_radius hc hR hj hcenter)

structure HubCellStructure (c : Fin 11 → Point) (r : ℝ) : Prop where
  compact : ∀ j : Fin 11, 9 ≤ j.val → IsCompact (Cell c j)
  convex : ∀ j : Fin 11, 9 ≤ j.val → Convex ℝ (Cell c j)
  center_interior : ∀ j : Fin 11, 9 ≤ j.val → c j ∈ interior (Cell c j)
  inside : ∀ j : Fin 11, 9 ≤ j.val → ∀ x ∈ Cell c j, ‖x‖ < 1
  radius : ∀ j : Fin 11, 9 ≤ j.val → Cell c j ⊆ Metric.closedBall (c j) r

theorem hubCells_of_atom (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr : r ≤ 19/50) (hc : Covers c r) (hR : RingLabels c r) :
    HubCellStructure c r := by
  have hm (j : Fin 11) (hj : 9 ≤ j.val) : ‖c j‖ < 1 := by
    have hh := hub_strict_margin_of_atom h450 hr hc hR hj
    have hn := Covers.nonneg hc
    linarith
  refine ⟨?_, fun j _ => cell_convex c j, ?_, ?_, ?_⟩
  · intro j hj
    exact hub_cell_compact hc hR hj (hm j hj)
  · intro j hj
    apply center_mem_interior_of_ne
    intro i hi
    exact (private_point_ne (private_point_of_atom h450 hr hc hR hj) hi.symm).symm
  · intro j hj
    exact hub_cell_inside hc hR hj (hm j hj)
  · intro j hj
    exact hub_cell_radius hc hR hj (hm j hj)

theorem core_subset_hubCells {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hR : RingLabels c r) :
    Metric.ball (0 : Point) (1 - 2*r) ⊆ Cell c 9 ∪ Cell c 10 := by
  intro x hx
  have hxn : ‖x‖ < 1 - 2*r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hxD : x ∈ unitDisk := mem_unitDisk.mpr (by linarith [Covers.nonneg hc])
  obtain ⟨j, hj⟩ := exists_nearest c x
  have hd := nearest_le_radius hc hxD hj
  have hjhub : 9 ≤ j.val := by
    by_contra h
    have hring := hR.ring_meets (show j.val < 9 by omega)
    have hnorm := one_sub_le_norm_of_meetsCircle hring
    have ht := norm_le_norm_add_norm_sub x (c j)
    rw [norm_sub_rev x (c j)] at ht
    have hd' : ‖c j - x‖ ≤ r := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hd
    linarith
  have hjcases : j = (9 : Fin 11) ∨ j = 10 := by
    have hv := j.isLt
    have : j.val = 9 ∨ j.val = 10 := by omega
    exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  rcases hjcases with rfl | rfl
  · exact Or.inl hj
  · exact Or.inr hj

theorem disjoint_core_one_hub {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hR : RingLabels c r)
    (hdis : Metric.ball (0 : Point) (1 - 2*r) ∩ (Cell c 9 ∩ Cell c 10) = ∅) :
    Metric.ball (0 : Point) (1 - 2*r) ⊆ Cell c 9 ∨
      Metric.ball (0 : Point) (1 - 2*r) ⊆ Cell c 10 :=
  isPreconnected_iff_subset_of_disjoint_closed.mp (convex_ball (0 : Point) (1 - 2*r)).isPreconnected
    (Cell c 9) (Cell c 10) (cell_closed c 9) (cell_closed c 10)
    (core_subset_hubCells hc hR) hdis

end N11Formalization.ActualVoronoiCells

#check @N11Formalization.ActualVoronoiCells.hubCells_of_atom
#check @N11Formalization.ActualVoronoiCells.core_subset_hubCells
#check @N11Formalization.ActualVoronoiCells.disjoint_core_one_hub
#print axioms N11Formalization.ActualVoronoiCells.hubCells_of_atom
#print axioms N11Formalization.ActualVoronoiCells.core_subset_hubCells
#print axioms N11Formalization.ActualVoronoiCells.disjoint_core_one_hub
