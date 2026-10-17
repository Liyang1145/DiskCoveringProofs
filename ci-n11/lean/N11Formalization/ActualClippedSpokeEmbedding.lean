import N11Formalization.ActualClippedMeshVertices

/-! ACTUAL clipped-cell spokes give an embedded topological dual skeleton.
Every spoke from the actual site to a tied boundary point stays strictly in
that cell until its endpoint. Different-cell spoke interiors are disjoint;
within one cell, two boundary spokes meet away from the site only when their
boundary endpoints coincide. No straight-dual or disk-graph premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualClippedSpokeEmbedding
open ActualVoronoiCells ActualVoronoiIncidence ActualClippedCellPartition
open ActualCoverStructuralReduction ActualVoronoiRadialExit

def spoke (c : Fin 11 → Point) (i : Fin 11) (x : Point) (t : ℝ) : Point :=
  c i+t • (x-c i)

theorem tied_point_not_cell_interior {c : Fin 11 → Point} (hc : Function.Injective c)
    {i j : Fin 11} (hij : i ≠ j) {x : Point}
    (hi : x ∈ Cell c i) (hj : x ∈ Cell c j) : x ∉ interior (ClippedCell c i) := by
  intro hx
  have hs := interior_cell_strict hc (interior_mono Set.inter_subset_right hx)
  exact not_lt_of_ge (hj i) (hs j hij.symm)

theorem spoke_interior {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) {i : Fin 11} {x : Point}
    (hx : x ∈ ClippedCell c i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    spoke c i x t ∈ interior (ClippedCell c i) := by
  have hh := (clipped_convex c i).add_smul_sub_mem_interior hx
    (Representative.clipped_center_interior h i)
    (t := 1-t) ⟨by linarith,by linarith⟩
  have he : x+(1-t) • (c i-x) = spoke c i x t := by unfold spoke; module
  rwa [he] at hh

theorem different_cell_spokes_disjoint {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) {i j : Fin 11} (hij : i ≠ j) {x y : Point}
    (hx : x ∈ ClippedCell c i) (hy : y ∈ ClippedCell c j) {s t : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    spoke c i x s ≠ spoke c j y t := by
  intro he
  have hI := spoke_interior h hx hs0 hs1
  have hJ := spoke_interior h hy ht0 ht1
  rw [← he] at hJ
  exact Set.disjoint_left.mp (clipped_interiors_disjoint h.injective hij) hI hJ

/-- Generic boundary-ray injectivity, paid using convex interior rather than
a planar drawing or an unproved cyclic order of cell boundary vertices. -/
theorem convex_boundary_spokes_unique {C : Set Point} (hC : Convex ℝ C)
    {a x y : Point} (ha : a ∈ interior C) (hx : x ∈ C) (hy : y ∈ C)
    (hxout : x ∉ interior C) (hyout : y ∉ interior C)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (he : a+s • (x-a) = a+t • (y-a)) : x = y := by
  have hraw : s • (x-a) = t • (y-a) := add_left_cancel he
  have hsame : s = t := by
    by_contra hnot
    rcases lt_or_gt_of_ne hnot with hst | hts
    · have hratio : 0 < s/t := div_pos hs ht
      have hratio1 : s/t ≤ 1 := (div_le_one ht).mpr hst.le
      have hh := hC.add_smul_sub_mem_interior hx ha
        (t := 1-s/t) ⟨by have hh := (div_lt_one ht).mpr hst; linarith,by linarith⟩
      have hscaled := congrArg (fun z : Point => t⁻¹ • z) hraw
      simp only [smul_smul,inv_mul_cancel₀ ht.ne',one_smul] at hscaled
      have hyform : x+(1-s/t) • (a-x) = y := by
        have h1 : x+(1-s/t) • (a-x) = a+(s/t) • (x-a) := by module
        rw [h1,div_eq_mul_inv,mul_comm,hscaled]
        abel
      exact hyout (by rwa [hyform] at hh)
    · have hratio : 0 < t/s := div_pos ht hs
      have hh := hC.add_smul_sub_mem_interior hy ha
        (t := 1-t/s) ⟨by have hh := (div_lt_one hs).mpr hts; linarith,by linarith⟩
      have hscaled := congrArg (fun z : Point => s⁻¹ • z) hraw.symm
      simp only [smul_smul,inv_mul_cancel₀ hs.ne',one_smul] at hscaled
      have hxform : y+(1-t/s) • (a-y) = x := by
        have h1 : y+(1-t/s) • (a-y) = a+(t/s) • (y-a) := by module
        rw [h1,div_eq_mul_inv,mul_comm,hscaled]
        abel
      exact hxout (by rwa [hxform] at hh)
  rw [hsame] at hraw
  have heq : x-a = y-a := (smul_right_injective _ ht.ne') hraw
  exact sub_left_inj.mp heq

theorem same_cell_spokes_unique {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) {i : Fin 11} {x y : Point}
    (hx : x ∈ ClippedCell c i) (hy : y ∈ ClippedCell c i)
    (hxout : x ∉ interior (ClippedCell c i)) (hyout : y ∉ interior (ClippedCell c i))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (he : spoke c i x s = spoke c i y t) : x = y :=
  convex_boundary_spokes_unique (clipped_convex c i)
    (Representative.clipped_center_interior h i) hx hy hxout hyout hs ht he

theorem tied_spokes_same_cell_unique {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) {i j k : Fin 11} (hij : i ≠ j) (hik : i ≠ k)
    {x y : Point} (hx : x ∈ unitDisk) (hy : y ∈ unitDisk)
    (hxij : x ∈ Cell c i ∩ Cell c j) (hyik : y ∈ Cell c i ∩ Cell c k)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (he : spoke c i x s = spoke c i y t) : x = y :=
  same_cell_spokes_unique h ⟨hx,hxij.1⟩ ⟨hy,hyik.1⟩
    (tied_point_not_cell_interior h.injective hij hxij.1 hxij.2)
    (tied_point_not_cell_interior h.injective hik hyik.1 hyik.2) hs ht he

end N11Formalization.ActualClippedSpokeEmbedding
#check @N11Formalization.ActualClippedSpokeEmbedding.different_cell_spokes_disjoint
#check @N11Formalization.ActualClippedSpokeEmbedding.tied_spokes_same_cell_unique
#print axioms N11Formalization.ActualClippedSpokeEmbedding.spoke_interior
#print axioms N11Formalization.ActualClippedSpokeEmbedding.convex_boundary_spokes_unique
#print axioms N11Formalization.ActualClippedSpokeEmbedding.tied_spokes_same_cell_unique
