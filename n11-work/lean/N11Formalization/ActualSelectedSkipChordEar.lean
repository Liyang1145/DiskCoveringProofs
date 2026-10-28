import N11Formalization.ActualTriangleChainRows
import N11Formalization.ActualShortChordHubData

/-! Every ACTUAL selected skip-one ring chord has its selected short ear.
Without that ear, real boundary coefficient conservation forces a
three-ring closed cycle in one hub link, contradicting its true connected
degree2 link containing the other hub. No global disk/Euler premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSelectedSkipChordEar
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementLocalLinks
open ActualRefinementVertexLinks ActualTriangleBoundaryChain ActualTriangleChainRows
open ActualShortChordHubData ActualHubLinkNoRingCycle
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder

theorem third_ring_face_ne {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    {A D : R.Index} {p m n h : Fin 11}
    (hmp : m ≠ p) (hmn : m ≠ n) (hmh : m ≠ h)
    (hA : labelSet R A = {p,n,h}) (hD : m ∈ labelSet R D) : A ≠ D := by
  intro he
  rw [← he,hA] at hD
  simp only [Finset.mem_insert,Finset.mem_singleton] at hD
  rcases hD with he | he | he
  · exact hmp he
  · exact hmn he
  · exact hmh he

theorem short_boundary_chord_coefficient {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} (R : Refinement c r)
    {A D : R.Index} {p m n h : Fin 11}
    (hpm : p ≠ m) (hmn : m ≠ n) (hph : p ≠ h) (hmh : m ≠ h) (hnh : n ≠ h)
    (hA : labelSet R A = {p,n,h}) (hD : labelSet R D = {p,m,h}) :
    coefficient R A p n = -coefficient R D p m := by
  have hDm : m ∈ labelSet R D := by rw [hD]; simp
  have hAD := third_ring_face_ne R hpm.symm hmn hmh hA hDm
  have hcancel := coefficient_shared_cancel hc R hAD hph
    (show p ∈ labelSet R A by rw [hA]; simp)
    (show h ∈ labelSet R A by rw [hA]; simp)
    (show p ∈ labelSet R D by rw [hD]; simp)
    (show h ∈ labelSet R D by rw [hD]; simp)
  have hrowA := coefficient_three_label_row R hnh hA
  have hrowD := coefficient_three_label_row R hmh hD
  omega

theorem right_boundary_chord_coefficient {c : Fin 11 → Point}
    (hc : Function.Injective c) {r : ℝ} (R : Refinement c r)
    {A E : R.Index} {p m n h : Fin 11}
    (hpm : p ≠ m) (hmn : m ≠ n) (hph : p ≠ h) (hmh : m ≠ h) (hnh : n ≠ h)
    (hA : labelSet R A = {p,n,h}) (hE : labelSet R E = {m,n,h}) :
    coefficient R A p n = -coefficient R E m n := by
  have hA' : labelSet R A = {n,p,h} := by rw [hA,Finset.insert_comm]
  have hE' : labelSet R E = {n,m,h} := by rw [hE,Finset.insert_comm]
  have hh := short_boundary_chord_coefficient hc R hmn.symm hpm.symm hnh hmh hph hA' hE'
  rw [coefficient_antisymm R A n p,coefficient_antisymm R E n m] at hh
  omega

theorem link_adj_of_three_labels {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A : R.Index} {p q h : Fin 11}
    (hpq : p ≠ q) (hph : p ≠ h) (hqh : q ≠ h)
    (hA : labelSet R A = {p,q,h}) : (linkGraph R h).Adj p q := by
  exact ⟨hpq,hph,hqh,A,by rw [hA]; simp,by rw [hA]; simp,by rw [hA]; simp⟩

theorem hub_ne_ring {h p : Fin 11} (hh : 9 ≤ h.val) (hp : p.val < 9) : h ≠ p := by
  intro he
  subst p
  omega

theorem actual_selected_skip_chord_ear {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r) (i : Fin 9)
    (hp : Neighbor R (prevSite i) (nextSite i)) : SelectedEarAt R i := by
  by_contra hno
  obtain ⟨A,B,hAB,hA,hB⟩ := actual_skip_no_ear_two_hubs h hr R i hp hno
  obtain ⟨⟨D,hD⟩,⟨E,hE⟩⟩ := actual_skip_short_boundary_hubs h hr R i hp hno
  have hd := boundary_sites_distinct i
  have hp9 : prevSite i ≠ (9 : Fin 11) := (hub_ne_ring (h := 9) (p := prevSite i)
    (by decide) (i-1).isLt).symm
  have hm9 : ringSite i ≠ (9 : Fin 11) := (hub_ne_ring (h := 9) (p := ringSite i)
    (by decide) i.isLt).symm
  have hn9 : nextSite i ≠ (9 : Fin 11) := (hub_ne_ring (h := 9) (p := nextSite i)
    (by decide) (nextRing i).isLt).symm
  have hp10 : prevSite i ≠ (10 : Fin 11) := (hub_ne_ring (h := 10) (p := prevSite i)
    (by decide) (i-1).isLt).symm
  have hm10 : ringSite i ≠ (10 : Fin 11) := (hub_ne_ring (h := 10) (p := ringSite i)
    (by decide) i.isLt).symm
  have hn10 : nextSite i ≠ (10 : Fin 11) := (hub_ne_ring (h := 10) (p := nextSite i)
    (by decide) (nextRing i).isLt).symm
  have hc := coefficient_shared_cancel h.injective R hAB hd.2.2
    (show prevSite i ∈ labelSet R A by rw [hA]; simp)
    (show nextSite i ∈ labelSet R A by rw [hA]; simp)
    (show prevSite i ∈ labelSet R B by rw [hB]; simp)
    (show nextSite i ∈ labelSet R B by rw [hB]; simp)
  rcases hD with hD | hD <;> rcases hE with hE | hE
  · exact actual_hub_no_three_ring_cycle h hr R (i := 9) (u := 10) (Or.inl ⟨rfl,rfl⟩)
      (i-1).isLt i.isLt (nextRing i).isLt hd.1 hd.2.2.symm hd.2.1
      (link_adj_of_three_labels R hd.1 hp9 hm9 hD)
      (link_adj_of_three_labels R hd.2.1.symm hm9 hn9 hE)
      (link_adj_of_three_labels R hd.2.2 hp9 hn9 hA).symm
  · have hl := short_boundary_chord_coefficient h.injective R hd.1 hd.2.1.symm
      hp9 hm9 hn9 hA hD
    have hr' := right_boundary_chord_coefficient h.injective R hd.1 hd.2.1.symm
      hp10 hm10 hn10 hB hE
    have heq := actual_short_boundary_coefficients_equal h hr R i
      (show prevSite i ∈ labelSet R D by rw [hD]; simp)
      (show ringSite i ∈ labelSet R D by rw [hD]; simp)
      (show ringSite i ∈ labelSet R E by rw [hE]; simp)
      (show nextSite i ∈ labelSet R E by rw [hE]; simp)
    have hnz := coefficient_nonzero_of_third R hd.1 hp9.symm hm9.symm
      (show prevSite i ∈ labelSet R D by rw [hD]; simp)
      (show ringSite i ∈ labelSet R D by rw [hD]; simp)
      (show (9 : Fin 11) ∈ labelSet R D by rw [hD]; simp)
    omega
  · have hl := short_boundary_chord_coefficient h.injective R hd.1 hd.2.1.symm
      hp10 hm10 hn10 hB hD
    have hr' := right_boundary_chord_coefficient h.injective R hd.1 hd.2.1.symm
      hp9 hm9 hn9 hA hE
    have heq := actual_short_boundary_coefficients_equal h hr R i
      (show prevSite i ∈ labelSet R D by rw [hD]; simp)
      (show ringSite i ∈ labelSet R D by rw [hD]; simp)
      (show ringSite i ∈ labelSet R E by rw [hE]; simp)
      (show nextSite i ∈ labelSet R E by rw [hE]; simp)
    have hnz := coefficient_nonzero_of_third R hd.1 hp10.symm hm10.symm
      (show prevSite i ∈ labelSet R D by rw [hD]; simp)
      (show ringSite i ∈ labelSet R D by rw [hD]; simp)
      (show (10 : Fin 11) ∈ labelSet R D by rw [hD]; simp)
    omega
  · exact actual_hub_no_three_ring_cycle h hr R (i := 10) (u := 9) (Or.inr ⟨rfl,rfl⟩)
      (i-1).isLt i.isLt (nextRing i).isLt hd.1 hd.2.2.symm hd.2.1
      (link_adj_of_three_labels R hd.1 hp10 hm10 hD)
      (link_adj_of_three_labels R hd.2.1.symm hm10 hn10 hE)
      (link_adj_of_three_labels R hd.2.2 hp10 hn10 hB).symm

end N11Formalization.ActualSelectedSkipChordEar
#check @N11Formalization.ActualSelectedSkipChordEar.actual_selected_skip_chord_ear
#print axioms N11Formalization.ActualSelectedSkipChordEar.actual_selected_skip_chord_ear
