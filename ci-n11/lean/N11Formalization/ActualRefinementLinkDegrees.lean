import N11Formalization.ActualRefinementDoubleCounting

/-! Exact local link degrees of the ACTUAL selected triangle family.
For a selected pair(i,j), each incident triangle contributes one unique
third neighbor in link(i); injective labelSets rule out repeated neighbors.
Thus link degree is1 on boundary pairs and2 everywhere else. This does not
assume/prove that each link is connected; that remains the next step. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementLinkDegrees
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualRefinementInteriorFacetCount
open ActualSelectedEdgeIncidence

theorem three_set_third {s : Finset (Fin 11)} (hs : s.card = 3)
    {i j : Fin 11} (hij : i ≠ j) (hi : i ∈ s) (hj : j ∈ s) :
    ∃ k : Fin 11, k ≠ i ∧ k ≠ j ∧ s = {i,j,k} := by
  have hjE : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm,hj⟩
  have hci : (s.erase i).card = 2 := by
    have hh := Finset.card_erase_add_one hi
    omega
  have hcj : ((s.erase i).erase j).card = 1 := by
    have hh := Finset.card_erase_add_one hjE
    omega
  obtain ⟨k,hk⟩ := Finset.card_eq_one.mp hcj
  have hkE : k ∈ (s.erase i).erase j := by rw [hk]; simp
  have hkj := (Finset.mem_erase.mp hkE).1
  have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hkE).2).1
  refine ⟨k,hki,hkj,?_⟩
  calc
    s = insert i (s.erase i) := (Finset.insert_erase hi).symm
    _ = insert i (insert j ((s.erase i).erase j)) := by rw [Finset.insert_erase hjE]
    _ = {i,j,k} := by rw [hk]

def third {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (i j : Fin 11) (hij : i ≠ j) (a : pairTriangles R i j) : Fin 11 :=
  Classical.choose (three_set_third (labelSet_card R a.val) hij
    (mem_pairTriangles.mp a.property).1 (mem_pairTriangles.mp a.property).2)

theorem third_spec {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (i j : Fin 11) (hij : i ≠ j) (a : pairTriangles R i j) :
    third R i j hij a ≠ i ∧ third R i j hij a ≠ j ∧
      labelSet R a.val = {i,j,third R i j hij a} :=
  Classical.choose_spec (three_set_third (labelSet_card R a.val) hij
    (mem_pairTriangles.mp a.property).1 (mem_pairTriangles.mp a.property).2)

theorem third_injective {c : Fin 11 → Point} (hc : Function.Injective c)
    {r : ℝ} (R : Refinement c r) (i j : Fin 11) (hij : i ≠ j) :
    Function.Injective (third R i j hij) := by
  intro a b he
  apply Subtype.ext
  apply labelSet_injective hc R
  rw [(third_spec R i j hij a).2.2,(third_spec R i j hij b).2.2,he]

def linkNeighbors {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i j : Fin 11) (hij : i ≠ j) : Finset (Fin 11) := by
  classical
  exact Finset.univ.image (third R i j hij)

theorem mem_linkNeighbors {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i j : Fin 11) (hij : i ≠ j) {k : Fin 11} :
    k ∈ linkNeighbors R i j hij ↔
      k ≠ i ∧ k ≠ j ∧ ∃ a : R.Index, {i,j,k} ⊆ labelSet R a := by
  classical
  constructor
  · intro hk
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hk
    have hs := third_spec R i j hij a
    rw [ha] at hs
    exact ⟨hs.1,hs.2.1,a.val,by rw [hs.2.2]⟩
  · rintro ⟨hki,hkj,a,hsub⟩
    have hi : i ∈ labelSet R a := hsub (by simp)
    have hj : j ∈ labelSet R a := hsub (by simp)
    let A : pairTriangles R i j := ⟨a,mem_pairTriangles.mpr ⟨hi,hj⟩⟩
    have hk : k ∈ labelSet R a := hsub (by simp)
    have hs := (third_spec R i j hij A).2.2
    rw [hs] at hk
    have hkt : k = third R i j hij A := by
      rcases Finset.mem_insert.mp hk with he | hk
      · exact (hki he).elim
      rcases Finset.mem_insert.mp hk with he | hk
      · exact (hkj he).elim
      exact Finset.mem_singleton.mp hk
    exact Finset.mem_image.mpr ⟨A,Finset.mem_univ _,hkt.symm⟩

theorem link_card_eq_pair_incidence {c : Fin 11 → Point} (hc : Function.Injective c)
    {r : ℝ} (R : Refinement c r) (i j : Fin 11) (hij : i ≠ j) :
    (linkNeighbors R i j hij).card = (pairTriangles R i j).card := by
  classical
  rw [linkNeighbors,Finset.card_image_of_injective _ (third_injective hc R i j hij),Finset.card_univ]
  exact Fintype.card_coe _

theorem actual_link_degree {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    {i j : Fin 11} (hij : i ≠ j) {a : R.Index}
    (hai : i ∈ labelSet R a) (haj : j ∈ labelSet R a) :
    (linkNeighbors R i j hij).card = if BoundaryLabels i j then 1 else 2 := by
  rw [link_card_eq_pair_incidence h.injective R i j hij]
  exact actual_selected_edge_incidence h hr R hij hai haj

end N11Formalization.ActualRefinementLinkDegrees
#check @N11Formalization.ActualRefinementLinkDegrees.actual_link_degree
#print axioms N11Formalization.ActualRefinementLinkDegrees.third_injective
#print axioms N11Formalization.ActualRefinementLinkDegrees.actual_link_degree
