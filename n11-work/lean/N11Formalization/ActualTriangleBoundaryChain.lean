import N11Formalization.ActualSelectedEdgeOrientation

/-! Integer boundary chain of each genuinely positive selected triangle.
This supplies the algebraic boundary-of-boundary identity, without
assuming a planar disk or Euler characteristic. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualTriangleBoundaryChain
open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open ActualIncidentFacetAdjacency ActualSelectedEdgeOrientation FlashTiling

def triangleBoundary (t : Fin 3 → Fin 11) (i j : Fin 11) : ℤ :=
  (if i=t 0 ∧ j=t 1 then 1 else 0) +
  (if i=t 1 ∧ j=t 2 then 1 else 0) +
  (if i=t 2 ∧ j=t 0 then 1 else 0) -
  (if j=t 0 ∧ i=t 1 then 1 else 0) -
  (if j=t 1 ∧ i=t 2 then 1 else 0) -
  (if j=t 2 ∧ i=t 0 then 1 else 0)

theorem triangle_boundary_antisymm (t : Fin 3 → Fin 11) (i j : Fin 11) :
    triangleBoundary t i j = -triangleBoundary t j i := by
  unfold triangleBoundary
  ring

theorem triangle_boundary_row_zero (t : Fin 3 → Fin 11) (i : Fin 11) :
    ∑ j : Fin 11, triangleBoundary t i j = 0 := by
  simp only [triangleBoundary,Finset.sum_add_distrib,Finset.sum_sub_distrib,ite_and]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp
  ring

theorem triangle_boundary_outside (t : Fin 3 → Fin 11) {i j : Fin 11}
    (h : i ∉ Set.range t ∨ j ∉ Set.range t) : triangleBoundary t i j = 0 := by
  have hne {k : Fin 11} (hk : k ∉ Set.range t) (v : Fin 3) : k ≠ t v :=
    fun he => hk ⟨v,he.symm⟩
  rcases h with hi | hj
  · simp [triangleBoundary,hne hi 0,hne hi 1,hne hi 2]
  · simp [triangleBoundary,hne hj 0,hne hj 1,hne hj 2]

theorem positive_triangle_boundary_sign {c : Fin 11 → Point} {t : Fin 3 → Fin 11}
    (hinj : Function.Injective t)
    (hpos : 0 < orient (c (t 0)) (c (t 1)) (c (t 2)))
    (I J K : Fin 3) (hIJ : I ≠ J) (hKI : K ≠ I) (hKJ : K ≠ J) :
    triangleBoundary t (t I) (t J) =
      if 0 < orient (c (t I)) (c (t J)) (c (t K)) then 1 else -1 := by
  have h120 : 0 < orient (c (t 1)) (c (t 2)) (c (t 0)) := by
    rw [← orient_cycle]
    exact hpos
  have h201 : 0 < orient (c (t 2)) (c (t 0)) (c (t 1)) := by
    rw [orient_cycle]
    exact hpos
  have h021 : ¬ 0 < orient (c (t 0)) (c (t 2)) (c (t 1)) := by
    rw [orient_swap]
    linarith
  have h102 : ¬ 0 < orient (c (t 1)) (c (t 0)) (c (t 2)) := by
    rw [orient_swap]
    linarith
  have h210 : ¬ 0 < orient (c (t 2)) (c (t 1)) (c (t 0)) := by
    rw [orient_swap]
    linarith
  have h01 := hinj.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := hinj.ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := hinj.ne (by decide : (1 : Fin 3) ≠ 2)
  fin_cases I <;> fin_cases J <;> fin_cases K <;>
    simp_all [triangleBoundary,Ne.symm h01,Ne.symm h02,Ne.symm h12]

def coefficient {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (a : R.Index) (i j : Fin 11) : ℤ := triangleBoundary (R.labels a) i j

theorem coefficient_row_zero {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (a : R.Index) (i : Fin 11) :
    ∑ j : Fin 11, coefficient R a i j = 0 :=
  triangle_boundary_row_zero _ _

theorem coefficient_antisymm {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (a : R.Index) (i j : Fin 11) :
    coefficient R a i j = -coefficient R a j i :=
  triangle_boundary_antisymm _ _ _

theorem coefficient_of_third {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {a : R.Index} {i j k : Fin 11}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hi : i ∈ labelSet R a) (hj : j ∈ labelSet R a) (hk : k ∈ labelSet R a) :
    coefficient R a i j = if 0 < orient (c i) (c j) (c k) then 1 else -1 := by
  obtain ⟨I,hI⟩ := mem_labelSet.mp hi
  obtain ⟨J,hJ⟩ := mem_labelSet.mp hj
  obtain ⟨K,hK⟩ := mem_labelSet.mp hk
  have hIJ : I ≠ J := fun he => hij (by rw [← hI,← hJ,he])
  have hKI : K ≠ I := fun he => hki (by rw [← hK,← hI,he])
  have hKJ : K ≠ J := fun he => hkj (by rw [← hK,← hJ,he])
  have hh := positive_triangle_boundary_sign (Refinement.labels_injective R a)
    (Refinement.real_triangle R a).2.2 I J K hIJ hKI hKJ
  simpa only [hI,hJ,hK,coefficient] using hh

theorem coefficient_zero_of_not_pair {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {a : R.Index} {i j : Fin 11}
    (h : ¬ (i ∈ labelSet R a ∧ j ∈ labelSet R a)) : coefficient R a i j = 0 := by
  apply triangle_boundary_outside
  have he (k : Fin 11) : k ∈ labelSet R a ↔ k ∈ Set.range (R.labels a) := mem_labelSet
  simpa only [he,not_and_or] using h

theorem coefficient_shared_cancel {c : Fin 11 → Point} (hc : Function.Injective c)
    {r : ℝ} (R : Refinement c r) {a b : R.Index} (hab : a ≠ b)
    {i j : Fin 11} (hij : i ≠ j)
    (hai : i ∈ labelSet R a) (haj : j ∈ labelSet R a)
    (hbi : i ∈ labelSet R b) (hbj : j ∈ labelSet R b) :
    coefficient R a i j + coefficient R b i j = 0 := by
  classical
  obtain ⟨k,hki,hkj,hA⟩ := ActualRefinementLinkDegrees.three_set_third
    (labelSet_card R a) hij hai haj
  obtain ⟨l,hli,hlj,hB⟩ := ActualRefinementLinkDegrees.three_set_third
    (labelSet_card R b) hij hbi hbj
  have hak : k ∈ labelSet R a := by rw [hA]; simp
  have hbl : l ∈ labelSet R b := by rw [hB]; simp
  have ho := actual_shared_edge_opposite hc R hab hij hki hkj hli hlj
    hai haj hak hbi hbj hbl
  rw [coefficient_of_third R hij hki hkj hai haj hak,
    coefficient_of_third R hij hli hlj hbi hbj hbl]
  rcases mul_neg_iff.mp ho with ⟨hp,hn⟩ | ⟨hn,hp⟩
  · rw [if_pos hp,if_neg (by linarith)]
    norm_num
  · rw [if_neg (by linarith),if_pos hp]
    norm_num

def total {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) (i j : Fin 11) : ℤ :=
  ∑ a : R.Index, coefficient R a i j

theorem total_row_zero {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) : ∑ j : Fin 11, total R i j = 0 := by
  unfold total
  rw [Finset.sum_comm]
  simp only [coefficient_row_zero,Finset.sum_const_zero]

end N11Formalization.ActualTriangleBoundaryChain
#check @N11Formalization.ActualTriangleBoundaryChain.coefficient_shared_cancel
#check @N11Formalization.ActualTriangleBoundaryChain.total_row_zero
#print axioms N11Formalization.ActualTriangleBoundaryChain.coefficient_shared_cancel
#print axioms N11Formalization.ActualTriangleBoundaryChain.total_row_zero
