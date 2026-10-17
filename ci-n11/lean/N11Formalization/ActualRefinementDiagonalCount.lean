import N11Formalization.ActualRefinementInteriorFacetCount
import N11Formalization.ActualLocalRefinementPairCounts

/-! Every SELECTED nonadjacent polygon diagonal has exactly TWO global
selected triangle incidences. Its global nearest-witness rigidity pins all
triangle indices to one primal polygon; a proved finite bijection transfers
the actual local fan pair count, not an assumed graph incidence. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRefinementDiagonalCount
open ActualVoronoiCells ActualVoronoiIncidence ActualFiniteNearestRefinement
open ActualRefinementTriangleUniqueness ActualIncidentFanRefinement
open ActualRefinementSideMultiplicity ActualRefinementInteriorFacetCount
open ActualLocalRefinementPairCounts ActualNearestPairRigidity

theorem singular_pair_count_transfer {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (v : R.vertices)
    (I J : Fin (incident c (R.face v).point).card) {i j : Fin 11}
    (hI : ((R.order v).order I).val = i) (hJ : ((R.order v).order J).val = j)
    (hSingle : ∀ a : R.Index, a ∈ pairTriangles R i j → R.witness a = (R.face v).point) :
    (pairTriangles R i j).card =
      (pairIndices (lt_of_lt_of_le (by decide : 0 < 3) (R.face v).at_least_three) I J).card := by
  classical
  let hn : 0 < (incident c (R.face v).point).card :=
    lt_of_lt_of_le (by decide : 0 < 3) (R.face v).at_least_three
  let T := pairIndices hn I J
  let S := pairTriangles R i j
  let g : T → S := fun k => by
    have hk := (Finset.mem_filter.mp k.property).2
    let K : {k : Fin (incident c (R.face v).point).card // FanIndex k} := ⟨k.val,hk.1⟩
    refine ⟨⟨v,K⟩,mem_pairTriangles.mpr ⟨?_,?_⟩⟩
    · have hh := (local_label_mem R v K I).mpr hk.2.1
      rwa [hI] at hh
    · have hh := (local_label_mem R v K J).mpr hk.2.2
      rwa [hJ] at hh
  have hg : Function.Bijective g := by
    constructor
    · intro k l he
      apply Subtype.ext
      apply Fin.ext
      exact congrArg (fun a : S => a.val.2.val.val) he
    · intro a
      rcases a with ⟨⟨w,k⟩,ha⟩
      have hw : w = v := by
        apply Subtype.ext
        have hh := hSingle ⟨w,k⟩ ha
        simpa only [Refinement.witness,R.base] using hh
      subst w
      have hmem := mem_pairTriangles.mp ha
      have hkI : I ∈ indexTriangle hn k.val := by
        apply (local_label_mem R v k I).mp
        rw [hI]
        exact hmem.1
      have hkJ : J ∈ indexTriangle hn k.val := by
        apply (local_label_mem R v k J).mp
        rw [hJ]
        exact hmem.2
      let K : T := ⟨k.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,k.property,hkI,hkJ⟩⟩
      refine ⟨K,?_⟩
      apply Subtype.ext
      rfl
  have hcard := Fintype.card_congr (Equiv.ofBijective g hg)
  simpa only [Fintype.card_coe] using hcard.symm

theorem actual_selected_diagonal_count {c : Fin 11 → Point} (hc : Function.Injective c)
    {r : ℝ} (R : Refinement c r) (v : R.vertices)
    {I J k : Fin (incident c (R.face v).point).card}
    (hIJ : I ≠ J) (hnadj : ¬ Adjacent I J) (hk : FanIndex k)
    (hIk : I ∈ indexTriangle (lt_of_lt_of_le (by decide : 0 < 3) (R.face v).at_least_three) k)
    (hJk : J ∈ indexTriangle (lt_of_lt_of_le (by decide : 0 < 3) (R.face v).at_least_three) k) :
    (pairTriangles R ((R.order v).order I).val ((R.order v).order J).val).card = 2 := by
  have hn1 : J ≠ finRotate (incident c (R.face v).point).card I :=
    fun he => hnadj (Or.inl he)
  have hn2 : I ≠ finRotate (incident c (R.face v).point).card J :=
    fun he => hnadj (Or.inr he)
  have hsingle (a : R.Index)
      (ha : a ∈ pairTriangles R ((R.order v).order I).val ((R.order v).order J).val) :
      R.witness a = (R.face v).point := by
    have hmem := mem_pairTriangles.mp ha
    exact nonadjacent_diagonal_unique_witness hc (R.order v) hIJ hn1 hn2
      ⟨nearest_of_label_mem R hmem.1,nearest_of_label_mem R hmem.2⟩
  rw [singular_pair_count_transfer R v I J rfl rfl hsingle]
  exact selected_diagonal_count (R.face v).at_least_three (R.face v).at_most_five
    I J k hIJ hnadj hk hIk hJk

end N11Formalization.ActualRefinementDiagonalCount
#check @N11Formalization.ActualRefinementDiagonalCount.singular_pair_count_transfer
#check @N11Formalization.ActualRefinementDiagonalCount.actual_selected_diagonal_count
#print axioms N11Formalization.ActualRefinementDiagonalCount.singular_pair_count_transfer
#print axioms N11Formalization.ActualRefinementDiagonalCount.actual_selected_diagonal_count
