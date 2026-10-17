import N11Formalization.ActualMixedCircleCapacity
import N11Formalization.ActualRingDirectionOrder

/-! Actual metric exclusion of TWO disjoint-label ring triples with common
points. No planar graph/ear assertion is smuggled in; this applies to any
two true triple witnesses in the whole plane. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualTwoTripleCapacity
open DSHTopologyInterior ActualRingDirectionOrder ActualMixedCircleCapacity

theorem not_two_big_and_three_small {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 19/50)
    (p q : Point) (c : Fin 3 → Point)
    (hc : ∀ x : Point, ‖x‖ = 1 →
      dist x p ≤ 2*r ∨ dist x q ≤ 2*r ∨ ∃ i : Fin 3, dist x (c i) ≤ r) : False := by
  let d : Fin 2 ⊕ Fin 3 → Point := Sum.elim ![p,q] c
  let R : Fin 2 ⊕ Fin 3 → ℝ := Sum.elim (fun _ => 2*r) (fun _ => r)
  have hh := sum_two_arcsin_ge_two_pi d R
    (by intro i; cases i <;> dsimp [R] <;> linarith)
    (by intro i; cases i <;> dsimp [R] <;> linarith)
    (by
      intro x hx
      rcases hc x hx with hp | hq | hsmall
      · exact ⟨Sum.inl 0,hp⟩
      · exact ⟨Sum.inl 1,hq⟩
      · obtain ⟨i,hi⟩ := hsmall
        exact ⟨Sum.inr i,hi⟩)
  simp only [Fintype.sum_sum_type,R,Sum.elim_inl,Sum.elim_inr,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hdouble := (Real.arcsin_le_arcsin (show 2*r ≤ (19:ℝ)/25 by linarith)).trans_lt
    arcsin_double_R0_lt
  have hsmall := (Real.arcsin_le_arcsin hr.le).trans_lt arcsin_R0_lt_pi_div_eight
  linarith [Real.pi_gt_three]

theorem no_disjoint_common_triples {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (p q : Point) (s t : Finset (Fin 9)) (hs : s.card = 3) (ht : t.card = 3)
    (hdis : Disjoint s t)
    (hcommonS : ∀ i ∈ s, dist p (c (ringSite i)) ≤ r)
    (hcommonT : ∀ i ∈ t, dist q (c (ringSite i)) ≤ r) : False := by
  classical
  have hcardUnion : (s∪t).card = 6 := by rw [Finset.card_union_of_disjoint hdis,hs,ht]
  let T := {i : Fin 9 // i ∉ s∪t}
  have hcard : Fintype.card T = 3 := by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,hcardUnion]
  let e : T ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let d : Fin 3 → Point := fun j => c (ringSite (e.symm j).val)
  apply not_two_big_and_three_small (Covers.nonneg hc) hr p q d
  intro x hx
  obtain ⟨j,hj⟩ := hc x (mem_unitDisk.mpr hx.le)
  have hj9 : j.val < 9 := (hR j).mp ⟨x,hx,hj⟩
  let i : Fin 9 := ⟨j.val,hj9⟩
  have hi : dist x (c (ringSite i)) ≤ r := hj
  by_cases his : i ∈ s
  · left
    have hh := dist_triangle x (c (ringSite i)) p
    rw [dist_comm (c (ringSite i)) p] at hh
    linarith [hcommonS i his]
  · right
    by_cases hit : i ∈ t
    · left
      have hh := dist_triangle x (c (ringSite i)) q
      rw [dist_comm (c (ringSite i)) q] at hh
      linarith [hcommonT i hit]
    · right
      have hin : i ∉ s∪t := by simpa only [Finset.mem_union,not_or] using And.intro his hit
      let a : T := ⟨i,hin⟩
      refine ⟨e a,?_⟩
      change dist x (c (ringSite (e.symm (e a)).val)) ≤ r
      rw [e.symm_apply_apply]
      exact hi

end N11Formalization.ActualTwoTripleCapacity
#check @N11Formalization.ActualTwoTripleCapacity.no_disjoint_common_triples
#print axioms N11Formalization.ActualTwoTripleCapacity.no_disjoint_common_triples
