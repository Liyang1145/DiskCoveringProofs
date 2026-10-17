import N11Formalization.DSHTopologyOwnershipLedger

/-! Mixed-radius whole-circle capacity, useful for actual ring locality.
This does NOT assert a cap grouping or a locality conclusion without its
geometric producer. No sampling or cap-position assumptions. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualMixedCircleCapacity
open MeasureTheory DSHTopologyOwnershipLedger

theorem sum_two_arcsin_ge_two_pi {ι : Type*} [Fintype ι]
    (c : ι → Point) (r : ι → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1)
    (hc : ∀ x : Point, ‖x‖ = 1 → ∃ i, dist x (c i) ≤ r i) :
    2*Real.pi ≤ ∑ i, 2*Real.arcsin (r i) := by
  let A := fun i => capPreimage (c i) (r i)
  have hcover : Set.Ioo (0:ℝ) (2*Real.pi) ⊆ ⋃ i, A i := by
    intro t ht
    obtain ⟨i,hi⟩ := hc (circleMap t) (circleMap_norm t)
    exact Set.mem_iUnion.mpr ⟨i,ht,hi⟩
  have hsub : (⋃ i, A i) ⊆ Set.Ioo (0:ℝ) (2*Real.pi) := by
    intro t ht
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ht
    exact hi.1
  have hfinite : volume (⋃ i, A i) ≠ ⊤ := by
    have hi : volume (Set.Ioo (0:ℝ) (2*Real.pi)) ≠ ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hi (measure_mono hsub)
  calc
    2*Real.pi = volume.real (Set.Ioo (0:ℝ) (2*Real.pi)) := by
      rw [Real.volume_real_Ioo_of_le (by positivity),sub_zero]
    _ ≤ volume.real (⋃ i, A i) := measureReal_mono hcover hfinite
    _ ≤ ∑ i, volume.real (A i) := measureReal_iUnion_fintype_le A
    _ ≤ ∑ i, 2*Real.arcsin (r i) := Finset.sum_le_sum fun i _ =>
      volumeReal_capPreimage_le (hr0 i) (hr1 i)

theorem arcsin_double_R0_lt : Real.arcsin ((19:ℝ)/25) < 9/10 := by
  apply (Real.arcsin_lt_iff_lt_sin (by norm_num : (19:ℝ)/25 ∈ Set.Icc (-1) 1)
    (by constructor <;> linarith [Real.pi_gt_three] : (9:ℝ)/10 ∈
      Set.Icc (-(Real.pi/2)) (Real.pi/2))).mpr
  have hs := Real.sin_gt_sub_cube (by norm_num : (0:ℝ) < 9/10)
  norm_num at hs ⊢
  linarith

theorem not_big_and_five_small {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 19/50)
    (p : Point) (c : Fin 5 → Point)
    (hc : ∀ x : Point, ‖x‖ = 1 →
      dist x p ≤ 2*r ∨ ∃ i : Fin 5, dist x (c i) ≤ r) : False := by
  let d : Unit ⊕ Fin 5 → Point := Sum.elim (fun _ => p) c
  let R : Unit ⊕ Fin 5 → ℝ := Sum.elim (fun _ => 2*r) (fun _ => r)
  have hh := sum_two_arcsin_ge_two_pi d R
    (by intro i; cases i <;> dsimp [R] <;> linarith)
    (by intro i; cases i <;> dsimp [R] <;> linarith)
    (by
      intro x hx
      rcases hc x hx with hp | hsmall
      · exact ⟨Sum.inl (),hp⟩
      · obtain ⟨i,hi⟩ := hsmall
        exact ⟨Sum.inr i,hi⟩)
  simp only [Fintype.sum_sum_type,d,R,Sum.elim_inl,Sum.elim_inr,
    Fintype.sum_unique,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  norm_num only [Fintype.card_unique,Nat.cast_one,one_mul,Nat.cast_ofNat] at hh
  have hdouble := (Real.arcsin_le_arcsin (show 2*r ≤ (19:ℝ)/25 by linarith)).trans_lt
    arcsin_double_R0_lt
  have hsmall := (Real.arcsin_le_arcsin hr.le).trans_lt arcsin_R0_lt_pi_div_eight
  linarith [Real.pi_gt_three,Real.pi_lt_d20]

end N11Formalization.ActualMixedCircleCapacity
#check @N11Formalization.ActualMixedCircleCapacity.sum_two_arcsin_ge_two_pi
#check @N11Formalization.ActualMixedCircleCapacity.not_big_and_five_small
#print axioms N11Formalization.ActualMixedCircleCapacity.not_big_and_five_small
