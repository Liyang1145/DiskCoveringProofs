import N11Formalization.ActualCapClusterCapacity

/-! Actual metric exclusion of a ring disk intersecting FOUR other rings.
Large-radius3R0 cap is bounded by a cosine window, NOT by a false arcsin
formula for radius>1. Norm≥1-r is derived from actual circle meeting. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualFiveRingStar
open MeasureTheory DSHTopologyInterior ActualRingDirectionOrder
open DSHTopologyOwnershipLedger

theorem cos_star_bound : Real.cos ((151:ℝ)/100) < 53/775 := by
  have hx : 0 ≤ Real.pi/2-(151:ℝ)/100 := by linarith [Real.pi_gt_d2]
  have hs := Real.sin_le hx
  rw [Real.sin_pi_div_two_sub] at hs
  linarith [Real.pi_lt_d20]

theorem arcsin_R0_lt_39 : Real.arcsin ((19:ℝ)/50) < 39/100 := by
  apply (Real.arcsin_lt_iff_lt_sin (by norm_num : (19:ℝ)/50 ∈ Set.Icc (-1) 1)
    (by constructor <;> linarith [Real.pi_gt_three] : (39:ℝ)/100 ∈
      Set.Icc (-(Real.pi/2)) (Real.pi/2))).mpr
  have hs := Real.sin_gt_sub_cube (by norm_num : (0:ℝ) < 39/100)
  norm_num at hs ⊢
  linarith

theorem star_threshold {p : Point} (hn : (31:ℝ)/50 ≤ ‖p‖) :
    (53:ℝ)/775 ≤ (1+‖p‖^2-((57:ℝ)/50)^2)/(2*‖p‖) := by
  rw [le_div_iff₀ (by linarith : 0 < 2*‖p‖)]
  have hprod : 0 ≤ (‖p‖-(31:ℝ)/50)*(‖p‖+(31:ℝ)/50-(106:ℝ)/775) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem star_window_volume {p : Point} (hn : (31:ℝ)/50 ≤ ‖p‖) :
    volume.real (capPreimage p ((57:ℝ)/50)) ≤ 2*((151:ℝ)/100) := by
  have hpos : 0 < ‖p‖ := by linarith
  have hp : p ≠ 0 := norm_pos_iff.mp hpos
  let theta := circleAngle (centerDir p)
  have htheta : theta ∈ Set.Ioc (-Real.pi) Real.pi := circleAngle_mem_Ioc _
  have hsub : capPreimage p ((57:ℝ)/50) ⊆
      {t : ℝ | t ∈ Set.Ioo 0 (2*Real.pi) ∧ Real.cos ((151:ℝ)/100) ≤ Real.cos (t-theta)} := by
    intro t ht
    refine ⟨ht.1,?_⟩
    have hd := (mem_sphere_closedBall_iff (by norm_num : (0:ℝ) ≤ 57/50)
      (circleMap_norm t)).mp ht.2
    have hi : inner ℝ (circleMap t) p = ‖p‖*Real.cos (t-theta) := by
      conv_lhs => rw [self_eq_norm_smul_centerDir hp]
      rw [real_inner_smul_right]
      rw [← circleMap_circleAngle _ (centerDir_norm hp),inner_circleMap]
    rw [hi] at hd
    have hdiv : (1+‖p‖^2-((57:ℝ)/50)^2)/(2*‖p‖) ≤ Real.cos (t-theta) := by
      rw [div_le_iff₀ (by linarith : 0 < 2*‖p‖)]
      linarith
    exact cos_star_bound.le.trans ((star_threshold hn).trans hdiv)
  have hb := (measure_mono hsub).trans (volume_cos_ge_le htheta
    (by norm_num : (0:ℝ) ≤ 151/100) (by linarith [Real.pi_gt_d2] : (151:ℝ)/100 ≤ Real.pi/2))
  exact (ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne hb).trans_eq
    (ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2*(151/100)))

theorem no_five_star_cluster {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (p : Point) (hn : (31:ℝ)/50 ≤ ‖p‖) (s : Finset (Fin 9)) (hs : s.card = 5)
    (hcluster : ∀ i ∈ s, ∀ x : Point, ‖x‖ = 1 →
      dist x (c (ringSite i)) ≤ r → dist x p ≤ (57:ℝ)/50) : False := by
  classical
  let T := {i : Fin 9 // i ∉ s}
  have hcard : Fintype.card T = 4 := by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,hs]
  let e : T ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  let d : Fin 4 → Point := fun j => c (ringSite (e.symm j).val)
  let A := capPreimage p ((57:ℝ)/50)
  let B := ⋃ j : Fin 4, capPreimage (d j) r
  have hcover : Set.Ioo (0:ℝ) (2*Real.pi) ⊆ A ∪ B := by
    intro t ht
    obtain ⟨j,hj⟩ := hc (circleMap t) (mem_unitDisk.mpr (circleMap_norm t).le)
    have hj9 : j.val < 9 := (hR j).mp ⟨circleMap t,circleMap_norm t,hj⟩
    let i : Fin 9 := ⟨j.val,hj9⟩
    by_cases his : i ∈ s
    · exact Or.inl ⟨ht,hcluster i his _ (circleMap_norm t) hj⟩
    · right
      let a : T := ⟨i,his⟩
      apply Set.mem_iUnion.mpr
      refine ⟨e a,ht,?_⟩
      change dist (circleMap t) (c (ringSite (e.symm (e a)).val)) ≤ r
      rw [e.symm_apply_apply]
      exact hj
  have hsub : A ∪ B ⊆ Set.Ioo (0:ℝ) (2*Real.pi) := by
    intro t ht
    rcases ht with ht | ht
    · exact ht.1
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ht
      exact hj.1
  have hfinite : volume (A∪B) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (measure_mono hsub)
  have hB : volume.real B ≤ 4*(2*Real.arcsin r) := by
    have hh := (measureReal_iUnion_fintype_le (fun j => capPreimage (d j) r)).trans
      (Finset.sum_le_sum (fun j _ =>
        volumeReal_capPreimage_le (Covers.nonneg hc) (by linarith : r < 1)))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using hh
  have hA := star_window_volume hn
  have hsum : 2*Real.pi ≤ volume.real A+volume.real B := by
    calc
      2*Real.pi = volume.real (Set.Ioo (0:ℝ) (2*Real.pi)) := by
        rw [Real.volume_real_Ioo_of_le (by positivity),sub_zero]
      _ ≤ volume.real (A∪B) := measureReal_mono hcover hfinite
      _ ≤ volume.real A+volume.real B := measureReal_union_le A B
  have harc := (Real.arcsin_le_arcsin hr.le).trans_lt arcsin_R0_lt_39
  linarith [Real.pi_gt_d2]

theorem no_four_ring_neighbors {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    (i : Fin 9) (s : Finset (Fin 9)) (hs : s.card = 4) (hi : i ∉ s)
    (hmeet : ∀ j ∈ s, ∃ p : Point, dist p (c (ringSite i)) ≤ r ∧
      dist p (c (ringSite j)) ≤ r) : False := by
  have hn : (31:ℝ)/50 ≤ ‖c (ringSite i)‖ := by
    obtain ⟨x,hx,hxi⟩ := hR.ring_meets (i := ringSite i) i.isLt
    have ht := norm_le_norm_add_norm_sub (c (ringSite i)) x
    rw [← dist_eq_norm,hx,dist_comm (c (ringSite i)) x] at ht
    linarith
  apply no_five_star_cluster hc hr hR (c (ringSite i)) hn (insert i s)
    (by rw [Finset.card_insert_of_notMem hi,hs])
  intro j hj x hx hxj
  rcases Finset.mem_insert.mp hj with he | hj
  · subst j
    linarith
  · obtain ⟨p,hpi,hpj⟩ := hmeet j hj
    have hcent := dist_triangle (c (ringSite j)) p (c (ringSite i))
    rw [dist_comm (c (ringSite j)) p] at hcent
    have hdist := dist_triangle x (c (ringSite j)) (c (ringSite i))
    linarith

end N11Formalization.ActualFiveRingStar
#check @N11Formalization.ActualFiveRingStar.no_four_ring_neighbors
#print axioms N11Formalization.ActualFiveRingStar.no_four_ring_neighbors
