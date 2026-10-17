import N11Formalization.C450NormalizedInterface

/-! The actual per-disk C450 certificate excludes simultaneous covering of
the two test circles. A whole-disk cover with only one hub is NOT assumed.
This is the stronger consumer needed by the hub-adjacency argument. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualTwoCircleCapacity
open scoped Interval
open MeasureTheory C450NormalizedInterface SourceChartIsometry

theorem direct_capacity_contradiction (W0 W1 : TrigDensity)
    (c : Fin 10 → Point) (h : Point)
    (houter : ∀ theta : ℝ, ∃ i : Fin 10, dist (angPt theta) (c i) ≤ 19/50)
    (hinner : ∀ theta : ℝ, ∃ i : Fin 10,
      dist (h+(19/50:ℝ) • angPt theta) (c i) ≤ 19/50)
    (hper : ∀ i : Fin 10,
      (∫ theta in (0)..(2*Real.pi),
        if dist (angPt theta) (c i) ≤ (19/50:ℝ) then W0.toFun theta else 0) +
      (∫ theta in (0)..(2*Real.pi),
        if dist (h+(19/50:ℝ) • angPt theta) (c i) ≤ (19/50:ℝ)
          then W1.toFun theta else 0) <
        (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10) : False := by
  have ho := circle_integral_le_sum_arc_integrals (γ := angPt) continuous_angPt
    W0.continuous_toFun W0.nonneg_toFun houter
  have hi := circle_integral_le_sum_arc_integrals
    (γ := fun theta : ℝ => h+(19/50:ℝ) • angPt theta)
    (continuous_const.add (continuous_angPt.const_smul (19/50:ℝ)))
    W1.continuous_toFun W1.nonneg_toFun hinner
  rw [W0.integral_toFun] at ho
  rw [W1.integral_toFun] at hi
  have hsum := Finset.sum_lt_sum_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 10)).Nonempty)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 10))) => hper i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  norm_num only [Nat.cast_ofNat, mul_div_cancel₀] at hsum
  linarith

theorem normalized_two_circles_impossible (hs : SourceObligation)
    (c : Fin 10 → Point) (e : ℝ) (he0 : 0 ≤ e) (he7 : e ≤ 7/50)
    (hnorm : ∀ i : Fin 10, 1-19/50 ≤ ‖c i‖ ∧ ‖c i‖ ≤ 1+19/50)
    (houter : ∀ theta : ℝ, ∃ i : Fin 10, dist (angPt theta) (c i) ≤ 19/50)
    (hinner : ∀ theta : ℝ, ∃ i : Fin 10,
      dist (hubPt e+(19/50:ℝ) • angPt theta) (c i) ≤ 19/50) : False := by
  let cert := source_certificate hs
  have hehiQ : e ≤ (↑(7/50:ℚ):ℝ) := by norm_num; exact he7
  obtain ⟨s, hmem, hlo, hhi⟩ := exists_seg_of_chain cert.segs 0 (7/50)
    cert.chain cert.segs_ne_nil e (by simpa only [Rat.cast_zero] using he0) hehiQ
  obtain ⟨h0,h1⟩ := cert.nonneg s hmem
  have hbound := cert.bound s hmem h0 h1
  exact direct_capacity_contradiction (s.W0 h0) (s.W1 h1) c (hubPt e) houter hinner
    (fun i => hbound (c i) e (hnorm i).1 (hnorm i).2 he0 hlo hhi)

/-- The hub direction is paid by a real common isometry.
Fixed source densities are never applied to an arbitrary unnormalized hub. -/
theorem two_circles_impossible (hs : SourceObligation)
    (c : Fin 10 → Point) (h : Point) (he : ‖h‖ ≤ 7/50)
    (hnorm : ∀ i : Fin 10, 1-19/50 ≤ ‖c i‖ ∧ ‖c i‖ ≤ 1+19/50)
    (houter : ∀ x : Point, ‖x‖ = 1 → ∃ i : Fin 10, dist x (c i) ≤ 19/50)
    (hinner : ∀ x : Point, dist x h = (19/50:ℝ) →
      ∃ i : Fin 10, dist x (c i) ≤ 19/50) : False := by
  obtain ⟨a,ha⟩ := exists_hub_rotation h
  let d : Fin 10 → Point := fun i => rotate a (c i)
  have hd (i : Fin 10) : 1-19/50 ≤ ‖d i‖ ∧ ‖d i‖ ≤ 1+19/50 := by
    change 1-19/50 ≤ ‖rotate a (c i)‖ ∧ ‖rotate a (c i)‖ ≤ 1+19/50
    rw [rotate_norm]
    exact hnorm i
  apply normalized_two_circles_impossible hs d ‖h‖ (norm_nonneg h) he hd
  · intro theta
    obtain ⟨i,hi⟩ := houter (rotate (-a) (angPt theta))
      (by rw [rotate_norm, norm_angPt])
    refine ⟨i, ?_⟩
    change dist (angPt theta) (rotate a (c i)) ≤ 19/50
    rw [inverse_dist]
    exact hi
  · intro theta
    let z : Point := hubPt ‖h‖+(19/50:ℝ) • angPt theta
    have hz : dist z (hubPt ‖h‖) = (19/50:ℝ) := by
      change dist (hubPt ‖h‖+(19/50:ℝ) • angPt theta) (hubPt ‖h‖) = (19/50:ℝ)
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_angPt,
        mul_one, Real.norm_eq_abs]
      norm_num
    have hx : dist (rotate (-a) z) h = (19/50:ℝ) := by
      rw [← inverse_dist, ha]
      exact hz
    obtain ⟨i,hi⟩ := hinner (rotate (-a) z) hx
    refine ⟨i, ?_⟩
    change dist z (rotate a (c i)) ≤ 19/50
    rw [inverse_dist]
    exact hi

end N11Formalization.ActualTwoCircleCapacity
#check @N11Formalization.ActualTwoCircleCapacity.two_circles_impossible
#print axioms N11Formalization.ActualTwoCircleCapacity.direct_capacity_contradiction
#print axioms N11Formalization.ActualTwoCircleCapacity.two_circles_impossible
