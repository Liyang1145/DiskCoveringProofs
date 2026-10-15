import N11Formalization.ActualVoronoiCells

/-! The core-to-small-hub implication with the ACTUAL cover radius.
No geometric support inequality, closure or farthest-point input is assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubCoreSupport
open ActualVoronoiCells DSHTopologyInterior

theorem closedBall_support {p : Point} {a r : ℝ} (ha : 0 ≤ a)
    (hsub : Metric.closedBall (0 : Point) a ⊆ Metric.closedBall p r) :
    ‖p‖ + a ≤ r := by
  by_cases hp : p = 0
  · have hx : a • angPt 0 ∈ Metric.closedBall (0 : Point) a := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_angPt,
        mul_one, Real.norm_eq_abs, abs_of_nonneg ha]
    have hd := Metric.mem_closedBall.mp (hsub hx)
    rw [hp, dist_zero_right, norm_smul, norm_angPt, mul_one,
      Real.norm_eq_abs, abs_of_nonneg ha] at hd
    simpa only [hp, norm_zero, zero_add] using hd
  · have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp
    let u : Point := ‖p‖⁻¹ • p
    have hu : ‖u‖ = 1 := by
      change ‖‖p‖⁻¹ • p‖ = 1
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hn,
        inv_mul_cancel₀ hn.ne']
    have hpu : p = ‖p‖ • u := by
      change p = ‖p‖ • (‖p‖⁻¹ • p)
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hx : (-a) • u ∈ Metric.closedBall (0 : Point) a := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hu, mul_one,
        Real.norm_eq_abs, abs_neg, abs_of_nonneg ha]
    have hsubpoint : (-a) • u - p = (-(a + ‖p‖)) • u := by
      calc
        (-a) • u - p = (-a) • u - ‖p‖ • u :=
          congrArg (fun q : Point => (-a) • u - q) hpu
        _ = (-a - ‖p‖) • u := (sub_smul _ _ _).symm
        _ = (-(a + ‖p‖)) • u := by congr 1; ring
    have hd := Metric.mem_closedBall.mp (hsub hx)
    rw [dist_eq_norm, hsubpoint, norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg (add_nonneg ha hn.le)] at hd
    linarith

theorem openBall_support {p : Point} {a r : ℝ} (ha : 0 < a)
    (hsub : Metric.ball (0 : Point) a ⊆ Metric.closedBall p r) :
    ‖p‖ + a ≤ r := by
  apply closedBall_support ha.le
  rw [← closure_ball (0 : Point) ha.ne']
  exact closure_minimal hsub Metric.isClosed_closedBall

theorem core_containment_offset {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hR : RingLabels c r) (hr : r < 1/2)
    {j : Fin 11} (hj : 9 ≤ j.val) (hcenter : ‖c j‖ < 1)
    (hcore : Metric.ball (0 : Point) (1-2*r) ⊆ Cell c j) :
    ‖c j‖ ≤ 3*r-1 := by
  have hsub := hcore.trans (hub_cell_radius hc hR hj hcenter)
  have hsupport := openBall_support (by linarith : 0 < 1-2*r) hsub
  linarith

theorem disjoint_core_small_hub (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r ≤ 19/50) (hR : RingLabels c r)
    (hdis : Metric.ball (0 : Point) (1-2*r) ∩ (Cell c 9 ∩ Cell c 10) = ∅) :
    ∃ j : Fin 11, 9 ≤ j.val ∧
      Metric.ball (0 : Point) (1-2*r) ⊆ Cell c j ∧
      ‖c j‖ ≤ 3*r-1 ∧ ‖c j‖ ≤ 7/50 := by
  have hcent (j : Fin 11) (hj : 9 ≤ j.val) : ‖c j‖ < 1 := by
    have hh := ActualHubEssentiality.hub_strict_margin_of_atom h450 hr hc hR hj
    linarith [Covers.nonneg hc]
  rcases disjoint_core_one_hub hc hR hdis with h9 | h10
  · have hoff := core_containment_offset hc hR (by linarith) (by decide) (hcent 9 (by decide)) h9
    exact ⟨9, by decide, h9, hoff, by linarith⟩
  · have hoff := core_containment_offset hc hR (by linarith) (by decide) (hcent 10 (by decide)) h10
    exact ⟨10, by decide, h10, hoff, by linarith⟩

end N11Formalization.ActualHubCoreSupport
#check @N11Formalization.ActualHubCoreSupport.closedBall_support
#check @N11Formalization.ActualHubCoreSupport.disjoint_core_small_hub
#print axioms N11Formalization.ActualHubCoreSupport.closedBall_support
#print axioms N11Formalization.ActualHubCoreSupport.disjoint_core_small_hub
