import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubEssentialityControls
open ActualHubEssentiality

theorem tangent_not_strict :
    ¬ (‖((3:ℝ)/4) • angPt 0‖ + (1:ℝ)/4 < 1) := tangent_margin_control

theorem disjoint_circle_without_initial_point_insufficient :
    (∀ x : Point, dist x ((2:ℝ) • angPt 0) ≤ (1:ℝ)/4 → ‖x‖ ≠ 1) ∧
      ¬ (‖(2:ℝ) • angPt 0‖ + (1:ℝ)/4 < 1) := outside_no_circle_control

theorem coincident_private_rejected {c : Fin 11 → Point} {r : ℝ} {j k : Fin 11}
    (hjk : j ≠ k) (heq : c j = c k) : ¬ PrivatePoint c r j :=
  fun hp => private_point_ne hp hjk heq

theorem zero_centre_calibration {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖(0 : Point)‖ + r < 1 := by
  apply closed_ball_strict_margin hr
  · refine ⟨0, by simp, ?_⟩
    simpa only [dist_self] using hr
  · intro y hy hn
    rw [dist_zero_right, hn] at hy
    linarith

end N11Formalization.ActualHubEssentialityControls
#print axioms N11Formalization.ActualHubEssentialityControls.tangent_not_strict
#print axioms N11Formalization.ActualHubEssentialityControls.disjoint_circle_without_initial_point_insufficient
#print axioms N11Formalization.ActualHubEssentialityControls.coincident_private_rejected
#print axioms N11Formalization.ActualHubEssentialityControls.zero_centre_calibration
