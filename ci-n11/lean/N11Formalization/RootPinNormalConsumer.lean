import N11Formalization.PinTangentGeometry
import N11Formalization.RootFanBranchConsumer
import N11Formalization.SourceWidthNondegenerate
import N11Formalization.Assembly.G2Unified
set_option autoImplicit false
namespace N11Formalization.RootPinNormalConsumer
open N11Formalization PinTangentGeometry PinBranchBind
noncomputable section

private theorem chord_read_1 : (1/10 : ℚ) ≤
    (ndRingBox ndBox 2 0).lo - (ndRingBox ndBox 1 0).hi := by nd_eval
private theorem chord_read_2 : (1/10 : ℚ) ≤
    (ndRingBox ndBox 3 0).lo - (ndRingBox ndBox 2 0).hi := by nd_eval
private theorem chord_read_3 : (1/10 : ℚ) ≤
    (ndRingBox ndBox 4 0).lo - (ndRingBox ndBox 3 0).hi := by nd_eval
private theorem chord_read_8 : (1/10 : ℚ) ≤
    (ndRingBox ndBox 8 1).lo - (ndRingBox ndBox 0 1).hi := by nd_eval

theorem source_contact_chord_ne (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ringCenter SourceExactRoot.sourceRoot k ≠ ringCenter SourceExactRoot.sourceRoot (k+1) := by
  have hb := ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball
  rcases hk with rfl | rfl | rfl | rfl
  · rw [nd_fin_succ_1]
    exact point_ne_of_coord (i := 0) (a := 1/10) (by norm_num)
      (le_abs_sub_of_lo_sub_hi' (ndRingBox_mem hb 1 0) (ndRingBox_mem hb 2 0)
        (by norm_num) chord_read_1)
  · rw [nd_fin_succ_2]
    exact point_ne_of_coord (i := 0) (a := 1/10) (by norm_num)
      (le_abs_sub_of_lo_sub_hi' (ndRingBox_mem hb 2 0) (ndRingBox_mem hb 3 0)
        (by norm_num) chord_read_2)
  · rw [nd_fin_succ_3]
    exact point_ne_of_coord (i := 0) (a := 1/10) (by norm_num)
      (le_abs_sub_of_lo_sub_hi' (ndRingBox_mem hb 3 0) (ndRingBox_mem hb 4 0)
        (by norm_num) chord_read_3)
  · rw [nd_fin_succ_8]
    exact point_ne_of_coord (i := 1) (a := 1/10) (by norm_num)
      (le_abs_sub_of_lo_sub_hi (ndRingBox_mem hb 8 1) (ndRingBox_mem hb 0 1)
        (by norm_num) chord_read_8)

theorem source_contact_equidistant (k : Fin 9) :
    ‖Uvec SourceExactRoot.sourceRoot k - ringCenter SourceExactRoot.sourceRoot k‖ =
      ‖Uvec SourceExactRoot.sourceRoot k - ringCenter SourceExactRoot.sourceRoot (k+1)‖ := by
  have hs : ∀ j : Fin 9, Real.sin (angleVec SourceExactRoot.sourceRoot j)^2 ≤
      (SourceExactRoot.sourceRoot 6)^2 := by
    intro j
    linarith [SourceWidthNondegenerate.source_radicand_pos j]
  have hr : 0 ≤ SourceExactRoot.sourceRoot 6 := le_of_lt SourceExactRoot.sourceRadius_pos
  have h1 := dist_Uvec_ringCenter_self SourceExactRoot.sourceRoot hs hr k
  have h2 := dist_Uvec_ringCenter_succ SourceExactRoot.sourceRoot hs hr k
  rw [dist_eq_norm] at h1 h2
  exact h1.trans h2.symm

theorem source_contact_height (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    0 < pinHeight (ringCenter SourceExactRoot.sourceRoot k)
      (ringCenter SourceExactRoot.sourceRoot (k+1)) (Uvec SourceExactRoot.sourceRoot k) := by
  rcases hk with rfl | rfl | rfl | rfl
  · rw [nd_fin_succ_1]; exact RootFanBranchConsumer.contact_y_pos_1.2
  · rw [nd_fin_succ_2]; exact RootFanBranchConsumer.contact_y_pos_2.2
  · rw [nd_fin_succ_3]; exact RootFanBranchConsumer.contact_y_pos_3.2
  · rw [nd_fin_succ_8]; exact RootFanBranchConsumer.contact_y_pos_8.2

/-- Actual-root normal rank, including the wrapping 8-to-0 contact. No rank premise remains. -/
theorem source_contact_normals_independent (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    det (Uvec SourceExactRoot.sourceRoot k - ringCenter SourceExactRoot.sourceRoot k)
      (Uvec SourceExactRoot.sourceRoot k - ringCenter SourceExactRoot.sourceRoot (k+1)) ≠ 0 :=
  pin_normals_independent (source_contact_chord_ne k hk)
    (source_contact_equidistant k) (source_contact_height k hk)

end
end N11Formalization.RootPinNormalConsumer
#check @N11Formalization.RootPinNormalConsumer.source_contact_normals_independent
#print axioms N11Formalization.RootPinNormalConsumer.source_contact_normals_independent
