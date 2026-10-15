import Mathlib
import N11Formalization.FanFoutPos
import N11Formalization.FanBranchClosure
import N11Formalization.SourceExactRoot
set_option autoImplicit false
namespace N11Formalization.RootFanBranchConsumer
open N11Formalization
open N11Formalization.FanBranchClosure
open N11Formalization.PinBranchBind
noncomputable section

private theorem residual_zero (k : Fin 5) :
    residual SourceExactRoot.sourceRoot k = 0 := by
  have h := congrFun SourceExactRoot.sourceRoot_mem.2
    (⟨(k : ℕ), by omega⟩ : Fin 12)
  simpa [TCSystem] using h

theorem contact_dist_1 :
    dist (hub1 SourceExactRoot.sourceRoot) (Uvec SourceExactRoot.sourceRoot 1)
      = SourceExactRoot.sourceRoot 6 := by
  rw [dist_comm]
  have h := residual_zero 0
  simp [residual] at h
  exact sub_eq_zero.mp h

theorem contact_dist_2 :
    dist (hub0 SourceExactRoot.sourceRoot) (Uvec SourceExactRoot.sourceRoot 2)
      = SourceExactRoot.sourceRoot 6 := by
  rw [dist_comm]
  have h := residual_zero 1
  simp [residual] at h
  exact sub_eq_zero.mp h

theorem contact_dist_3 :
    dist (hub0 SourceExactRoot.sourceRoot) (Uvec SourceExactRoot.sourceRoot 3)
      = SourceExactRoot.sourceRoot 6 := by
  rw [dist_comm]
  have h := residual_zero 2
  simp [residual] at h
  exact sub_eq_zero.mp h

theorem contact_dist_8 :
    dist (hub1 SourceExactRoot.sourceRoot) (Uvec SourceExactRoot.sourceRoot 8)
      = SourceExactRoot.sourceRoot 6 := by
  rw [dist_comm]
  have h := residual_zero 3
  simp [residual] at h
  exact sub_eq_zero.mp h

/-- At each of the four source fan contacts (including the cyclic 8-to-0 contact),
strict outer residual forces the signed pin coordinate and height to be positive.  This is a genuine consumer of the source root,
not an assumption of the branch argument. -/
theorem contact_y_pos_1 :
    0 < hubCoord (ringCenter SourceExactRoot.sourceRoot 1)
        (ringCenter SourceExactRoot.sourceRoot 2) (Uvec SourceExactRoot.sourceRoot 1)
        (hub1 SourceExactRoot.sourceRoot) ∧
    0 < pinHeight (ringCenter SourceExactRoot.sourceRoot 1)
        (ringCenter SourceExactRoot.sourceRoot 2) (Uvec SourceExactRoot.sourceRoot 1) := by
  have hf := FanFoutPos.fan_Fout_pos_root 1 (Hub := hub1 SourceExactRoot.sourceRoot) (Or.inr rfl)
  have he := fan_Fout_eq_four_yh SourceExactRoot.sourceRoot 1 (hub1 SourceExactRoot.sourceRoot)
      contact_dist_1
  have hh : 0 ≤ pinHeight (ringCenter SourceExactRoot.sourceRoot 1)
      (ringCenter SourceExactRoot.sourceRoot 2) (Uvec SourceExactRoot.sourceRoot 1) :=
    norm_nonneg _
  have hidx : (1 : Fin 9) + 1 = 2 := by decide
  rw [hidx] at he
  rw [he] at hf
  have hne : pinHeight (ringCenter SourceExactRoot.sourceRoot 1)
      (ringCenter SourceExactRoot.sourceRoot 2) (Uvec SourceExactRoot.sourceRoot 1) ≠ 0 := by
    intro hz
    rw [hz] at hf
    norm_num at hf
  have hp : 0 < pinHeight (ringCenter SourceExactRoot.sourceRoot 1)
      (ringCenter SourceExactRoot.sourceRoot 2) (Uvec SourceExactRoot.sourceRoot 1) :=
    lt_of_le_of_ne hh (Ne.symm hne)
  constructor
  · have hy4 := pos_of_mul_pos_left hf (le_of_lt hp)
    exact pos_of_mul_pos_right hy4 (by norm_num : (0 : ℝ) ≤ 4)
  · exact hp

theorem contact_y_pos_2 :
    0 < hubCoord (ringCenter SourceExactRoot.sourceRoot 2)
        (ringCenter SourceExactRoot.sourceRoot 3) (Uvec SourceExactRoot.sourceRoot 2)
        (hub0 SourceExactRoot.sourceRoot) ∧
    0 < pinHeight (ringCenter SourceExactRoot.sourceRoot 2)
        (ringCenter SourceExactRoot.sourceRoot 3) (Uvec SourceExactRoot.sourceRoot 2) := by
  have hf := FanFoutPos.fan_Fout_pos_root 2 (Hub := hub0 SourceExactRoot.sourceRoot) (Or.inl rfl)
  have he := fan_Fout_eq_four_yh SourceExactRoot.sourceRoot 2 (hub0 SourceExactRoot.sourceRoot)
      contact_dist_2
  have hh : 0 ≤ pinHeight (ringCenter SourceExactRoot.sourceRoot 2)
      (ringCenter SourceExactRoot.sourceRoot 3) (Uvec SourceExactRoot.sourceRoot 2) :=
    norm_nonneg _
  have hidx : (2 : Fin 9) + 1 = 3 := by decide
  rw [hidx] at he
  rw [he] at hf
  have hne : pinHeight (ringCenter SourceExactRoot.sourceRoot 2)
      (ringCenter SourceExactRoot.sourceRoot 3) (Uvec SourceExactRoot.sourceRoot 2) ≠ 0 := by
    intro hz
    rw [hz] at hf
    norm_num at hf
  have hp : 0 < pinHeight (ringCenter SourceExactRoot.sourceRoot 2)
      (ringCenter SourceExactRoot.sourceRoot 3) (Uvec SourceExactRoot.sourceRoot 2) :=
    lt_of_le_of_ne hh (Ne.symm hne)
  constructor
  · have hy4 := pos_of_mul_pos_left hf (le_of_lt hp)
    exact pos_of_mul_pos_right hy4 (by norm_num : (0 : ℝ) ≤ 4)
  · exact hp

theorem contact_y_pos_3 :
    0 < hubCoord (ringCenter SourceExactRoot.sourceRoot 3)
        (ringCenter SourceExactRoot.sourceRoot 4) (Uvec SourceExactRoot.sourceRoot 3)
        (hub0 SourceExactRoot.sourceRoot) ∧
    0 < pinHeight (ringCenter SourceExactRoot.sourceRoot 3)
        (ringCenter SourceExactRoot.sourceRoot 4) (Uvec SourceExactRoot.sourceRoot 3) := by
  have hf := FanFoutPos.fan_Fout_pos_root 3 (Hub := hub0 SourceExactRoot.sourceRoot) (Or.inl rfl)
  have he := fan_Fout_eq_four_yh SourceExactRoot.sourceRoot 3 (hub0 SourceExactRoot.sourceRoot)
      contact_dist_3
  have hh : 0 ≤ pinHeight (ringCenter SourceExactRoot.sourceRoot 3)
      (ringCenter SourceExactRoot.sourceRoot 4) (Uvec SourceExactRoot.sourceRoot 3) :=
    norm_nonneg _
  have hidx : (3 : Fin 9) + 1 = 4 := by decide
  rw [hidx] at he
  rw [he] at hf
  have hne : pinHeight (ringCenter SourceExactRoot.sourceRoot 3)
      (ringCenter SourceExactRoot.sourceRoot 4) (Uvec SourceExactRoot.sourceRoot 3) ≠ 0 := by
    intro hz
    rw [hz] at hf
    norm_num at hf
  have hp : 0 < pinHeight (ringCenter SourceExactRoot.sourceRoot 3)
      (ringCenter SourceExactRoot.sourceRoot 4) (Uvec SourceExactRoot.sourceRoot 3) :=
    lt_of_le_of_ne hh (Ne.symm hne)
  constructor
  · have hy4 := pos_of_mul_pos_left hf (le_of_lt hp)
    exact pos_of_mul_pos_right hy4 (by norm_num : (0 : ℝ) ≤ 4)
  · exact hp

theorem contact_y_pos_8 :
    0 < hubCoord (ringCenter SourceExactRoot.sourceRoot 8)
        (ringCenter SourceExactRoot.sourceRoot 0) (Uvec SourceExactRoot.sourceRoot 8)
        (hub1 SourceExactRoot.sourceRoot) ∧
    0 < pinHeight (ringCenter SourceExactRoot.sourceRoot 8)
        (ringCenter SourceExactRoot.sourceRoot 0) (Uvec SourceExactRoot.sourceRoot 8) := by
  have hf := FanFoutPos.fan_Fout_pos_root 8 (Hub := hub1 SourceExactRoot.sourceRoot) (Or.inr rfl)
  have he := fan_Fout_eq_four_yh SourceExactRoot.sourceRoot 8 (hub1 SourceExactRoot.sourceRoot)
      contact_dist_8
  have hh : 0 ≤ pinHeight (ringCenter SourceExactRoot.sourceRoot 8)
      (ringCenter SourceExactRoot.sourceRoot 0) (Uvec SourceExactRoot.sourceRoot 8) :=
    norm_nonneg _
  have hidx : (8 : Fin 9) + 1 = 0 := by decide
  rw [hidx] at he
  rw [he] at hf
  have hne : pinHeight (ringCenter SourceExactRoot.sourceRoot 8)
      (ringCenter SourceExactRoot.sourceRoot 0) (Uvec SourceExactRoot.sourceRoot 8) ≠ 0 := by
    intro hz
    rw [hz] at hf
    norm_num at hf
  have hp : 0 < pinHeight (ringCenter SourceExactRoot.sourceRoot 8)
      (ringCenter SourceExactRoot.sourceRoot 0) (Uvec SourceExactRoot.sourceRoot 8) :=
    lt_of_le_of_ne hh (Ne.symm hne)
  constructor
  · have hy4 := pos_of_mul_pos_left hf (le_of_lt hp)
    exact pos_of_mul_pos_right hy4 (by norm_num : (0 : ℝ) ≤ 4)
  · exact hp

end
end N11Formalization.RootFanBranchConsumer
#print axioms N11Formalization.RootFanBranchConsumer.contact_y_pos_1
#print axioms N11Formalization.RootFanBranchConsumer.contact_y_pos_8
