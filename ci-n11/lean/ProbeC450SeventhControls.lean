import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhControls
open C450GroupedPacketKernel C450SeventhData C450SeventhSegment

def first : Packet := C450SeventhGroupedC01.packet0
theorem negative_width_rejected : ¬ Valid seventh {first with qt := -1} := by
  intro h
  have hn := h.qt_nonneg
  norm_num at hn
theorem missing_scalar_upper_rejected : ¬ Valid seventh {first with p0 := 3} := by
  intro h
  have hn := h.scalar0
  norm_num [seventh] at hn
theorem invalid_norm_lower_rejected : ¬ Valid seventh {first with lo := 0} := by
  intro h
  have hn := h.lower
  norm_num at hn
theorem invalid_offset_upper_rejected : ¬ Valid {seventh with eHi := 1} first := by
  intro h
  have hn := h.e_upper
  norm_num at hn
theorem false_amplitude_rejected : ¬ Valid seventh {first with p0 := -1} := by
  intro h
  have hn := h.amplitude0
  have hh : ¬ (C450GroupedAmplitude.amplitudeInterval seventh.a1 seventh.a2 seventh.a3
      first.Z first.V).hi ≤ (-1:ℚ) := by decide +kernel
  exact hh hn
theorem original_capacity_not_amplitude :
    seventh.a0+seventh.b0 ≠ first.p0+first.p1 := by decide +kernel
theorem radial_gap_control :
    ¬ ∃ i : Fin 2, RatInterval.Mem (![⟨0,1⟩,⟨2,3⟩] i) (3/2:ℝ) := by
  rintro ⟨i,hi⟩
  fin_cases i <;> norm_num [RatInterval.Mem,RatInterval.toSet] at hi
theorem omitted_direction_endpoint_control :
    ¬ RatInterval.Mem (⟨-15/16,1⟩ : RatInterval) (-1:ℝ) := by
  norm_num [RatInterval.Mem,RatInterval.toSet]
end N11Formalization.C450SeventhControls
#print axioms N11Formalization.C450SeventhControls.negative_width_rejected
#print axioms N11Formalization.C450SeventhControls.missing_scalar_upper_rejected
#print axioms N11Formalization.C450SeventhControls.invalid_norm_lower_rejected
#print axioms N11Formalization.C450SeventhControls.invalid_offset_upper_rejected
#print axioms N11Formalization.C450SeventhControls.false_amplitude_rejected
#print axioms N11Formalization.C450SeventhControls.original_capacity_not_amplitude
#print axioms N11Formalization.C450SeventhControls.radial_gap_control
#print axioms N11Formalization.C450SeventhControls.omitted_direction_endpoint_control
