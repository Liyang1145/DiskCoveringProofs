import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthControls
open C450GroupedPacketKernel C450EighthData C450EighthSegment

def first : Packet := C450EighthGroupedC01.packet0
theorem negative_width_rejected : ¬ Valid eighth {first with qt := -1} := by
  intro h
  have hn := h.qt_nonneg
  norm_num at hn
theorem missing_scalar_upper_rejected : ¬ Valid eighth {first with p0 := 3} := by
  intro h
  have hn := h.scalar0
  norm_num [eighth] at hn
theorem invalid_norm_lower_rejected : ¬ Valid eighth {first with lo := 0} := by
  intro h
  have hn := h.lower
  norm_num at hn
theorem invalid_offset_upper_rejected : ¬ Valid {eighth with eHi := 1} first := by
  intro h
  have hn := h.e_upper
  norm_num at hn
theorem false_amplitude_rejected : ¬ Valid eighth {first with p0 := -1} := by
  intro h
  have hn := h.amplitude0
  have hh : ¬ (C450GroupedAmplitude.amplitudeInterval eighth.a1 eighth.a2 eighth.a3
      first.Z first.V).hi ≤ (-1:ℚ) := by decide +kernel
  exact hh hn
theorem original_capacity_not_amplitude :
    eighth.a0+eighth.b0 ≠ first.p0+first.p1 := by decide +kernel
theorem radial_gap_control :
    ¬ ∃ i : Fin 2, RatInterval.Mem (![⟨0,1⟩,⟨2,3⟩] i) (3/2:ℝ) := by
  rintro ⟨i,hi⟩
  fin_cases i <;> norm_num [RatInterval.Mem,RatInterval.toSet] at hi
theorem omitted_direction_endpoint_control :
    ¬ RatInterval.Mem (⟨-15/16,1⟩ : RatInterval) (-1:ℝ) := by
  norm_num [RatInterval.Mem,RatInterval.toSet]
end N11Formalization.C450EighthControls
#print axioms N11Formalization.C450EighthControls.negative_width_rejected
#print axioms N11Formalization.C450EighthControls.missing_scalar_upper_rejected
#print axioms N11Formalization.C450EighthControls.invalid_norm_lower_rejected
#print axioms N11Formalization.C450EighthControls.invalid_offset_upper_rejected
#print axioms N11Formalization.C450EighthControls.false_amplitude_rejected
#print axioms N11Formalization.C450EighthControls.original_capacity_not_amplitude
#print axioms N11Formalization.C450EighthControls.radial_gap_control
#print axioms N11Formalization.C450EighthControls.omitted_direction_endpoint_control
