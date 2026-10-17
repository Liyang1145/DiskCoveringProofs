import N11Formalization

/-! Root-imported invalid-data controls. No negative control is a new
Cover counterexample. Mutation leaves the genuine frozen packet unchanged. -/
set_option autoImplicit false
open N11Formalization Finset
set_option maxRecDepth 10000
namespace HarmonicB03Controls
open CertifiedHarmonicField
def original : Packet := HarmonicFieldsB03.packet 4
theorem original_valid : Valid original := HarmonicFieldsB03.all_valid 4
def badMass : Packet := {original with mass := 0}
def badDenominator : Packet := {original with denominator := 0}
def badHarmonicRow : Packet := {original with
  harmonicNumerator := fun v j => if v = 0 then 0 else original.harmonicNumerator v j}
def badGramWeight : Packet := {original with
  weightNumerator := fun k => if k = 0 then original.weightNumerator k + 1
    else original.weightNumerator k}
theorem mass_rejected : ¬Valid badMass := by
  intro h
  have hp := h.mass_pos
  change (0 : ℤ) < 0 at hp
  exact (lt_irrefl 0) hp
theorem denominator_rejected : ¬Valid badDenominator := by
  intro h
  have hp := h.denominator_pos
  change (0 : ℤ) < 0 at hp
  exact (lt_irrefl 0) hp
theorem harmonic_row_rejected : ¬Valid badHarmonicRow := by
  intro h
  have hr := h.harmonic_row (.inl 0)
  change (∑ _j : Fin 9, (0 : ℤ)) = D original at hr
  simp only [sum_const_zero] at hr
  exact original_valid.denominator_pos.ne' hr.symm
theorem gram_weight_rejected : ¬Valid badGramWeight := by
  intro h
  have hb := h.weights 0
  have hg := original_valid.weights 0
  change (∑ e : ResumeNetwork.Edge,
      aZ original e * bZ original e (FlashCosineLeaf284Bridge.iOf 0) *
        bZ original e (FlashCosineLeaf284Bridge.jOf 0)) * wDen original 0 =
      -(wNum original 0 + 1) * A original * D original * D original at hb
  have hz : A original * D original * D original = 0 := by nlinarith only [hb, hg]
  have hp : 0 < A original * D original * D original :=
    mul_pos (mul_pos original_valid.mass_pos original_valid.denominator_pos)
      original_valid.denominator_pos
  exact hp.ne' hz
theorem rounded_overshoot_rejected :
    ¬(Terminal4267Packet.rounded 0 0 + 1 ≤
      2 * CertifiedFieldMixtures.weightQ (HarmonicFieldsB03.packet 0) 0) := by
  decide +kernel
theorem beta_sum_two_rejected :
    (∑ f : Fin 6, (Terminal4267Packet.beta f + (if f = 0 then 1 else 0))) ≠ 1 := by
  decide +kernel
theorem angular_shift_rejected :
    ¬CosineLinePacket.Valid {Terminal4267Packet.packet 0 with shift := 97} := by
  decide +kernel
end HarmonicB03Controls
#print axioms HarmonicB03Controls.mass_rejected
#print axioms HarmonicB03Controls.denominator_rejected
#print axioms HarmonicB03Controls.harmonic_row_rejected
#print axioms HarmonicB03Controls.gram_weight_rejected
#print axioms HarmonicB03Controls.rounded_overshoot_rejected
#print axioms HarmonicB03Controls.beta_sum_two_rejected
#print axioms HarmonicB03Controls.angular_shift_rejected
