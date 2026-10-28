import N11Formalization
set_option autoImplicit false
namespace N11Formalization.C450ThirdRadialControls
open C450RadialPacketKernel
def goodParams : Params := C450ThirdRadialNeg1.params
def good : Packet := C450ThirdRadialNeg1.packet0
theorem good_params_valid : ValidParams goodParams := C450ThirdRadialNeg1.params_valid
theorem good_valid : Valid goodParams good := C450ThirdRadialNeg1.valid0
def badM : Params := {goodParams with M := -1}
def badSum : Params := {goodParams with B := -goodParams.A}
def badT : Packet := {good with qt := 0}
def badB : Packet := {good with qb := -1}
def badLo : Packet := {good with lo := 0}
theorem bad_m_rejected : ¬ValidParams badM := by
  intro hp
  have hh := hp.M_nonneg
  change (0:ℚ) ≤ -1 at hh
  norm_num at hh
theorem bad_sum_rejected : ¬ValidParams badSum := by
  intro hp
  have hh := hp.total_pos
  change (0:ℚ) < goodParams.A + -goodParams.A at hh
  norm_num at hh
theorem bad_t_rejected : ¬Valid goodParams badT := by
  intro hp
  have hh : ¬(cosHiNLag badT.qt ≤ C450FirstRadialKernel.zQ badT.hi) := by decide +kernel
  exact hh hp.t_cos
theorem bad_beta_rejected : ¬Valid goodParams badB := by
  intro hp
  have hh := hp.qb_nonneg
  change (0:ℚ) ≤ -1 at hh
  norm_num at hh
theorem bad_domain_rejected : ¬Valid goodParams badLo := by
  intro hp
  have hh := hp.lower
  change (31/50:ℚ) ≤ 0 at hh
  norm_num at hh

/-! Without the genuine lower-e domain, the signed ell bound is FALSE.
This is an invalid-input control, not a source C450/Covers counterexample. -/
theorem signed_lower_e_needed :
    ¬(‖(!₂[-7/10,0]:Point)‖-((71/10000:ℝ)*(-1/2)+(1/125)^2) ≤
      ‖(!₂[-7/10,0]:Point)-(!₂[0,0]:Point)‖) := by
  have hn : ‖(!₂[-7/10,0]:Point)‖ = (7/10:ℝ) := by
    have hh := norm_sq_coord (!₂[-7/10,0]:Point)
    norm_num at hh
    nlinarith [norm_nonneg (!₂[-7/10,0]:Point)]
  have hz : (!₂[0,0]:Point) = 0 := by
    ext i
    fin_cases i <;> simp
  rw [hz,sub_zero,hn]
  norm_num
end N11Formalization.C450ThirdRadialControls
#print axioms N11Formalization.C450ThirdRadialControls.good_params_valid
#print axioms N11Formalization.C450ThirdRadialControls.good_valid
#print axioms N11Formalization.C450ThirdRadialControls.bad_m_rejected
#print axioms N11Formalization.C450ThirdRadialControls.bad_sum_rejected
#print axioms N11Formalization.C450ThirdRadialControls.bad_t_rejected
#print axioms N11Formalization.C450ThirdRadialControls.bad_beta_rejected
#print axioms N11Formalization.C450ThirdRadialControls.bad_domain_rejected
#print axioms N11Formalization.C450ThirdRadialControls.signed_lower_e_needed
