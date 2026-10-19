import Class33Core.Rep7
import Class33Core.Rep1
import Class33Core.Q0M2
/- Negative controls + axiom audit for the class33 core-Lean pre-validation. -/
namespace Class33Core.Audit
open Class33Core
/-- Control: flipping one interior face mask breaks the transcribed balance check. -/
def badMask : Table := { Rep7.table with faceMask := fun f s => if f = [1,8,9] ∧ s = 0 then -1 else Rep7.table.faceMask f s }
theorem badMask_unbalanced : badMask.balancedB = false := by decide +kernel
/-- Control: wrong cut is detected by the graph check. -/
theorem wrong_cut_rejected : sameFacesB 6 4 Rep7.faces = false := by decide +kernel
theorem wrong_cut_rejected' : sameFacesB 7 4 Rep1.faces = false := by decide +kernel
theorem q0_wrong_m_rejected : sameFacesQ0B 3 Q0M2.faces = false := by decide +kernel
/-- Control: the batch tuple does NOT match the unshifted index (shift j = K-1 is load-bearing). -/
theorem unshifted_mismatch : Rep7.table.switchQ 0 ≠ (21538627/125000000 : Rat) := by decide +kernel
/-- Control: strict total fails if switch maxima are inflated by 1/100 each. -/
theorem strict_sensitive : ¬ (Rep1.table.totalUpper sharpAlpha Rep1.faceMaxP
    (Rep1.switchMaxP.map (· + 1/100)) Rep1.sectorMaxP < piLo) := by decide +kernel
end Class33Core.Audit
#print axioms Class33Core.Rep7.faces_eq_lean
#print axioms Class33Core.Rep7.edges_ok
#print axioms Class33Core.Rep7.balanced
#print axioms Class33Core.Rep7.kap_nonneg
#print axioms Class33Core.Rep7.eta_nonneg
#print axioms Class33Core.Rep7.sharp_value
#print axioms Class33Core.Rep7.strict_with_proposed
#print axioms Class33Core.Rep7.batch0_is_switch8
#print axioms Class33Core.Rep7.batch4_is_switch3
#print axioms Class33Core.Rep7.batch5_is_switch4
#print axioms Class33Core.Rep7.batch8_is_switch7
#print axioms Class33Core.Rep7.switch_aggregate
#print axioms Class33Core.Rep7.switchMax_are_batch_bounds
#print axioms Class33Core.Rep7.face189_is_face1_reversed
#print axioms Class33Core.Rep1.faces_eq_lean
#print axioms Class33Core.Rep1.edges_ok
#print axioms Class33Core.Rep1.balanced
#print axioms Class33Core.Rep1.kap_nonneg
#print axioms Class33Core.Rep1.eta_nonneg
#print axioms Class33Core.Rep1.sharp_value
#print axioms Class33Core.Rep1.strict_with_proposed
#print axioms Class33Core.Q0M2.faces_eq_lean
#print axioms Class33Core.Q0M2.edges_ok
#print axioms Class33Core.Q0M2.balanced
#print axioms Class33Core.Q0M2.kap_nonneg
#print axioms Class33Core.Q0M2.eta_nonneg
#print axioms Class33Core.Q0M2.sharp_value
#print axioms Class33Core.Q0M2.strict_with_proposed
#print axioms Class33Core.Audit.q0_wrong_m_rejected
#print axioms Class33Core.Audit.badMask_unbalanced
#print axioms Class33Core.Audit.wrong_cut_rejected
#print axioms Class33Core.Audit.wrong_cut_rejected'
#print axioms Class33Core.Audit.unshifted_mismatch
#print axioms Class33Core.Audit.strict_sensitive
