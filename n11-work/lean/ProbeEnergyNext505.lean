import N11Formalization

/-! Stage-1 probe for the `next505` energy emission. Run ONLY after the root
build that imports `EnergyTerminalBatchB12Main`; the identical file is the
stale-olean control (it must FAIL when the root import is reverted). -/

namespace ProbeEnergyNext505

-- 1. types of the aggregate, the dispatch and the conditional main consumer
#check @N11Formalization.Paid16GeneralNext505.new_count
#check @N11Formalization.Paid16GeneralNext505.new_radius
#check @N11Formalization.EnergyTerminalBatchB12.paid_count
#check @N11Formalization.EnergyTerminalBatchB12.paid_radius
#check @N11Formalization.EnergyTerminalBatchB12.chart_radius_of_remaining
#check @N11Formalization.EnergyTerminalBatchB12.remaining_of_b12
#check @N11Formalization.EnergyTerminalBatchB12Main.main_of_energy_b12_and_seven_classes

-- 2. per-module axiom sweep (25 emitted packet modules)
#print axioms N11Formalization.Paid16GeneralH01.all_valid
#print axioms N11Formalization.Paid16GeneralH02.all_valid
#print axioms N11Formalization.Paid16GeneralH03.all_valid
#print axioms N11Formalization.Paid16GeneralH04.all_valid
#print axioms N11Formalization.Paid16GeneralH05.all_valid
#print axioms N11Formalization.Paid16GeneralH06.all_valid
#print axioms N11Formalization.Paid16GeneralH07.all_valid
#print axioms N11Formalization.Paid16GeneralH08.all_valid
#print axioms N11Formalization.Paid16GeneralH09.all_valid
#print axioms N11Formalization.Paid16GeneralH10.all_valid
#print axioms N11Formalization.Paid16GeneralH11.all_valid
#print axioms N11Formalization.Paid16GeneralH12.all_valid
#print axioms N11Formalization.Paid16GeneralH13.all_valid
#print axioms N11Formalization.Paid16GeneralH14.all_valid
#print axioms N11Formalization.Paid16GeneralH15.all_valid
#print axioms N11Formalization.Paid16GeneralH16.all_valid
#print axioms N11Formalization.Paid16GeneralH17.all_valid
#print axioms N11Formalization.Paid16GeneralH18.all_valid
#print axioms N11Formalization.Paid16GeneralH19.all_valid
#print axioms N11Formalization.Paid16GeneralH20.all_valid
#print axioms N11Formalization.Paid16GeneralH21.all_valid
#print axioms N11Formalization.Paid16GeneralH22.all_valid
#print axioms N11Formalization.Paid16GeneralH23.all_valid
#print axioms N11Formalization.Paid16GeneralH24.all_valid
#print axioms N11Formalization.Paid16GeneralH25.all_valid

-- 3. aggregate / dispatch / main axiom reports
#print axioms N11Formalization.Paid16GeneralNext505.new_count
#print axioms N11Formalization.Paid16GeneralNext505.new_radius
#print axioms N11Formalization.EnergyTerminalBatchB12.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB12.remaining_of_b12
#print axioms N11Formalization.EnergyTerminalBatchB12Main.main_of_energy_b12_and_seven_classes

-- 4. negative controls: the paid count is EXACT, and `Valid` is not vacuous
example : N11Formalization.EnergyTerminalBatchB12.paidIDs.card = 815 := by
  decide +kernel
example : ¬ (N11Formalization.EnergyTerminalBatchB12.paidIDs.card = 814) := by
  decide +kernel
example : ¬ (N11Formalization.Paid16GeneralNext505.newIDs.card = 504) := by
  decide +kernel
example : ¬ (N11Formalization.EnergyTerminalBatchB11.paidIDs.card =
    N11Formalization.EnergyTerminalBatchB12.paidIDs.card) := by
  decide +kernel
/-- A packet with all weights zero violates `Valid.beta_sum`, so the checker
rejects it: `Valid` is not a vacuous predicate. -/
example : ¬ N11Formalization.Paid16CellCertificate.Valid
    { N11Formalization.Paid16GeneralH01.packet 0 with beta := fun _ => 0 } := by
  intro h
  have hs := h.beta_sum
  simp only [Finset.sum_const_zero] at hs
  norm_num at hs

end ProbeEnergyNext505
