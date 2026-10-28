import N11Formalization

/-! Stage-2 probe for the `rest1182` energy emission (H26..H82). Byte-identical
file is reused as the stale-olean control: it must FAIL when the root import of
`EnergyTerminalBatchB13Main` is reverted and the root is rebuilt. -/

namespace ProbeEnergyRest1182

-- 1. aggregate / dispatch / main types
#check @N11Formalization.Paid16GeneralNext1182.new_count
#check @N11Formalization.Paid16GeneralNext1182.new_radius
#check @N11Formalization.EnergyTerminalBatchB13.paid_count
#check @N11Formalization.EnergyTerminalBatchB13.paid_radius
#check @N11Formalization.EnergyTerminalBatchB13.chart_radius_of_remaining
#check @N11Formalization.EnergyTerminalBatchB13.remaining_of
#check @N11Formalization.EnergyTerminalBatchB13Main.main_of_energy_and_seven_classes

-- 2. per-module axiom sweep (57 emitted packet modules)
#print axioms N11Formalization.Paid16GeneralH26.all_valid
#print axioms N11Formalization.Paid16GeneralH27.all_valid
#print axioms N11Formalization.Paid16GeneralH28.all_valid
#print axioms N11Formalization.Paid16GeneralH29.all_valid
#print axioms N11Formalization.Paid16GeneralH30.all_valid
#print axioms N11Formalization.Paid16GeneralH31.all_valid
#print axioms N11Formalization.Paid16GeneralH32.all_valid
#print axioms N11Formalization.Paid16GeneralH33.all_valid
#print axioms N11Formalization.Paid16GeneralH34.all_valid
#print axioms N11Formalization.Paid16GeneralH35.all_valid
#print axioms N11Formalization.Paid16GeneralH36.all_valid
#print axioms N11Formalization.Paid16GeneralH37.all_valid
#print axioms N11Formalization.Paid16GeneralH38.all_valid
#print axioms N11Formalization.Paid16GeneralH39.all_valid
#print axioms N11Formalization.Paid16GeneralH40.all_valid
#print axioms N11Formalization.Paid16GeneralH41.all_valid
#print axioms N11Formalization.Paid16GeneralH42.all_valid
#print axioms N11Formalization.Paid16GeneralH43.all_valid
#print axioms N11Formalization.Paid16GeneralH44.all_valid
#print axioms N11Formalization.Paid16GeneralH45.all_valid
#print axioms N11Formalization.Paid16GeneralH46.all_valid
#print axioms N11Formalization.Paid16GeneralH47.all_valid
#print axioms N11Formalization.Paid16GeneralH48.all_valid
#print axioms N11Formalization.Paid16GeneralH49.all_valid
#print axioms N11Formalization.Paid16GeneralH50.all_valid
#print axioms N11Formalization.Paid16GeneralH51.all_valid
#print axioms N11Formalization.Paid16GeneralH52.all_valid
#print axioms N11Formalization.Paid16GeneralH53.all_valid
#print axioms N11Formalization.Paid16GeneralH54.all_valid
#print axioms N11Formalization.Paid16GeneralH55.all_valid
#print axioms N11Formalization.Paid16GeneralH56.all_valid
#print axioms N11Formalization.Paid16GeneralH57.all_valid
#print axioms N11Formalization.Paid16GeneralH58.all_valid
#print axioms N11Formalization.Paid16GeneralH59.all_valid
#print axioms N11Formalization.Paid16GeneralH60.all_valid
#print axioms N11Formalization.Paid16GeneralH61.all_valid
#print axioms N11Formalization.Paid16GeneralH62.all_valid
#print axioms N11Formalization.Paid16GeneralH63.all_valid
#print axioms N11Formalization.Paid16GeneralH64.all_valid
#print axioms N11Formalization.Paid16GeneralH65.all_valid
#print axioms N11Formalization.Paid16GeneralH66.all_valid
#print axioms N11Formalization.Paid16GeneralH67.all_valid
#print axioms N11Formalization.Paid16GeneralH68.all_valid
#print axioms N11Formalization.Paid16GeneralH69.all_valid
#print axioms N11Formalization.Paid16GeneralH70.all_valid
#print axioms N11Formalization.Paid16GeneralH71.all_valid
#print axioms N11Formalization.Paid16GeneralH72.all_valid
#print axioms N11Formalization.Paid16GeneralH73.all_valid
#print axioms N11Formalization.Paid16GeneralH74.all_valid
#print axioms N11Formalization.Paid16GeneralH75.all_valid
#print axioms N11Formalization.Paid16GeneralH76.all_valid
#print axioms N11Formalization.Paid16GeneralH77.all_valid
#print axioms N11Formalization.Paid16GeneralH78.all_valid
#print axioms N11Formalization.Paid16GeneralH79.all_valid
#print axioms N11Formalization.Paid16GeneralH80.all_valid
#print axioms N11Formalization.Paid16GeneralH81.all_valid
#print axioms N11Formalization.Paid16GeneralH82.all_valid

-- 3. aggregate / dispatch / main axiom reports
#print axioms N11Formalization.Paid16GeneralNext1182.new_count
#print axioms N11Formalization.Paid16GeneralNext1182.new_radius
#print axioms N11Formalization.EnergyTerminalBatchB13.paid_radius
#print axioms N11Formalization.EnergyTerminalBatchB13.remaining_of
#print axioms N11Formalization.EnergyTerminalBatchB13Main.main_of_energy_and_seven_classes

-- 4. negative controls: counts are EXACT and the residual shrank
example : N11Formalization.EnergyTerminalBatchB13.paidIDs.card = 1997 := by
  decide +kernel
example : ¬ (N11Formalization.EnergyTerminalBatchB13.paidIDs.card = 1996) := by
  decide +kernel
example : ¬ (N11Formalization.Paid16GeneralNext1182.newIDs.card = 1181) := by
  decide +kernel
example : ¬ (N11Formalization.EnergyTerminalBatchB12.paidIDs.card =
    N11Formalization.EnergyTerminalBatchB13.paidIDs.card) := by
  decide +kernel

end ProbeEnergyRest1182

