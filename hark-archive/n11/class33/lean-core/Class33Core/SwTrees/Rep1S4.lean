import Class33Core.SwTrees.Rep1S4P0
import Class33Core.SwTrees.Rep1S4P1
import Class33Core.SwTrees.Rep1S4P2
import Class33Core.SwTrees.Rep1S4P3
import Class33Core.SwTrees.Rep1S4P4
import Class33Core.SwTrees.Rep1S4P5
import Class33Core.SwTrees.Rep1S4P6
/- rep1 Lean switch 4, M=1007/500000 (hist upper 0.00199321)
   677 leaves in 7 parts. Core-Lean pre-validation, NOT credit. -/
namespace Class33Core.SwTrees.Rep1S4
open Class33Core.SwitchKernel
def partEnds : List (Rat × Rat) := [((0 : Rat),(441451/512000 : Rat)),((441451/512000 : Rat),(73837/81920 : Rat)),((73837/81920 : Rat),(15036041/16384000 : Rat)),((15036041/16384000 : Rat),(15193141/16384000 : Rat)),((15193141/16384000 : Rat),(7724607/8192000 : Rat)),((7724607/8192000 : Rat),(501149/512000 : Rat)),((501149/512000 : Rat),(1571/1000 : Rat))]
theorem parts_match : [(P0.ends.head?.map (·.1), P0.ends.getLast?.map (·.2)),(P1.ends.head?.map (·.1), P1.ends.getLast?.map (·.2)),(P2.ends.head?.map (·.1), P2.ends.getLast?.map (·.2)),(P3.ends.head?.map (·.1), P3.ends.getLast?.map (·.2)),(P4.ends.head?.map (·.1), P4.ends.getLast?.map (·.2)),(P5.ends.head?.map (·.1), P5.ends.getLast?.map (·.2)),(P6.ends.head?.map (·.1), P6.ends.getLast?.map (·.2))] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel
/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/
theorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel
end Class33Core.SwTrees.Rep1S4
