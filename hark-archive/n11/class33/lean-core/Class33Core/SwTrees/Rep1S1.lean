import Class33Core.SwTrees.Rep1S1P0
import Class33Core.SwTrees.Rep1S1P1
import Class33Core.SwTrees.Rep1S1P2
import Class33Core.SwTrees.Rep1S1P3
import Class33Core.SwTrees.Rep1S1P4
/- rep1 Lean switch 1, M=5309/25000 (hist upper 0.21233978)
   1312 leaves in 5 parts. Core-Lean pre-validation, NOT credit. -/
namespace Class33Core.SwTrees.Rep1S1
open Class33Core.SwitchKernel
def partEnds : List (Rat × Rat) := [((0 : Rat),(1066709/1024000 : Rat)),((1066709/1024000 : Rat),(17725593/16384000 : Rat)),((17725593/16384000 : Rat),(18196893/16384000 : Rat)),((18196893/16384000 : Rat),(617403/512000 : Rat)),((617403/512000 : Rat),(1571/1000 : Rat))]
theorem parts_match : [(P0.ends.head?.map (·.1), P0.ends.getLast?.map (·.2)),(P1.ends.head?.map (·.1), P1.ends.getLast?.map (·.2)),(P2.ends.head?.map (·.1), P2.ends.getLast?.map (·.2)),(P3.ends.head?.map (·.1), P3.ends.getLast?.map (·.2)),(P4.ends.head?.map (·.1), P4.ends.getLast?.map (·.2))] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel
/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/
theorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel
end Class33Core.SwTrees.Rep1S1
