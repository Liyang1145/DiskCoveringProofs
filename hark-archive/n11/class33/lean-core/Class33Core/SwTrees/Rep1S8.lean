import Class33Core.SwTrees.Rep1S8P0
import Class33Core.SwTrees.Rep1S8P1
import Class33Core.SwTrees.Rep1S8P2
import Class33Core.SwTrees.Rep1S8P3
import Class33Core.SwTrees.Rep1S8P4
import Class33Core.SwTrees.Rep1S8P5
/- rep1 Lean switch 8, M=3/50000 (hist upper 0.00003989)
   552 leaves in 6 parts. Core-Lean pre-validation, NOT credit. -/
namespace Class33Core.SwTrees.Rep1S8
open Class33Core.SwitchKernel
def partEnds : List (Rat × Rat) := [((0 : Rat),(1308643/2048000 : Rat)),((1308643/2048000 : Rat),(1120123/1638400 : Rat)),((1120123/1638400 : Rat),(1151543/1638400 : Rat)),((1151543/1638400 : Rat),(1182963/1638400 : Rat)),((1182963/1638400 : Rat),(787071/1024000 : Rat)),((787071/1024000 : Rat),(1571/1000 : Rat))]
theorem parts_match : [(P0.ends.head?.map (·.1), P0.ends.getLast?.map (·.2)),(P1.ends.head?.map (·.1), P1.ends.getLast?.map (·.2)),(P2.ends.head?.map (·.1), P2.ends.getLast?.map (·.2)),(P3.ends.head?.map (·.1), P3.ends.getLast?.map (·.2)),(P4.ends.head?.map (·.1), P4.ends.getLast?.map (·.2)),(P5.ends.head?.map (·.1), P5.ends.getLast?.map (·.2))] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel
/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/
theorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel
end Class33Core.SwTrees.Rep1S8
