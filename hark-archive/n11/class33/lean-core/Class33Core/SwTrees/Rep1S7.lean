import Class33Core.SwTrees.Rep1S7P0
import Class33Core.SwTrees.Rep1S7P1
import Class33Core.SwTrees.Rep1S7P2
import Class33Core.SwTrees.Rep1S7P3
import Class33Core.SwTrees.Rep1S7P4
import Class33Core.SwTrees.Rep1S7P5
import Class33Core.SwTrees.Rep1S7P6
import Class33Core.SwTrees.Rep1S7P7
/- rep1 Lean switch 7, M=12301/1000000 (hist upper 0.01228030)
   714 leaves in 8 parts. Core-Lean pre-validation, NOT credit. -/
namespace Class33Core.SwTrees.Rep1S7
open Class33Core.SwitchKernel
def partEnds : List (Rat × Rat) := [((0 : Rat),(1855351/2048000 : Rat)),((1855351/2048000 : Rat),(1933901/2048000 : Rat)),((1933901/2048000 : Rat),(1965321/2048000 : Rat)),((1965321/2048000 : Rat),(3969917/4096000 : Rat)),((3969917/4096000 : Rat),(1003869/1024000 : Rat)),((1003869/1024000 : Rat),(4111307/4096000 : Rat)),((4111307/4096000 : Rat),(300061/256000 : Rat)),((300061/256000 : Rat),(1571/1000 : Rat))]
theorem parts_match : [(P0.ends.head?.map (·.1), P0.ends.getLast?.map (·.2)),(P1.ends.head?.map (·.1), P1.ends.getLast?.map (·.2)),(P2.ends.head?.map (·.1), P2.ends.getLast?.map (·.2)),(P3.ends.head?.map (·.1), P3.ends.getLast?.map (·.2)),(P4.ends.head?.map (·.1), P4.ends.getLast?.map (·.2)),(P5.ends.head?.map (·.1), P5.ends.getLast?.map (·.2)),(P6.ends.head?.map (·.1), P6.ends.getLast?.map (·.2)),(P7.ends.head?.map (·.1), P7.ends.getLast?.map (·.2))] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel
/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/
theorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel
end Class33Core.SwTrees.Rep1S7
