import Class33Core.SwTrees.Rep1S5P0
import Class33Core.SwTrees.Rep1S5P1
import Class33Core.SwTrees.Rep1S5P2
import Class33Core.SwTrees.Rep1S5P3
import Class33Core.SwTrees.Rep1S5P4
import Class33Core.SwTrees.Rep1S5P5
import Class33Core.SwTrees.Rep1S5P6
import Class33Core.SwTrees.Rep1S5P7
import Class33Core.SwTrees.Rep1S5P8
import Class33Core.SwTrees.Rep1S5P9
import Class33Core.SwTrees.Rep1S5P10
/- rep1 Lean switch 5, M=275777/1000000 (hist upper 0.27575612)
   1037 leaves in 11 parts. Core-Lean pre-validation, NOT credit. -/
namespace Class33Core.SwTrees.Rep1S5
open Class33Core.SwitchKernel
def partEnds : List (Rat × Rat) := [((0 : Rat),(26707/25600 : Rat)),((26707/25600 : Rat),(4387803/4096000 : Rat)),((4387803/4096000 : Rat),(444593/409600 : Rat)),((444593/409600 : Rat),(897041/819200 : Rat)),((897041/819200 : Rat),(14139/12800 : Rat)),((14139/12800 : Rat),(912751/819200 : Rat)),((912751/819200 : Rat),(1855351/1638400 : Rat)),((1855351/1638400 : Rat),(2389491/2048000 : Rat)),((2389491/2048000 : Rat),(83263/64000 : Rat)),((83263/64000 : Rat),(3190701/2048000 : Rat)),((3190701/2048000 : Rat),(1571/1000 : Rat))]
theorem parts_match : [(P0.ends.head?.map (·.1), P0.ends.getLast?.map (·.2)),(P1.ends.head?.map (·.1), P1.ends.getLast?.map (·.2)),(P2.ends.head?.map (·.1), P2.ends.getLast?.map (·.2)),(P3.ends.head?.map (·.1), P3.ends.getLast?.map (·.2)),(P4.ends.head?.map (·.1), P4.ends.getLast?.map (·.2)),(P5.ends.head?.map (·.1), P5.ends.getLast?.map (·.2)),(P6.ends.head?.map (·.1), P6.ends.getLast?.map (·.2)),(P7.ends.head?.map (·.1), P7.ends.getLast?.map (·.2)),(P8.ends.head?.map (·.1), P8.ends.getLast?.map (·.2)),(P9.ends.head?.map (·.1), P9.ends.getLast?.map (·.2)),(P10.ends.head?.map (·.1), P10.ends.getLast?.map (·.2))] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel
/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/
theorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel
end Class33Core.SwTrees.Rep1S5
