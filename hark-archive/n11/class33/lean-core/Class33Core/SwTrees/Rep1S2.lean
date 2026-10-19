import Class33Core.SwTrees.Rep1S2P0
import Class33Core.SwTrees.Rep1S2P1
import Class33Core.SwTrees.Rep1S2P2
import Class33Core.SwTrees.Rep1S2P3
import Class33Core.SwTrees.Rep1S2P4
import Class33Core.SwTrees.Rep1S2P5
import Class33Core.SwTrees.Rep1S2P6
import Class33Core.SwTrees.Rep1S2P7
import Class33Core.SwTrees.Rep1S2P8
import Class33Core.SwTrees.Rep1S2P9
import Class33Core.SwTrees.Rep1S2P10
import Class33Core.SwTrees.Rep1S2P11
import Class33Core.SwTrees.Rep1S2P12
import Class33Core.SwTrees.Rep1S2P13
import Class33Core.SwTrees.Rep1S2P14
import Class33Core.SwTrees.Rep1S2P15
import Class33Core.SwTrees.Rep1S2P16
import Class33Core.SwTrees.Rep1S2P17
/- rep1 Lean switch 2, M=30833/125000 (hist upper 0.24664370)
   1789 leaves in 18 parts. Core-Lean pre-validation, NOT credit. -/
namespace Class33Core.SwTrees.Rep1S2
open Class33Core.SwitchKernel
def partEnds : List (Rat × Rat) := [((0 : Rat),(95831/128000 : Rat)),((95831/128000 : Rat),(98973/102400 : Rat)),((98973/102400 : Rat),(4180431/4096000 : Rat)),((4180431/4096000 : Rat),(4290401/4096000 : Rat)),((4290401/4096000 : Rat),(4368951/4096000 : Rat)),((4368951/4096000 : Rat),(17669037/16384000 : Rat)),((17669037/16384000 : Rat),(17826137/16384000 : Rat)),((17826137/16384000 : Rat),(17983237/16384000 : Rat)),((17983237/16384000 : Rat),(18140337/16384000 : Rat)),((18140337/16384000 : Rat),(18297437/16384000 : Rat)),((18297437/16384000 : Rat),(18454537/16384000 : Rat)),((18454537/16384000 : Rat),(4661157/4096000 : Rat)),((4661157/4096000 : Rat),(4739707/4096000 : Rat)),((4739707/4096000 : Rat),(193233/163840 : Rat)),((193233/163840 : Rat),(199517/163840 : Rat)),((199517/163840 : Rat),(2643993/2048000 : Rat)),((2643993/2048000 : Rat),(1475169/1024000 : Rat)),((1475169/1024000 : Rat),(1571/1000 : Rat))]
theorem parts_match : [(P0.ends.head?.map (·.1), P0.ends.getLast?.map (·.2)),(P1.ends.head?.map (·.1), P1.ends.getLast?.map (·.2)),(P2.ends.head?.map (·.1), P2.ends.getLast?.map (·.2)),(P3.ends.head?.map (·.1), P3.ends.getLast?.map (·.2)),(P4.ends.head?.map (·.1), P4.ends.getLast?.map (·.2)),(P5.ends.head?.map (·.1), P5.ends.getLast?.map (·.2)),(P6.ends.head?.map (·.1), P6.ends.getLast?.map (·.2)),(P7.ends.head?.map (·.1), P7.ends.getLast?.map (·.2)),(P8.ends.head?.map (·.1), P8.ends.getLast?.map (·.2)),(P9.ends.head?.map (·.1), P9.ends.getLast?.map (·.2)),(P10.ends.head?.map (·.1), P10.ends.getLast?.map (·.2)),(P11.ends.head?.map (·.1), P11.ends.getLast?.map (·.2)),(P12.ends.head?.map (·.1), P12.ends.getLast?.map (·.2)),(P13.ends.head?.map (·.1), P13.ends.getLast?.map (·.2)),(P14.ends.head?.map (·.1), P14.ends.getLast?.map (·.2)),(P15.ends.head?.map (·.1), P15.ends.getLast?.map (·.2)),(P16.ends.head?.map (·.1), P16.ends.getLast?.map (·.2)),(P17.ends.head?.map (·.1), P17.ends.getLast?.map (·.2))] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel
/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/
theorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel
end Class33Core.SwTrees.Rep1S2
