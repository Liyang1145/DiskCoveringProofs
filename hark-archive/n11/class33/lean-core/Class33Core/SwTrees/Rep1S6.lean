import Class33Core.SwTrees.Rep1S6P0
import Class33Core.SwTrees.Rep1S6P1
import Class33Core.SwTrees.Rep1S6P2
import Class33Core.SwTrees.Rep1S6P3
import Class33Core.SwTrees.Rep1S6P4
import Class33Core.SwTrees.Rep1S6P5
import Class33Core.SwTrees.Rep1S6P6
import Class33Core.SwTrees.Rep1S6P7
/- rep1 Lean switch 6, M=132957/500000 (hist upper 0.26589346)
   725 leaves in 8 parts. Core-Lean pre-validation, NOT credit. -/
namespace Class33Core.SwTrees.Rep1S6
open Class33Core.SwitchKernel
def partEnds : List (Rat × Rat) := [((0 : Rat),(523143/512000 : Rat)),((523143/512000 : Rat),(4309253/4096000 : Rat)),((4309253/4096000 : Rat),(4387803/4096000 : Rat)),((4387803/4096000 : Rat),(4466353/4096000 : Rat)),((4466353/4096000 : Rat),(2292089/2048000 : Rat)),((2292089/2048000 : Rat),(124109/102400 : Rat)),((124109/102400 : Rat),(799639/512000 : Rat)),((799639/512000 : Rat),(1571/1000 : Rat))]
theorem parts_match : [(P0.ends.head?.map (·.1), P0.ends.getLast?.map (·.2)),(P1.ends.head?.map (·.1), P1.ends.getLast?.map (·.2)),(P2.ends.head?.map (·.1), P2.ends.getLast?.map (·.2)),(P3.ends.head?.map (·.1), P3.ends.getLast?.map (·.2)),(P4.ends.head?.map (·.1), P4.ends.getLast?.map (·.2)),(P5.ends.head?.map (·.1), P5.ends.getLast?.map (·.2)),(P6.ends.head?.map (·.1), P6.ends.getLast?.map (·.2)),(P7.ends.head?.map (·.1), P7.ends.getLast?.map (·.2))] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel
/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/
theorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel
end Class33Core.SwTrees.Rep1S6
