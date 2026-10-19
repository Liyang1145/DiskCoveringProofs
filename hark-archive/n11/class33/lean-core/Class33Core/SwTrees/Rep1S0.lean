import Class33Core.SwTrees.Rep1S0P0
import Class33Core.SwTrees.Rep1S0P1
/- rep1 Lean switch 0, M=3/50000 (hist upper 0.00003985)
   547 leaves in 2 parts. Core-Lean pre-validation, NOT credit. -/
namespace Class33Core.SwTrees.Rep1S0
open Class33Core.SwitchKernel
def partEnds : List (Rat × Rat) := [((0 : Rat),(48701/64000 : Rat)),((48701/64000 : Rat),(1571/1000 : Rat))]
theorem parts_match : [(P0.ends.head?.map (·.1), P0.ends.getLast?.map (·.2)),(P1.ends.head?.map (·.1), P1.ends.getLast?.map (·.2))] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel
/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/
theorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel
end Class33Core.SwTrees.Rep1S0
