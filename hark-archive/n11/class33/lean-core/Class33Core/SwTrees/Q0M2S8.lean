import Class33Core.SwTrees.Q0M2S8P0
/- q0m2 Lean switch 8, M=11693/50000 (hist upper 0.23185979)
   47 leaves in 1 parts. Core-Lean pre-validation, NOT credit. -/
namespace Class33Core.SwTrees.Q0M2S8
open Class33Core.SwitchKernel
def partEnds : List (Rat × Rat) := [((0 : Rat),(1571/1000 : Rat))]
theorem parts_match : [(P0.ends.head?.map (·.1), P0.ends.getLast?.map (·.2))] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel
/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/
theorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel
end Class33Core.SwTrees.Q0M2S8
