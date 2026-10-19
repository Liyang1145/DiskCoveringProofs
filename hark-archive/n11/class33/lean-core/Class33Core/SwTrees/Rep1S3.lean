import Class33Core.SwTrees.Rep1S3P0
import Class33Core.SwTrees.Rep1S3P1
import Class33Core.SwTrees.Rep1S3P2
import Class33Core.SwTrees.Rep1S3P3
import Class33Core.SwTrees.Rep1S3P4
import Class33Core.SwTrees.Rep1S3P5
import Class33Core.SwTrees.Rep1S3P6
/- rep1 Lean switch 3, M=3/50000 (hist upper 0.00003990)
   655 leaves in 7 parts. Core-Lean pre-validation, NOT credit. -/
namespace Class33Core.SwTrees.Rep1S3
open Class33Core.SwitchKernel
def partEnds : List (Rat × Rat) := [((0 : Rat),(849911/1024000 : Rat)),((849911/1024000 : Rat),(7133911/8192000 : Rat)),((7133911/8192000 : Rat),(14552173/16384000 : Rat)),((14552173/16384000 : Rat),(14709273/16384000 : Rat)),((14709273/16384000 : Rat),(3753119/4096000 : Rat)),((3753119/4096000 : Rat),(991301/1024000 : Rat)),((991301/1024000 : Rat),(1571/1000 : Rat))]
theorem parts_match : [(P0.ends.head?.map (·.1), P0.ends.getLast?.map (·.2)),(P1.ends.head?.map (·.1), P1.ends.getLast?.map (·.2)),(P2.ends.head?.map (·.1), P2.ends.getLast?.map (·.2)),(P3.ends.head?.map (·.1), P3.ends.getLast?.map (·.2)),(P4.ends.head?.map (·.1), P4.ends.getLast?.map (·.2)),(P5.ends.head?.map (·.1), P5.ends.getLast?.map (·.2)),(P6.ends.head?.map (·.1), P6.ends.getLast?.map (·.2))] = partEnds.map (fun x => (some x.1, some x.2)) := by decide +kernel
/-- all leaves accepted (part theorems) and they tile [0,1571/1000]. -/
theorem tiles : chainB partEnds = true ∧ (partEnds.head?.map (·.1)) = some 0 ∧ (partEnds.getLast?.map (·.2)) = some (1571/1000) := by decide +kernel
end Class33Core.SwTrees.Rep1S3
