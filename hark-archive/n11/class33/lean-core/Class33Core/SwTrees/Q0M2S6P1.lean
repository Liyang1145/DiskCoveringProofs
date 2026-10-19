import Class33Core.SwTrees.Q0M2S6Base
namespace Class33Core.SwTrees.Q0M2S6.P1
open Class33Core Class33Core.SwitchKernel Class33Core.SwTrees.Q0M2S6
def c0 : List (Rat × Rat) := [((42417/32000 : Rat),(10997/8000 : Rat)),((10997/8000 : Rat),(45559/32000 : Rat)),((45559/32000 : Rat),(4713/3200 : Rat)),((4713/3200 : Rat),(48701/32000 : Rat)),((48701/32000 : Rat),(1571/1000 : Rat))]
theorem c0_ok : allLeavesOK coeff M c0 = true ∧ chainB c0 = true := by decide +kernel
def ends : List (Rat × Rat) := [((42417/32000 : Rat),(1571/1000 : Rat))]
theorem ends_ok : chainB ends = true ∧ [(c0.head?.map (·.1), c0.getLast?.map (·.2))] = ends.map (fun x => (some x.1, some x.2)) := by decide +kernel
end Class33Core.SwTrees.Q0M2S6.P1
