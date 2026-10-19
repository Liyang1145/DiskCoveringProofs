import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P262
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(5/8 : Rat),(11/16 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (0 : Rat) (95053/131072 : Rat) (0 : Rat) (72471/524288 : Rat),.S 0 (3/2 : Rat),.L (301529/524288 : Rat) (1077341/1048576 : Rat) (57405/524288 : Rat) (103009/524288 : Rat),.L (421097/524288 : Rat) (337615/262144 : Rat) (40161/262144 : Rat) (64805/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P262
