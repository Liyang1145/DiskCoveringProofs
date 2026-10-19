import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P57
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(0 : Rat),(1/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (3/4 : Rat) (949379/1048576 : Rat) (37483/262144 : Rat) (45321/262144 : Rat),.S 1 (27/32 : Rat),.L (3/4 : Rat) (991999/1048576 : Rat) (37483/262144 : Rat) (94755/524288 : Rat),.L (25/32 : Rat) (512487/524288 : Rat) (156225/1048576 : Rat) (195883/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P57
