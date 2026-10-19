import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P37
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(11/16 : Rat),(3/4 : Rat),(5/16 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (5/16 : Rat) (44917/65536 : Rat) (62295/1048576 : Rat) (136937/1048576 : Rat),.L (532371/1048576 : Rat) (1133167/1048576 : Rat) (25327/262144 : Rat) (216845/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P37
