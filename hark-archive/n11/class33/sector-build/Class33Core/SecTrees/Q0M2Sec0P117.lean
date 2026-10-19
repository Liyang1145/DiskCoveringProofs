import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P117
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(1/8 : Rat),(3/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (3/4 : Rat) (511331/524288 : Rat) (37483/262144 : Rat) (48859/262144 : Rat),.S 0 (3/2 : Rat),.L (426491/524288 : Rat) (1121439/1048576 : Rat) (81359/524288 : Rat) (26821/131072 : Rat),.S 1 (31/32 : Rat),.L (113967/131072 : Rat) (1191285/1048576 : Rat) (174027/1048576 : Rat) (57035/262144 : Rat),.L (943911/1048576 : Rat) (1224233/1048576 : Rat) (180229/1048576 : Rat) (58639/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P117
