import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P487
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(9/4 : Rat),(3/4 : Rat),(13/16 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 0 (17/8 : Rat),.S 2 (13/16 : Rat),.L (1300273/1048576 : Rat) (1516543/1048576 : Rat) (62349/262144 : Rat) (291899/1048576 : Rat),.L (1353367/1048576 : Rat) (1577775/1048576 : Rat) (259789/1048576 : Rat) (304019/1048576 : Rat),.S 2 (13/16 : Rat),.S 1 (25/32 : Rat),.L (1348109/1048576 : Rat) (384479/262144 : Rat) (129379/524288 : Rat) (296125/1048576 : Rat),.L (343977/262144 : Rat) (784159/524288 : Rat) (264209/1048576 : Rat) (302145/1048576 : Rat),.S 1 (25/32 : Rat),.L (1403539/1048576 : Rat) (399975/262144 : Rat) (134817/524288 : Rat) (308409/1048576 : Rat),.L (1432091/1048576 : Rat) (407267/262144 : Rat) (275247/1048576 : Rat) (78551/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P487
