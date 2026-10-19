import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P62
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(3/4 : Rat),(1 : Rat),(0 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 1 (7/8 : Rat),.L (1/2 : Rat) (1343089/1048576 : Rat) (99765/1048576 : Rat) (16111/65536 : Rat),.S 2 (1/8 : Rat),.L (3/4 : Rat) (1284239/1048576 : Rat) (37483/262144 : Rat) (30783/131072 : Rat),.L (805057/1048576 : Rat) (1393315/1048576 : Rat) (38377/262144 : Rat) (133813/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P62
