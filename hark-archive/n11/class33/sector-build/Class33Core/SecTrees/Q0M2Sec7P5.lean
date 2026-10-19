import Class33Core.SecTrees.Q0M2Sec7Base
namespace Class33Core.SecTrees.Q0M2Sec7.P5
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec7
def box : Box := ⟨(2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(0 : Rat),(1/4 : Rat),(1/2 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (3/4 : Rat),.L (1/4 : Rat) (1201295/1048576 : Rat) (24913/524288 : Rat) (230089/1048576 : Rat),.S 1 (1/8 : Rat),.L (5/8 : Rat) (1284239/1048576 : Rat) (31203/262144 : Rat) (30783/131072 : Rat),.S 2 (7/8 : Rat),.L (339951/524288 : Rat) (1257199/1048576 : Rat) (64755/524288 : Rat) (30123/131072 : Rat),.L (805057/1048576 : Rat) (1393315/1048576 : Rat) (38377/262144 : Rat) (133813/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec7.P5
