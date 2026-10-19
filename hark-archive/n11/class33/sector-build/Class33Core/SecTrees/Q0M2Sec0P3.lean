import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P3
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(314159265358979323847/100000000000000000000 : Rat),(0 : Rat),(1/4 : Rat),(1/2 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (3/4 : Rat),.S 1 (1/8 : Rat),.L (3/8 : Rat) (63455/65536 : Rat) (37387/524288 : Rat) (194009/1048576 : Rat),.L (1/4 : Rat) (139985/131072 : Rat) (24913/524288 : Rat) (107133/524288 : Rat),.S 1 (1/8 : Rat),.L (5/8 : Rat) (1284239/1048576 : Rat) (31203/262144 : Rat) (30783/131072 : Rat),.L (1/2 : Rat) (1393315/1048576 : Rat) (99765/1048576 : Rat) (133813/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P3
