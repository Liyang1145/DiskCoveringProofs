import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P60
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(3/4 : Rat),(7/8 : Rat),(0 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 2 (1/8 : Rat),.L (5/8 : Rat) (1150153/1048576 : Rat) (31203/262144 : Rat) (220143/1048576 : Rat),.S 1 (13/16 : Rat),.L (339951/524288 : Rat) (297179/262144 : Rat) (64755/524288 : Rat) (28455/131072 : Rat),.L (742225/1048576 : Rat) (1257199/1048576 : Rat) (141451/1048576 : Rat) (30123/131072 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P60
