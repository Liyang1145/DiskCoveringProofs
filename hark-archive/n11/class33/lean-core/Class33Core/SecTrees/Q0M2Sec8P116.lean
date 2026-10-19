import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P116
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(1/2 : Rat),(5/8 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 1 (9/16 : Rat),.S 2 (13/16 : Rat),.L (1079813/1048576 : Rat) (45473/32768 : Rat) (6453/32768 : Rat) (34973/131072 : Rat),.L (141973/131072 : Rat) (190365/131072 : Rat) (27169/131072 : Rat) (293159/1048576 : Rat),.S 2 (13/16 : Rat),.L (283443/262144 : Rat) (1517269/1048576 : Rat) (216961/1048576 : Rat) (292043/1048576 : Rat),.L (1188529/1048576 : Rat) (1585105/1048576 : Rat) (227603/1048576 : Rat) (305473/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P116
