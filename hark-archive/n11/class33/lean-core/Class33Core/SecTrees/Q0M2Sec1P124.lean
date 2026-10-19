import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P124
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(3/4 : Rat),(13/16 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 2 (11/16 : Rat),.S 1 (25/32 : Rat),.L (1188895/1048576 : Rat) (24151/16384 : Rat) (113837/524288 : Rat) (148829/524288 : Rat),.L (303887/262144 : Rat) (394919/262144 : Rat) (232863/1048576 : Rat) (76099/262144 : Rat),.S 1 (25/32 : Rat),.L (311257/262144 : Rat) (1608305/1048576 : Rat) (238609/1048576 : Rat) (155039/524288 : Rat),.S 0 (11/4 : Rat),.S 2 (23/32 : Rat),.L (1391453/1048576 : Rat) (1607971/1048576 : Rat) (66815/262144 : Rat) (77503/262144 : Rat),.L (1421525/1048576 : Rat) (820019/524288 : Rat) (273169/1048576 : Rat) (316387/1048576 : Rat),.L (21555/16384 : Rat) (205291/131072 : Rat) (132459/524288 : Rat) (158421/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P124
