import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P300
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(3/4 : Rat),(7/8 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 1 (13/16 : Rat),.S 2 (11/16 : Rat),.L (1188895/1048576 : Rat) (394919/262144 : Rat) (113837/524288 : Rat) (76099/262144 : Rat),.S 0 (11/4 : Rat),.S 1 (25/32 : Rat),.L (1361827/1048576 : Rat) (1608305/1048576 : Rat) (261447/1048576 : Rat) (155039/524288 : Rat),.L (1390295/1048576 : Rat) (205291/131072 : Rat) (267033/1048576 : Rat) (158421/524288 : Rat),.L (675633/524288 : Rat) (205291/131072 : Rat) (259377/1048576 : Rat) (158421/524288 : Rat),.S 2 (11/16 : Rat),.S 0 (11/4 : Rat),.L (339453/262144 : Rat) (823775/524288 : Rat) (65165/262144 : Rat) (158941/524288 : Rat),.L (1347381/1048576 : Rat) (823775/524288 : Rat) (32327/131072 : Rat) (158941/524288 : Rat),.S 0 (11/4 : Rat),.S 1 (27/32 : Rat),.L (1418949/1048576 : Rat) (1676301/1048576 : Rat) (136331/524288 : Rat) (161805/524288 : Rat),.L (1447777/1048576 : Rat) (855113/524288 : Rat) (139167/524288 : Rat) (330383/1048576 : Rat),.L (1407969/1048576 : Rat) (855113/524288 : Rat) (33813/131072 : Rat) (330383/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P300
