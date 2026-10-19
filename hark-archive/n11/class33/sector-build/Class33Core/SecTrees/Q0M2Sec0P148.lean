import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P148
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(13/16 : Rat),(27/32 : Rat),(11/32 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 1 (53/64 : Rat),.S 2 (23/64 : Rat),.S 0 (21/8 : Rat),.L (566039/524288 : Rat) (1240901/1048576 : Rat) (27079/131072 : Rat) (237805/1048576 : Rat),.L (1148159/1048576 : Rat) (625871/524288 : Rat) (219755/1048576 : Rat) (239919/1048576 : Rat),.S 0 (21/8 : Rat),.L (573213/524288 : Rat) (314165/262144 : Rat) (109709/524288 : Rat) (240879/1048576 : Rat),.L (581513/524288 : Rat) (633915/524288 : Rat) (55661/262144 : Rat) (243059/1048576 : Rat),.S 2 (23/64 : Rat),.S 0 (21/8 : Rat),.L (573965/524288 : Rat) (157169/131072 : Rat) (109855/524288 : Rat) (120507/524288 : Rat),.L (1164095/1048576 : Rat) (1268253/1048576 : Rat) (222851/1048576 : Rat) (121571/524288 : Rat),.S 0 (21/8 : Rat),.L (145281/131072 : Rat) (1273109/1048576 : Rat) (55623/262144 : Rat) (122045/524288 : Rat),.L (589469/524288 : Rat) (1284343/1048576 : Rat) (225737/1048576 : Rat) (61571/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P148
