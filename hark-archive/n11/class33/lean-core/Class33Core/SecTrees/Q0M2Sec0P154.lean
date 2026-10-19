import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P154
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(3/4 : Rat),(13/16 : Rat),(3/8 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/4 : Rat) (807777/1048576 : Rat) (24913/524288 : Rat) (154031/1048576 : Rat),.S 0 (3/2 : Rat),.L (574951/1048576 : Rat) (263555/262144 : Rat) (109439/1048576 : Rat) (201541/1048576 : Rat),.S 0 (7/4 : Rat),.L (783121/1048576 : Rat) (287373/262144 : Rat) (9331/65536 : Rat) (220015/1048576 : Rat),.S 2 (7/16 : Rat),.L (444775/524288 : Rat) (1178945/1048576 : Rat) (169755/1048576 : Rat) (56435/262144 : Rat),.L (930931/1048576 : Rat) (612897/524288 : Rat) (88863/524288 : Rat) (58715/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P154
