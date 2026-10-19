import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P104
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(7/8 : Rat),(29/32 : Rat),(1/8 : Rat),(3/16 : Rat)⟩
def toks : List Tok := [.S 2 (5/32 : Rat),.S 0 (9/4 : Rat),.L (470227/524288 : Rat) (1103079/1048576 : Rat) (89781/524288 : Rat) (211007/1048576 : Rat),.S 1 (57/64 : Rat),.L (963265/1048576 : Rat) (557739/524288 : Rat) (91981/524288 : Rat) (53353/262144 : Rat),.L (979423/1048576 : Rat) (1131985/1048576 : Rat) (187081/1048576 : Rat) (216615/1048576 : Rat),.S 0 (9/4 : Rat),.L (478343/524288 : Rat) (564205/524288 : Rat) (182693/1048576 : Rat) (215921/1048576 : Rat),.S 1 (57/64 : Rat),.L (492323/524288 : Rat) (572867/524288 : Rat) (188089/1048576 : Rat) (219285/1048576 : Rat),.L (500363/524288 : Rat) (1162255/1048576 : Rat) (191195/1048576 : Rat) (222495/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P104
