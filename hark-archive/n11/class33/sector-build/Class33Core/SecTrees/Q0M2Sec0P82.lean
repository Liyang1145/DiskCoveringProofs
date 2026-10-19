import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P82
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(27/32 : Rat),(7/8 : Rat),(1/8 : Rat),(3/16 : Rat)⟩
def toks : List Tok := [.S 2 (5/32 : Rat),.S 0 (9/4 : Rat),.L (227051/262144 : Rat) (267553/262144 : Rat) (173347/1048576 : Rat) (204637/1048576 : Rat),.S 1 (55/64 : Rat),.L (232743/262144 : Rat) (541227/524288 : Rat) (88867/524288 : Rat) (207009/1048576 : Rat),.L (473557/524288 : Rat) (137371/131072 : Rat) (90423/524288 : Rat) (105105/524288 : Rat),.S 0 (9/4 : Rat),.L (924635/1048576 : Rat) (1095565/1048576 : Rat) (176513/1048576 : Rat) (104775/524288 : Rat),.S 1 (55/64 : Rat),.L (952519/1048576 : Rat) (556341/524288 : Rat) (181889/1048576 : Rat) (212869/1048576 : Rat),.L (968577/1048576 : Rat) (564605/524288 : Rat) (184987/1048576 : Rat) (54019/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P82
