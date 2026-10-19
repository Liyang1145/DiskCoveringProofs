import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P7
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(0 : Rat),(1/2 : Rat),(0 : Rat),(1/8 : Rat),(3/4 : Rat),(13/16 : Rat)⟩
def toks : List Tok := [.S 1 (1/16 : Rat),.S 0 (1/4 : Rat),.S 2 (25/32 : Rat),.S 1 (1/32 : Rat),.L (23/32 : Rat) (820223/1048576 : Rat) (143645/1048576 : Rat) (78211/524288 : Rat),.L (11/16 : Rat) (394281/524288 : Rat) (68681/524288 : Rat) (75171/524288 : Rat),.S 1 (1/32 : Rat),.L (3/4 : Rat) (852991/1048576 : Rat) (37483/262144 : Rat) (162721/1048576 : Rat),.L (23/32 : Rat) (410663/524288 : Rat) (143645/1048576 : Rat) (78317/524288 : Rat),.L (11/16 : Rat) (430025/524288 : Rat) (68681/524288 : Rat) (164079/1048576 : Rat),.S 0 (1/4 : Rat),.S 2 (25/32 : Rat),.S 1 (3/32 : Rat),.L (21/32 : Rat) (378497/524288 : Rat) (131085/1048576 : Rat) (36071/262144 : Rat),.L (5/8 : Rat) (725533/1048576 : Rat) (31203/262144 : Rat) (34563/262144 : Rat),.S 1 (3/32 : Rat),.L (11/16 : Rat) (789751/1048576 : Rat) (68681/524288 : Rat) (75285/524288 : Rat),.L (21/32 : Rat) (379139/524288 : Rat) (131085/1048576 : Rat) (144531/1048576 : Rat),.L (328885/524288 : Rat) (401917/524288 : Rat) (62637/524288 : Rat) (76637/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P7
