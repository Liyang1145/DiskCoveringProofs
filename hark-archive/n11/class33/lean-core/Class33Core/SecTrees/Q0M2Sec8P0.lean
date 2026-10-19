import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P0
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(0 : Rat),(1 : Rat),(0 : Rat),(1/4 : Rat),(0 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 2 (1/4 : Rat),.L (0 : Rat) (369767/1048576 : Rat) (0 : Rat) (70309/1048576 : Rat),.S 0 (1/2 : Rat),.S 2 (3/8 : Rat),.L (0 : Rat) (424643/1048576 : Rat) (0 : Rat) (40381/524288 : Rat),.S 1 (1/8 : Rat),.L (1/4 : Rat) (540383/1048576 : Rat) (24913/524288 : Rat) (51419/524288 : Rat),.S 1 (3/16 : Rat),.L (3/16 : Rat) (424643/1048576 : Rat) (37363/1048576 : Rat) (40381/524288 : Rat),.L (1/8 : Rat) (376357/1048576 : Rat) (12453/524288 : Rat) (17891/262144 : Rat),.S 1 (1/8 : Rat),.L (1/8 : Rat) (146035/262144 : Rat) (12453/524288 : Rat) (111195/1048576 : Rat),.L (44723/524288 : Rat) (268003/524288 : Rat) (16995/1048576 : Rat) (51001/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P0
