import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P288
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(5/8 : Rat),(11/16 : Rat),(7/8 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (3/16 : Rat) (237527/262144 : Rat) (37363/1048576 : Rat) (181425/1048576 : Rat),.S 0 (3/2 : Rat),.L (740139/1048576 : Rat) (161983/131072 : Rat) (141051/1048576 : Rat) (248535/1048576 : Rat),.S 0 (7/4 : Rat),.L (523813/524288 : Rat) (713191/524288 : Rat) (25033/131072 : Rat) (274125/1048576 : Rat),.L (1169833/1048576 : Rat) (1560695/1048576 : Rat) (223967/1048576 : Rat) (150317/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P288
