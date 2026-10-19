import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P65
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(3/4 : Rat),(13/16 : Rat),(1/8 : Rat),(3/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (9/16 : Rat) (413963/524288 : Rat) (112281/1048576 : Rat) (157903/1048576 : Rat),.S 0 (3/2 : Rat),.L (329839/524288 : Rat) (463017/524288 : Rat) (125639/1048576 : Rat) (176783/1048576 : Rat),.L (719807/1048576 : Rat) (128297/131072 : Rat) (68577/524288 : Rat) (98077/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P65
