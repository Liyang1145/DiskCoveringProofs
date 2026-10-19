import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P15
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(11/16 : Rat),(3/4 : Rat),(1/16 : Rat),(1/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (9/16 : Rat) (394241/524288 : Rat) (112281/1048576 : Rat) (75163/524288 : Rat),.L (618951/1048576 : Rat) (936783/1048576 : Rat) (14731/131072 : Rat) (178855/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P15
