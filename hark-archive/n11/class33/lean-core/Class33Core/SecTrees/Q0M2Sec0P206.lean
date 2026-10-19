import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P206
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(5/16 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (9/16 : Rat) (120399/131072 : Rat) (112281/1048576 : Rat) (183949/1048576 : Rat),.S 0 (3/2 : Rat),.L (393907/524288 : Rat) (1162461/1048576 : Rat) (150197/1048576 : Rat) (222535/1048576 : Rat),.S 0 (7/4 : Rat),.L (478315/524288 : Rat) (310757/262144 : Rat) (91341/524288 : Rat) (59555/262144 : Rat),.L (257429/262144 : Rat) (1328139/1048576 : Rat) (196799/1048576 : Rat) (1991/8192 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P206
