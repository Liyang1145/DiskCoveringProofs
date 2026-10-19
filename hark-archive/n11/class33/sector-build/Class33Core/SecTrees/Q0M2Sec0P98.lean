import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P98
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(0 : Rat),(1/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (7/8 : Rat) (1080519/1048576 : Rat) (87569/524288 : Rat) (103317/524288 : Rat),.S 1 (31/32 : Rat),.L (7/8 : Rat) (1123829/1048576 : Rat) (87569/524288 : Rat) (26879/131072 : Rat),.L (29/32 : Rat) (144595/131072 : Rat) (181455/1048576 : Rat) (221427/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P98
