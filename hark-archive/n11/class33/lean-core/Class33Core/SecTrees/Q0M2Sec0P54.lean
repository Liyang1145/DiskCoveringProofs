import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P54
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(3/4 : Rat),(13/16 : Rat),(1/16 : Rat),(1/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (5/8 : Rat) (53363/65536 : Rat) (31203/262144 : Rat) (81439/524288 : Rat),.S 0 (3/2 : Rat),.L (343925/524288 : Rat) (114817/131072 : Rat) (16379/131072 : Rat) (87669/524288 : Rat),.L (179341/262144 : Rat) (987073/1048576 : Rat) (136685/1048576 : Rat) (188559/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P54
