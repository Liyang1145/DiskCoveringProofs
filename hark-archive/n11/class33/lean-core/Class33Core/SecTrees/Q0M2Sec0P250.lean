import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P250
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(5/8 : Rat),(11/16 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (0 : Rat) (711483/1048576 : Rat) (0 : Rat) (16945/131072 : Rat),.S 0 (3/2 : Rat),.L (2107/4096 : Rat) (497885/524288 : Rat) (12831/131072 : Rat) (190239/1048576 : Rat),.L (753281/1048576 : Rat) (310657/262144 : Rat) (143571/1048576 : Rat) (119071/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P250
