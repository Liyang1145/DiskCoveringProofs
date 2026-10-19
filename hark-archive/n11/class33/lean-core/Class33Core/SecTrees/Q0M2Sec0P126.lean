import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P126
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(3/4 : Rat),(13/16 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (7/16 : Rat) (790047/1048576 : Rat) (87263/1048576 : Rat) (150627/1048576 : Rat),.S 0 (3/2 : Rat),.L (620499/1048576 : Rat) (59653/65536 : Rat) (923/8192 : Rat) (91131/524288 : Rat),.L (742235/1048576 : Rat) (139053/131072 : Rat) (141453/1048576 : Rat) (212819/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P126
