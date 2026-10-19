import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P12
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(11/16 : Rat),(3/4 : Rat),(0 : Rat),(1/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (5/8 : Rat) (818219/1048576 : Rat) (31203/262144 : Rat) (156037/1048576 : Rat),.L (5/8 : Rat) (892979/1048576 : Rat) (31203/262144 : Rat) (10651/65536 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P12
