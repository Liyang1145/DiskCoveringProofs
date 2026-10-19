import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P276
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(5/8 : Rat),(11/16 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/16 : Rat) (850467/1048576 : Rat) (3113/262144 : Rat) (40559/262144 : Rat),.S 0 (3/2 : Rat),.L (165965/262144 : Rat) (148049/131072 : Rat) (126439/1048576 : Rat) (226799/1048576 : Rat),.L (462451/524288 : Rat) (737627/524288 : Rat) (44141/262144 : Rat) (283749/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P276
