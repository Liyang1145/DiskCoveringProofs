import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P20
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(11/16 : Rat),(3/4 : Rat),(1/8 : Rat),(3/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/2 : Rat) (763227/1048576 : Rat) (99765/1048576 : Rat) (18185/131072 : Rat),.L (293809/524288 : Rat) (30719/32768 : Rat) (111859/1048576 : Rat) (93887/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P20
