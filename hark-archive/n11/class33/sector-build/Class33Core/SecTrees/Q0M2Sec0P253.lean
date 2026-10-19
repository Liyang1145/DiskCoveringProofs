import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P253
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(11/16 : Rat),(3/4 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/16 : Rat) (760775/1048576 : Rat) (3113/262144 : Rat) (72505/524288 : Rat),.S 0 (3/2 : Rat),.L (284751/524288 : Rat) (1052735/1048576 : Rat) (54199/524288 : Rat) (201253/1048576 : Rat),.S 0 (7/4 : Rat),.L (409227/524288 : Rat) (1162111/1048576 : Rat) (156081/1048576 : Rat) (222467/1048576 : Rat),.L (458313/524288 : Rat) (637191/524288 : Rat) (174969/1048576 : Rat) (122169/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P253
