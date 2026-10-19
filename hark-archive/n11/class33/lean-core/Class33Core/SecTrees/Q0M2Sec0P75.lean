import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P75
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(25/32 : Rat),(13/16 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.L (856809/1048576 : Rat) (1101039/1048576 : Rat) (81727/524288 : Rat) (210611/1048576 : Rat),.S 2 (7/32 : Rat),.S 0 (19/8 : Rat),.L (115339/131072 : Rat) (1062945/1048576 : Rat) (88071/524288 : Rat) (101615/524288 : Rat),.L (937213/1048576 : Rat) (134911/131072 : Rat) (178937/1048576 : Rat) (206395/1048576 : Rat),.S 0 (19/8 : Rat),.L (29609/32768 : Rat) (544983/524288 : Rat) (180919/1048576 : Rat) (208465/1048576 : Rat),.L (963951/1048576 : Rat) (1108169/1048576 : Rat) (92047/524288 : Rat) (105997/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P75
