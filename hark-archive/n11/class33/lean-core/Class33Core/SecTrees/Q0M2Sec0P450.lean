import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P450
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (3/16 : Rat) (985247/1048576 : Rat) (37363/1048576 : Rat) (94103/524288 : Rat),.S 0 (3/2 : Rat),.L (764313/1048576 : Rat) (1348283/1048576 : Rat) (145687/1048576 : Rat) (129397/524288 : Rat),.S 0 (7/4 : Rat),.L (541561/524288 : Rat) (1485083/1048576 : Rat) (207137/1048576 : Rat) (35711/131072 : Rat),.S 2 (11/16 : Rat),.L (1222115/1048576 : Rat) (1560695/1048576 : Rat) (117071/524288 : Rat) (150317/524288 : Rat),.L (633637/524288 : Rat) (402795/262144 : Rat) (242949/1048576 : Rat) (310649/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P450
