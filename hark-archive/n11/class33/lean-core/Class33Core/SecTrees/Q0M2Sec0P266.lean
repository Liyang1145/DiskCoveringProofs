import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P266
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(11/16 : Rat),(3/4 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (0 : Rat) (793253/1048576 : Rat) (0 : Rat) (75621/524288 : Rat),.S 0 (3/2 : Rat),.L (632493/1048576 : Rat) (140569/131072 : Rat) (60219/524288 : Rat) (53793/262144 : Rat),.S 0 (7/4 : Rat),.L (912121/1048576 : Rat) (311781/262144 : Rat) (174101/1048576 : Rat) (239019/1048576 : Rat),.L (1022197/1048576 : Rat) (686217/524288 : Rat) (195345/1048576 : Rat) (32941/131072 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P266
