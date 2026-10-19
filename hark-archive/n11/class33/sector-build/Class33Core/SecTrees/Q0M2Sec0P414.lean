import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P414
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(9/4 : Rat),(7/8 : Rat),(15/16 : Rat),(5/8 : Rat),(11/16 : Rat)⟩
def toks : List Tok := [.S 0 (17/8 : Rat),.S 1 (29/32 : Rat),.L (648537/524288 : Rat) (1501179/1048576 : Rat) (248771/1048576 : Rat) (9027/32768 : Rat),.L (1324789/1048576 : Rat) (766265/524288 : Rat) (15887/65536 : Rat) (73765/262144 : Rat),.S 1 (29/32 : Rat),.S 2 (21/32 : Rat),.L (1348899/1048576 : Rat) (379057/262144 : Rat) (258913/1048576 : Rat) (291837/1048576 : Rat),.L (344049/262144 : Rat) (1544677/1048576 : Rat) (264265/1048576 : Rat) (297463/1048576 : Rat),.S 2 (21/32 : Rat),.L (1377947/1048576 : Rat) (386945/262144 : Rat) (264609/1048576 : Rat) (298077/1048576 : Rat),.L (1405039/1048576 : Rat) (788065/524288 : Rat) (33741/131072 : Rat) (303693/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P414
