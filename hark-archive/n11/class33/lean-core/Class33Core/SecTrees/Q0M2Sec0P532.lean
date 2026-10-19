import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P532
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(3/4 : Rat),(13/16 : Rat),(7/8 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/16 : Rat) (488063/524288 : Rat) (3113/262144 : Rat) (186445/1048576 : Rat),.S 0 (3/2 : Rat),.L (784395/1048576 : Rat) (1367689/1048576 : Rat) (149541/1048576 : Rat) (131299/524288 : Rat),.S 0 (7/4 : Rat),.L (1129129/1048576 : Rat) (189179/131072 : Rat) (54015/262144 : Rat) (72821/262144 : Rat),.S 2 (15/16 : Rat),.L (1264959/1048576 : Rat) (800947/524288 : Rat) (121249/524288 : Rat) (308805/1048576 : Rat),.L (1314151/1048576 : Rat) (1662715/1048576 : Rat) (126055/524288 : Rat) (160451/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P532
