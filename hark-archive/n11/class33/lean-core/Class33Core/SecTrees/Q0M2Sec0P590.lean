import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P590
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (0 : Rat) (965017/1048576 : Rat) (0 : Rat) (184301/1048576 : Rat),.S 0 (3/2 : Rat),.L (781653/1048576 : Rat) (1363023/1048576 : Rat) (149015/1048576 : Rat) (261683/1048576 : Rat),.S 0 (7/4 : Rat),.L (563613/524288 : Rat) (755277/524288 : Rat) (107845/524288 : Rat) (72679/262144 : Rat),.S 2 (13/16 : Rat),.L (1264959/1048576 : Rat) (800947/524288 : Rat) (121249/524288 : Rat) (308805/1048576 : Rat),.L (1314843/1048576 : Rat) (827497/524288 : Rat) (126123/524288 : Rat) (79841/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P590
