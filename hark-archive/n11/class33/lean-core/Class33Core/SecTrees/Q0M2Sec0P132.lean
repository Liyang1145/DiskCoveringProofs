import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P132
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(3/4 : Rat),(13/16 : Rat),(5/16 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (3/8 : Rat) (778727/1048576 : Rat) (37387/524288 : Rat) (74227/524288 : Rat),.S 0 (3/2 : Rat),.L (610595/1048576 : Rat) (974973/1048576 : Rat) (116251/1048576 : Rat) (186223/1048576 : Rat),.L (95213/131072 : Rat) (1158617/1048576 : Rat) (145187/1048576 : Rat) (55447/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P132
