import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P120
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (11/16 : Rat) (249735/262144 : Rat) (68681/524288 : Rat) (190851/1048576 : Rat),.S 0 (3/2 : Rat),.L (103331/131072 : Rat) (1131489/1048576 : Rat) (19707/131072 : Rat) (216519/1048576 : Rat),.S 1 (31/32 : Rat),.L (915899/1048576 : Rat) (1232731/1048576 : Rat) (174829/1048576 : Rat) (59053/262144 : Rat),.L (473769/524288 : Rat) (632803/524288 : Rat) (2827/16384 : Rat) (242625/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P120
