import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P166
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(3/8 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (5/16 : Rat) (216641/262144 : Rat) (62295/1048576 : Rat) (41333/262144 : Rat),.S 0 (3/2 : Rat),.L (625335/1048576 : Rat) (1115843/1048576 : Rat) (119069/1048576 : Rat) (106741/524288 : Rat),.S 0 (7/4 : Rat),.L (835053/1048576 : Rat) (606467/524288 : Rat) (159271/1048576 : Rat) (232355/1048576 : Rat),.S 2 (7/16 : Rat),.L (118291/131072 : Rat) (621503/524288 : Rat) (180695/1048576 : Rat) (238215/1048576 : Rat),.L (985789/1048576 : Rat) (644611/524288 : Rat) (94155/524288 : Rat) (247237/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P166
