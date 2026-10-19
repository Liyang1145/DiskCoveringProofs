import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P212
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(3/8 : Rat),(7/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (7/16 : Rat) (111397/131072 : Rat) (87263/1048576 : Rat) (170069/1048576 : Rat),.S 0 (3/2 : Rat),.L (179573/262144 : Rat) (1121375/1048576 : Rat) (136863/1048576 : Rat) (53639/262144 : Rat),.S 0 (7/4 : Rat),.L (919659/1048576 : Rat) (606105/524288 : Rat) (87777/524288 : Rat) (116107/524288 : Rat),.L (502087/524288 : Rat) (1307213/1048576 : Rat) (191861/1048576 : Rat) (125377/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P212
