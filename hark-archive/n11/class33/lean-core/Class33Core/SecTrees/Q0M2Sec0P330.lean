import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P330
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(3/4 : Rat),(13/16 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (0 : Rat) (418847/524288 : Rat) (0 : Rat) (39945/262144 : Rat),.S 0 (3/2 : Rat),.L (660617/1048576 : Rat) (1179001/1048576 : Rat) (62909/524288 : Rat) (225751/1048576 : Rat),.S 0 (7/4 : Rat),.L (119085/131072 : Rat) (652873/524288 : Rat) (5685/32768 : Rat) (250467/1048576 : Rat),.S 2 (11/16 : Rat),.L (1069659/1048576 : Rat) (343883/262144 : Rat) (204529/1048576 : Rat) (33017/131072 : Rat),.L (69985/65536 : Rat) (1427973/1048576 : Rat) (214241/1048576 : Rat) (137219/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P330
