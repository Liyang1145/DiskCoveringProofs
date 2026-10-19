import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P28
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(314159265358979323847/100000000000000000000 : Rat),(1/2 : Rat),(9/16 : Rat),(3/8 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 0 (2 : Rat),.L (0 : Rat) (1106901/1048576 : Rat) (0 : Rat) (52937/262144 : Rat),.S 2 (7/16 : Rat),.S 0 (5/2 : Rat),.L (708867/1048576 : Rat) (1058767/1048576 : Rat) (135057/1048576 : Rat) (202421/1048576 : Rat),.S 1 (17/32 : Rat),.L (753635/1048576 : Rat) (512115/524288 : Rat) (143639/1048576 : Rat) (195739/1048576 : Rat),.S 0 (11/4 : Rat),.L (53261/65536 : Rat) (1058767/1048576 : Rat) (162563/1048576 : Rat) (202421/1048576 : Rat),.L (845655/1048576 : Rat) (1058767/1048576 : Rat) (161309/1048576 : Rat) (202421/1048576 : Rat),.S 0 (5/2 : Rat),.L (762385/1048576 : Rat) (139985/131072 : Rat) (145317/1048576 : Rat) (107133/524288 : Rat),.S 1 (17/32 : Rat),.L (810935/1048576 : Rat) (1085309/1048576 : Rat) (154637/1048576 : Rat) (103781/524288 : Rat),.S 0 (11/4 : Rat),.L (914897/1048576 : Rat) (139985/131072 : Rat) (43659/262144 : Rat) (107133/524288 : Rat),.L (907811/1048576 : Rat) (139985/131072 : Rat) (173271/1048576 : Rat) (107133/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P28
