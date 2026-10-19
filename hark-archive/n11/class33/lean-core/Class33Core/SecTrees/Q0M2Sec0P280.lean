import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P280
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(11/16 : Rat),(3/4 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (0 : Rat) (216901/262144 : Rat) (0 : Rat) (41383/262144 : Rat),.S 0 (3/2 : Rat),.L (692861/1048576 : Rat) (305573/262144 : Rat) (131991/1048576 : Rat) (117089/524288 : Rat),.S 0 (7/4 : Rat),.L (999179/1048576 : Rat) (1353939/1048576 : Rat) (11931/65536 : Rat) (129951/524288 : Rat),.L (69985/65536 : Rat) (744331/524288 : Rat) (214241/1048576 : Rat) (143197/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P280
