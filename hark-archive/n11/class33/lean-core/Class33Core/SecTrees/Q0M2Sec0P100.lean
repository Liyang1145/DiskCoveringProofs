import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P100
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(1/16 : Rat),(1/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (13/16 : Rat) (1049945/1048576 : Rat) (162523/1048576 : Rat) (200713/1048576 : Rat),.S 0 (3/2 : Rat),.L (883403/1048576 : Rat) (557579/524288 : Rat) (168571/1048576 : Rat) (106675/524288 : Rat),.S 1 (31/32 : Rat),.L (912273/1048576 : Rat) (1152079/1048576 : Rat) (174131/1048576 : Rat) (220517/1048576 : Rat),.L (472413/524288 : Rat) (1185041/1048576 : Rat) (180405/1048576 : Rat) (226925/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P100
