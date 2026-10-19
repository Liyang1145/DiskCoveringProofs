import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P73
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(3/4 : Rat),(25/32 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.L (825673/1048576 : Rat) (533925/524288 : Rat) (157469/1048576 : Rat) (51045/262144 : Rat),.S 2 (7/32 : Rat),.L (879205/1048576 : Rat) (530139/524288 : Rat) (167763/1048576 : Rat) (101357/524288 : Rat),.S 0 (19/8 : Rat),.L (457931/524288 : Rat) (1057125/1048576 : Rat) (87411/524288 : Rat) (202103/1048576 : Rat),.L (58263/65536 : Rat) (33599/32768 : Rat) (44493/262144 : Rat) (205597/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P73
