import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P686
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(7/8 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (0 : Rat) (509239/524288 : Rat) (0 : Rat) (194627/1048576 : Rat),.S 0 (3/2 : Rat),.L (422141/524288 : Rat) (45245/32768 : Rat) (161045/1048576 : Rat) (69587/262144 : Rat),.S 0 (7/4 : Rat),.L (1217543/1048576 : Rat) (803235/524288 : Rat) (58313/262144 : Rat) (309713/1048576 : Rat),.S 2 (15/16 : Rat),.L (1364477/1048576 : Rat) (854479/524288 : Rat) (261967/1048576 : Rat) (330129/1048576 : Rat),.L (88273/65536 : Rat) (1768569/1048576 : Rat) (271369/1048576 : Rat) (342063/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P686
