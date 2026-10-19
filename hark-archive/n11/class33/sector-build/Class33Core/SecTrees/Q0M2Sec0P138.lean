import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P138
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/2 : Rat) (852661/1048576 : Rat) (99765/1048576 : Rat) (81329/524288 : Rat),.S 0 (3/2 : Rat),.L (681169/1048576 : Rat) (1017787/1048576 : Rat) (16219/131072 : Rat) (194493/1048576 : Rat),.L (802315/1048576 : Rat) (1177931/1048576 : Rat) (152981/1048576 : Rat) (112771/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P138
