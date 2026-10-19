import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P222
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(7/16 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (3/8 : Rat) (885967/1048576 : Rat) (37387/524288 : Rat) (84533/524288 : Rat),.S 0 (3/2 : Rat),.L (178715/262144 : Rat) (1146477/1048576 : Rat) (68103/524288 : Rat) (219429/1048576 : Rat),.S 0 (7/4 : Rat),.L (59155/65536 : Rat) (623831/524288 : Rat) (45181/262144 : Rat) (239123/1048576 : Rat),.L (1041881/1048576 : Rat) (1352851/1048576 : Rat) (12447/65536 : Rat) (259689/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P222
