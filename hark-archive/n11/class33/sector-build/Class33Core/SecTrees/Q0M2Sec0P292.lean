import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P292
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(11/16 : Rat),(3/4 : Rat),(7/8 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/8 : Rat) (240243/262144 : Rat) (12453/524288 : Rat) (183521/1048576 : Rat),.S 0 (3/2 : Rat),.L (759767/1048576 : Rat) (1330647/1048576 : Rat) (144815/1048576 : Rat) (255339/1048576 : Rat),.S 0 (7/4 : Rat),.L (1087167/1048576 : Rat) (734545/524288 : Rat) (207921/1048576 : Rat) (141267/524288 : Rat),.L (1216561/1048576 : Rat) (402795/262144 : Rat) (58265/262144 : Rat) (310649/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P292
