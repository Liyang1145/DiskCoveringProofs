import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P114
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(29/32 : Rat),(15/16 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 2 (7/32 : Rat),.S 0 (9/4 : Rat),.L (125705/131072 : Rat) (1186925/1048576 : Rat) (192145/1048576 : Rat) (56823/262144 : Rat),.S 0 (19/8 : Rat),.L (525299/524288 : Rat) (597197/524288 : Rat) (200839/1048576 : Rat) (228745/1048576 : Rat),.L (133173/131072 : Rat) (1211187/1048576 : Rat) (203701/1048576 : Rat) (232015/1048576 : Rat),.S 0 (9/4 : Rat),.L (255817/262144 : Rat) (606471/524288 : Rat) (6111/32768 : Rat) (58089/262144 : Rat),.S 0 (19/8 : Rat),.L (268669/262144 : Rat) (305323/262144 : Rat) (205501/1048576 : Rat) (233983/1048576 : Rat),.L (1091527/1048576 : Rat) (1240049/1048576 : Rat) (104383/524288 : Rat) (237639/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P114
