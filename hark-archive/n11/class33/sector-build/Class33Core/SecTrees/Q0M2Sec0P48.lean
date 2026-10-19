import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P48
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(11/16 : Rat),(3/4 : Rat),(7/16 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 1 (23/32 : Rat),.L (119169/131072 : Rat) (606611/524288 : Rat) (91025/524288 : Rat) (232411/1048576 : Rat),.L (981017/1048576 : Rat) (1246003/1048576 : Rat) (187389/1048576 : Rat) (14925/65536 : Rat),.S 1 (23/32 : Rat),.S 0 (19/8 : Rat),.L (129453/131072 : Rat) (1225999/1048576 : Rat) (98971/524288 : Rat) (58725/262144 : Rat),.S 2 (15/32 : Rat),.L (534289/524288 : Rat) (152117/131072 : Rat) (6385/32768 : Rat) (116567/524288 : Rat),.L (549023/524288 : Rat) (1247241/1048576 : Rat) (105015/524288 : Rat) (239041/1048576 : Rat),.S 0 (19/8 : Rat),.L (532323/524288 : Rat) (629493/524288 : Rat) (101779/524288 : Rat) (241333/1048576 : Rat),.S 2 (15/32 : Rat),.L (274713/262144 : Rat) (78111/65536 : Rat) (105093/524288 : Rat) (14971/65536 : Rat),.L (1128145/1048576 : Rat) (1280043/1048576 : Rat) (215869/1048576 : Rat) (61361/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P48
