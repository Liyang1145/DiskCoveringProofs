import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P180
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(2 : Rat),(9/4 : Rat),(7/8 : Rat),(15/16 : Rat),(1/2 : Rat),(9/16 : Rat)⟩
def toks : List Tok := [.S 1 (29/32 : Rat),.S 0 (17/8 : Rat),.S 2 (17/32 : Rat),.L (9391/8192 : Rat) (681107/524288 : Rat) (115117/524288 : Rat) (65381/262144 : Rat),.L (1226605/1048576 : Rat) (1388259/1048576 : Rat) (235017/1048576 : Rat) (133317/524288 : Rat),.S 2 (17/32 : Rat),.L (621179/524288 : Rat) (702159/524288 : Rat) (29761/131072 : Rat) (67447/262144 : Rat),.L (1268563/1048576 : Rat) (1431991/1048576 : Rat) (243201/1048576 : Rat) (68807/262144 : Rat),.S 0 (17/8 : Rat),.S 2 (17/32 : Rat),.L (1231495/1048576 : Rat) (1393681/1048576 : Rat) (117985/524288 : Rat) (133849/524288 : Rat),.S 1 (59/64 : Rat),.L (1255789/1048576 : Rat) (350979/262144 : Rat) (60177/262144 : Rat) (269709/1048576 : Rat),.L (1270447/1048576 : Rat) (1419589/1048576 : Rat) (243569/1048576 : Rat) (272789/1048576 : Rat),.S 2 (17/32 : Rat),.L (1272255/1048576 : Rat) (1436261/1048576 : Rat) (121961/524288 : Rat) (69017/262144 : Rat),.L (324561/262144 : Rat) (1463837/1048576 : Rat) (248999/1048576 : Rat) (281499/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P180
