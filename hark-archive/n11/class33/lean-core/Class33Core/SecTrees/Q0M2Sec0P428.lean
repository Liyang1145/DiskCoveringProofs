import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P428
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(29/32 : Rat),(15/16 : Rat),(5/8 : Rat),(21/32 : Rat)⟩
def toks : List Tok := [.S 1 (59/64 : Rat),.S 2 (41/64 : Rat),.S 1 (117/128 : Rat),.L (773371/524288 : Rat) (816585/524288 : Rat) (297871/1048576 : Rat) (78755/262144 : Rat),.L (1554669/1048576 : Rat) (1641429/1048576 : Rat) (18715/65536 : Rat) (316663/1048576 : Rat),.S 1 (117/128 : Rat),.L (1562505/1048576 : Rat) (824681/524288 : Rat) (4703/16384 : Rat) (159121/524288 : Rat),.L (785213/524288 : Rat) (1657621/1048576 : Rat) (302561/1048576 : Rat) (319887/1048576 : Rat),.S 2 (41/64 : Rat),.S 1 (119/128 : Rat),.L (1562599/1048576 : Rat) (1649687/1048576 : Rat) (301011/1048576 : Rat) (318307/1048576 : Rat),.L (392633/262144 : Rat) (1657945/1048576 : Rat) (151291/524288 : Rat) (19997/65536 : Rat),.S 1 (119/128 : Rat),.L (789175/524288 : Rat) (208235/131072 : Rat) (76033/262144 : Rat) (321533/1048576 : Rat),.L (1586277/1048576 : Rat) (1674137/1048576 : Rat) (38213/131072 : Rat) (323179/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P428
