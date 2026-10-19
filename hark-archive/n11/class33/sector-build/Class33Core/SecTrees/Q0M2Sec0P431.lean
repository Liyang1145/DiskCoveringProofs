import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P431
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(29/32 : Rat),(15/16 : Rat),(21/32 : Rat),(11/16 : Rat)⟩
def toks : List Tok := [.S 1 (59/64 : Rat),.S 2 (43/64 : Rat),.S 1 (117/128 : Rat),.L (1578281/1048576 : Rat) (1665557/1048576 : Rat) (304119/1048576 : Rat) (80367/262144 : Rat),.L (396549/262144 : Rat) (1673817/1048576 : Rat) (38211/131072 : Rat) (323115/1048576 : Rat),.S 1 (117/128 : Rat),.L (797035/524288 : Rat) (420439/262144 : Rat) (307251/1048576 : Rat) (162349/524288 : Rat),.L (800989/524288 : Rat) (52813/32768 : Rat) (77205/262144 : Rat) (326347/1048576 : Rat),.S 2 (43/64 : Rat),.S 1 (119/128 : Rat),.L (797057/524288 : Rat) (420519/262144 : Rat) (307259/1048576 : Rat) (162381/524288 : Rat),.L (1602035/1048576 : Rat) (845167/524288 : Rat) (9651/32768 : Rat) (163205/524288 : Rat),.S 1 (119/128 : Rat),.L (804945/524288 : Rat) (1698275/1048576 : Rat) (38799/131072 : Rat) (327995/1048576 : Rat),.L (1617805/1048576 : Rat) (853267/524288 : Rat) (77991/262144 : Rat) (329645/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P431
