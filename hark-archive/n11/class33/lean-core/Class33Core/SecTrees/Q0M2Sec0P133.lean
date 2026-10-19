import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P133
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(3/4 : Rat),(13/16 : Rat),(5/16 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 1 (25/32 : Rat),.L (912533/1048576 : Rat) (1170733/1048576 : Rat) (174181/1048576 : Rat) (224143/1048576 : Rat),.L (942239/1048576 : Rat) (601885/524288 : Rat) (89953/524288 : Rat) (115285/524288 : Rat),.S 1 (25/32 : Rat),.S 0 (19/8 : Rat),.L (979911/1048576 : Rat) (590767/524288 : Rat) (187175/1048576 : Rat) (226243/1048576 : Rat),.S 2 (11/32 : Rat),.L (126875/131072 : Rat) (1163065/1048576 : Rat) (96977/524288 : Rat) (55663/262144 : Rat),.L (260799/262144 : Rat) (1192725/1048576 : Rat) (99703/524288 : Rat) (228421/1048576 : Rat),.S 0 (19/8 : Rat),.S 2 (11/32 : Rat),.L (1024513/1048576 : Rat) (586395/524288 : Rat) (195793/1048576 : Rat) (224543/1048576 : Rat),.L (525489/524288 : Rat) (300229/262144 : Rat) (12557/65536 : Rat) (230015/1048576 : Rat),.S 2 (11/32 : Rat),.L (523111/524288 : Rat) (1196015/1048576 : Rat) (24999/131072 : Rat) (229061/1048576 : Rat),.L (1074245/1048576 : Rat) (612825/524288 : Rat) (205417/1048576 : Rat) (14677/65536 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P133
