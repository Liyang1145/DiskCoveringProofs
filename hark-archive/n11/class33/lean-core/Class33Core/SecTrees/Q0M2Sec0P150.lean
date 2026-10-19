import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P150
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(27/32 : Rat),(7/8 : Rat),(5/16 : Rat),(11/32 : Rat)⟩
def toks : List Tok := [.S 1 (55/64 : Rat),.S 2 (21/64 : Rat),.S 0 (21/8 : Rat),.L (1135387/1048576 : Rat) (621169/524288 : Rat) (217275/1048576 : Rat) (238085/1048576 : Rat),.L (1150531/1048576 : Rat) (156575/131072 : Rat) (27527/131072 : Rat) (240087/1048576 : Rat),.S 0 (21/8 : Rat),.L (1149563/1048576 : Rat) (1258061/1048576 : Rat) (55007/262144 : Rat) (471/2048 : Rat),.L (1165265/1048576 : Rat) (1268677/1048576 : Rat) (223079/1048576 : Rat) (30403/131072 : Rat),.S 2 (21/64 : Rat),.S 0 (21/8 : Rat),.L (287831/262144 : Rat) (1258787/1048576 : Rat) (110185/524288 : Rat) (120647/524288 : Rat),.L (145817/131072 : Rat) (317275/262144 : Rat) (111663/524288 : Rat) (243307/1048576 : Rat),.S 0 (21/8 : Rat),.L (36421/32768 : Rat) (1274509/1048576 : Rat) (223119/1048576 : Rat) (244363/1048576 : Rat),.L (18457/16384 : Rat) (1285179/1048576 : Rat) (226187/1048576 : Rat) (246447/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P150
