import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P308
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(2 : Rat),(17/8 : Rat),(3/4 : Rat),(13/16 : Rat),(3/4 : Rat),(13/16 : Rat)⟩
def toks : List Tok := [.S 1 (25/32 : Rat),.S 2 (25/32 : Rat),.S 0 (33/16 : Rat),.L (1312059/1048576 : Rat) (354577/262144 : Rat) (251701/1048576 : Rat) (272537/1048576 : Rat),.L (668655/524288 : Rat) (361151/262144 : Rat) (256643/1048576 : Rat) (138855/524288 : Rat),.S 0 (33/16 : Rat),.L (1339115/1048576 : Rat) (723747/524288 : Rat) (256997/1048576 : Rat) (278279/1048576 : Rat),.L (682443/524288 : Rat) (1474291/1048576 : Rat) (262047/1048576 : Rat) (283559/1048576 : Rat),.S 2 (25/32 : Rat),.S 0 (33/16 : Rat),.L (1339115/1048576 : Rat) (723747/524288 : Rat) (256997/1048576 : Rat) (278279/1048576 : Rat),.L (682443/524288 : Rat) (1474291/1048576 : Rat) (262047/1048576 : Rat) (283559/1048576 : Rat),.S 0 (33/16 : Rat),.S 1 (51/64 : Rat),.L (170841/131072 : Rat) (730383/524288 : Rat) (32801/131072 : Rat) (280893/1048576 : Rat),.L (172541/131072 : Rat) (1475011/1048576 : Rat) (66269/262144 : Rat) (283701/1048576 : Rat),.L (1393031/1048576 : Rat) (1502359/1048576 : Rat) (133785/524288 : Rat) (289097/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P308
