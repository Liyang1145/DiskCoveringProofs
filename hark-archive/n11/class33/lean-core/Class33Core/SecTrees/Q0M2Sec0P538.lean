import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P538
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(3/4 : Rat),(25/32 : Rat),(7/8 : Rat),(15/16 : Rat)⟩
def toks : List Tok := [.S 2 (29/32 : Rat),.S 1 (49/64 : Rat),.L (51303/32768 : Rat) (1754543/1048576 : Rat) (79179/262144 : Rat) (339251/1048576 : Rat),.S 2 (57/64 : Rat),.L (828787/524288 : Rat) (1754237/1048576 : Rat) (319877/1048576 : Rat) (169595/524288 : Rat),.L (418325/262144 : Rat) (885381/524288 : Rat) (323011/1048576 : Rat) (342503/1048576 : Rat),.S 1 (49/64 : Rat),.L (1673183/1048576 : Rat) (27931/16384 : Rat) (80747/262144 : Rat) (43235/131072 : Rat),.S 2 (59/64 : Rat),.L (844519/524288 : Rat) (446821/262144 : Rat) (163075/524288 : Rat) (345819/1048576 : Rat),.L (426197/262144 : Rat) (450951/262144 : Rat) (329295/1048576 : Rat) (349139/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P538
