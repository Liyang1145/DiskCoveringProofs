import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P113
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(5/8 : Rat),(3/4 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 1 (11/16 : Rat),.S 2 (11/16 : Rat),.L (541829/524288 : Rat) (1443281/1048576 : Rat) (207241/1048576 : Rat) (138725/524288 : Rat),.L (568275/524288 : Rat) (1511597/1048576 : Rat) (54375/262144 : Rat) (145461/524288 : Rat),.S 2 (11/16 : Rat),.L (568275/524288 : Rat) (1511597/1048576 : Rat) (54375/262144 : Rat) (145461/524288 : Rat),.L (149003/131072 : Rat) (1574229/1048576 : Rat) (228283/1048576 : Rat) (75829/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P113
