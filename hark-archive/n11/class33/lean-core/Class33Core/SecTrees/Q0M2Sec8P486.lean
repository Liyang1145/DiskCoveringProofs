import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P486
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(11/4 : Rat),(314159265358979323847/100000000000000000000 : Rat),(7/8 : Rat),(15/16 : Rat),(15/16 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (3 : Rat),.S 1 (29/32 : Rat),.L (1764155/1048576 : Rat) (250091/131072 : Rat) (341177/1048576 : Rat) (48625/131072 : Rat),.L (1753/1024 : Rat) (2032937/1048576 : Rat) (347383/1048576 : Rat) (395575/1048576 : Rat),.L (457747/262144 : Rat) (2034785/1048576 : Rat) (22163/65536 : Rat) (395953/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P486
