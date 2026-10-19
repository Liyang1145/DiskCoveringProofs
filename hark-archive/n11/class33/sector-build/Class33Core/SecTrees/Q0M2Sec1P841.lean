import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P841
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(11/4 : Rat),(314159265358979323847/100000000000000000000 : Rat),(31/32 : Rat),(1 : Rat),(7/8 : Rat),(15/16 : Rat)⟩
def toks : List Tok := [.S 0 (3 : Rat),.S 2 (29/32 : Rat),.L (448551/262144 : Rat) (250091/131072 : Rat) (43401/131072 : Rat) (48625/131072 : Rat),.S 1 (63/64 : Rat),.L (912519/524288 : Rat) (1008149/524288 : Rat) (176705/524288 : Rat) (24511/65536 : Rat),.L (920029/524288 : Rat) (2032937/1048576 : Rat) (356435/1048576 : Rat) (395575/1048576 : Rat),.L (930771/524288 : Rat) (2034785/1048576 : Rat) (5637/16384 : Rat) (395953/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P841
