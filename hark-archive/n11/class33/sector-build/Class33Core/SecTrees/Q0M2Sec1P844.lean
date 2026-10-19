import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P844
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(11/4 : Rat),(314159265358979323847/100000000000000000000 : Rat),(15/16 : Rat),(31/32 : Rat),(15/16 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (3 : Rat),.S 2 (31/32 : Rat),.L (1825759/1048576 : Rat) (2031881/1048576 : Rat) (353555/1048576 : Rat) (395359/1048576 : Rat),.S 1 (61/64 : Rat),.L (1856011/1048576 : Rat) (2048459/1048576 : Rat) (89913/262144 : Rat) (398749/1048576 : Rat),.L (1871341/1048576 : Rat) (1032355/524288 : Rat) (181373/524288 : Rat) (100519/262144 : Rat),.L (473813/262144 : Rat) (2065165/1048576 : Rat) (91895/262144 : Rat) (201085/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P844
