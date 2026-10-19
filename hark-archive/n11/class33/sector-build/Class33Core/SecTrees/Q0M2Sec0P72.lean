import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P72
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(3/4 : Rat),(13/16 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/2 : Rat) (403275/524288 : Rat) (99765/1048576 : Rat) (38449/262144 : Rat),.S 0 (3/2 : Rat),.L (318513/524288 : Rat) (469031/524288 : Rat) (121305/1048576 : Rat) (89551/524288 : Rat),.L (182041/262144 : Rat) (1068257/1048576 : Rat) (138755/1048576 : Rat) (204259/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P72
