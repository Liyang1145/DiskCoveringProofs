import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P617
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(11/4 : Rat),(314159265358979323847/100000000000000000000 : Rat),(31/32 : Rat),(1 : Rat),(13/16 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 0 (3 : Rat),.S 2 (27/32 : Rat),.L (1732749/1048576 : Rat) (1936365/1048576 : Rat) (167443/524288 : Rat) (187955/524288 : Rat),.L (110215/65536 : Rat) (1968537/1048576 : Rat) (170517/524288 : Rat) (191223/524288 : Rat),.L (1796241/1048576 : Rat) (985767/524288 : Rat) (173809/524288 : Rat) (383055/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P617
