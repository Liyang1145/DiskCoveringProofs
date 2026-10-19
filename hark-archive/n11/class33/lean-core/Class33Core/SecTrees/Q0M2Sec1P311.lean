import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P311
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(0 : Rat),(1/2 : Rat),(7/8 : Rat),(1 : Rat),(3/4 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (7/8 : Rat),.S 1 (15/16 : Rat),.L (0 : Rat) (16043/32768 : Rat) (0 : Rat) (97683/1048576 : Rat),.L (1/16 : Rat) (555529/1048576 : Rat) (3113/262144 : Rat) (52865/524288 : Rat),.S 0 (1/4 : Rat),.L (0 : Rat) (146505/524288 : Rat) (0 : Rat) (55699/1048576 : Rat),.L (227363/1048576 : Rat) (538193/1048576 : Rat) (43211/1048576 : Rat) (25605/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P311
