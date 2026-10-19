import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P95
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(1/16 : Rat),(1/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (3/4 : Rat) (984545/1048576 : Rat) (37483/262144 : Rat) (188071/1048576 : Rat),.S 0 (3/2 : Rat),.L (409081/524288 : Rat) (524809/524288 : Rat) (156025/1048576 : Rat) (100325/524288 : Rat),.S 1 (29/32 : Rat),.L (52951/65536 : Rat) (1086119/1048576 : Rat) (80805/524288 : Rat) (207719/1048576 : Rat),.L (109967/131072 : Rat) (1119105/1048576 : Rat) (167865/1048576 : Rat) (214115/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P95
