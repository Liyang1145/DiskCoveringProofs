import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P41
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(5/8 : Rat),(11/16 : Rat),(3/8 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/8 : Rat) (693843/1048576 : Rat) (12453/524288 : Rat) (33045/262144 : Rat),.S 0 (3/2 : Rat),.L (485167/1048576 : Rat) (932575/1048576 : Rat) (23075/262144 : Rat) (44511/262144 : Rat),.L (332699/524288 : Rat) (286329/262144 : Rat) (126733/1048576 : Rat) (54801/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P41
