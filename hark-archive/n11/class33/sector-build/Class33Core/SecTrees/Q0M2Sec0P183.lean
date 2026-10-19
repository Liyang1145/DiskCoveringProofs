import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P183
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (9/16 : Rat) (915685/1048576 : Rat) (112281/1048576 : Rat) (174789/1048576 : Rat),.S 0 (3/2 : Rat),.L (371333/524288 : Rat) (1081387/1048576 : Rat) (141535/1048576 : Rat) (103401/524288 : Rat),.S 0 (7/4 : Rat),.L (878315/1048576 : Rat) (1149263/1048576 : Rat) (20949/131072 : Rat) (109985/524288 : Rat),.L (937995/1048576 : Rat) (1221381/1048576 : Rat) (11193/65536 : Rat) (14625/65536 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P183
