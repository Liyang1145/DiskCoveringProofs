import Class33Core.SecTrees.Q0M2Sec6Base
namespace Class33Core.SecTrees.Q0M2Sec6.P1
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec6
def box : Box := ⟨(0 : Rat),(1 : Rat),(0 : Rat),(1/4 : Rat),(1/2 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 0 (1/2 : Rat),.S 2 (5/8 : Rat),.S 1 (1/8 : Rat),.L (3/8 : Rat) (671503/1048576 : Rat) (37387/524288 : Rat) (127903/1048576 : Rat),.L (1/4 : Rat) (563663/1048576 : Rat) (24913/524288 : Rat) (26821/262144 : Rat),.S 1 (1/8 : Rat),.S 2 (11/16 : Rat),.L (1/2 : Rat) (737057/1048576 : Rat) (99765/1048576 : Rat) (140461/1048576 : Rat),.S 0 (1/4 : Rat),.L (9/16 : Rat) (790515/1048576 : Rat) (112281/1048576 : Rat) (150717/1048576 : Rat),.L (9/16 : Rat) (802509/1048576 : Rat) (112281/1048576 : Rat) (38255/262144 : Rat),.L (3/8 : Rat) (21671/32768 : Rat) (37387/524288 : Rat) (132109/1048576 : Rat),.S 2 (5/8 : Rat),.L (1/4 : Rat) (385795/524288 : Rat) (24913/524288 : Rat) (36771/262144 : Rat),.S 1 (1/8 : Rat),.L (1/2 : Rat) (423671/524288 : Rat) (99765/1048576 : Rat) (161635/1048576 : Rat),.L (104469/262144 : Rat) (396397/524288 : Rat) (4967/65536 : Rat) (75577/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec6.P1
