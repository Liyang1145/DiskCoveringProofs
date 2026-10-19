import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P216
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(0 : Rat),(1/2 : Rat),(3/4 : Rat),(7/8 : Rat),(3/4 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (7/8 : Rat),.S 0 (1/4 : Rat),.L (0 : Rat) (33015/131072 : Rat) (0 : Rat) (25101/524288 : Rat),.S 1 (13/16 : Rat),.L (194883/1048576 : Rat) (114807/262144 : Rat) (37035/1048576 : Rat) (87355/1048576 : Rat),.L (25355/131072 : Rat) (475175/1048576 : Rat) (9637/262144 : Rat) (22599/262144 : Rat),.S 1 (13/16 : Rat),.L (1/16 : Rat) (539887/1048576 : Rat) (3113/262144 : Rat) (102743/1048576 : Rat),.L (0 : Rat) (16493/32768 : Rat) (0 : Rat) (100431/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P216
