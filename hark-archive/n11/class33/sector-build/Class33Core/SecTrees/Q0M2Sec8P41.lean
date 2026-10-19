import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P41
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(1/2 : Rat),(1 : Rat),(5/8 : Rat),(3/4 : Rat),(0 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 2 (1/8 : Rat),.S 1 (11/16 : Rat),.L (1/2 : Rat) (97701/131072 : Rat) (99765/1048576 : Rat) (149007/1048576 : Rat),.L (9/16 : Rat) (423671/524288 : Rat) (112281/1048576 : Rat) (161635/1048576 : Rat),.S 1 (11/16 : Rat),.S 0 (3/4 : Rat),.L (26163/65536 : Rat) (671821/1048576 : Rat) (79611/1048576 : Rat) (31991/262144 : Rat),.L (446587/1048576 : Rat) (725649/1048576 : Rat) (5309/65536 : Rat) (69137/524288 : Rat),.S 0 (3/4 : Rat),.L (241417/524288 : Rat) (368223/524288 : Rat) (91855/1048576 : Rat) (17543/131072 : Rat),.L (509663/1048576 : Rat) (790199/1048576 : Rat) (48487/524288 : Rat) (1177/8192 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P41
