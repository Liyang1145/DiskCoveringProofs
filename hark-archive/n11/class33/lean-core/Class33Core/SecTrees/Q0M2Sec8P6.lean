import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P6
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(1/2 : Rat),(1 : Rat),(0 : Rat),(1/4 : Rat),(1/2 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 2 (5/8 : Rat),.S 1 (1/8 : Rat),.L (3/8 : Rat) (357919/524288 : Rat) (37387/524288 : Rat) (68197/524288 : Rat),.S 0 (3/4 : Rat),.L (72977/262144 : Rat) (607391/1048576 : Rat) (867/16384 : Rat) (115639/1048576 : Rat),.L (323383/1048576 : Rat) (661293/1048576 : Rat) (61477/1048576 : Rat) (125949/1048576 : Rat),.S 1 (1/8 : Rat),.S 2 (11/16 : Rat),.L (1/2 : Rat) (97701/131072 : Rat) (99765/1048576 : Rat) (149007/1048576 : Rat),.L (9/16 : Rat) (423671/524288 : Rat) (112281/1048576 : Rat) (161635/1048576 : Rat),.S 0 (3/4 : Rat),.S 2 (11/16 : Rat),.L (26163/65536 : Rat) (671821/1048576 : Rat) (79611/1048576 : Rat) (31991/262144 : Rat),.L (241417/524288 : Rat) (368223/524288 : Rat) (91855/1048576 : Rat) (17543/131072 : Rat),.S 1 (3/16 : Rat),.L (505247/1048576 : Rat) (758739/1048576 : Rat) (96131/1048576 : Rat) (144619/1048576 : Rat),.L (235505/524288 : Rat) (184189/262144 : Rat) (175/2048 : Rat) (140403/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P6
