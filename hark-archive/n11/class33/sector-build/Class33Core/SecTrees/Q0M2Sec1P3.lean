import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P3
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(1/4 : Rat),(1/2 : Rat),(1/2 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 1 (3/8 : Rat),.L (32297/65536 : Rat) (1229565/1048576 : Rat) (49163/524288 : Rat) (235595/1048576 : Rat),.S 2 (5/8 : Rat),.L (19131/32768 : Rat) (1201295/1048576 : Rat) (29139/262144 : Rat) (230089/1048576 : Rat),.S 1 (7/16 : Rat),.L (356065/524288 : Rat) (1264013/1048576 : Rat) (135683/1048576 : Rat) (121157/524288 : Rat),.L (750821/1048576 : Rat) (165673/131072 : Rat) (143099/1048576 : Rat) (254309/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P3
