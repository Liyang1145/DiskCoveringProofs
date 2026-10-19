import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P60
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(1/16 : Rat),(1/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (11/16 : Rat) (919165/1048576 : Rat) (68681/524288 : Rat) (43865/262144 : Rat),.S 0 (3/2 : Rat),.L (752973/1048576 : Rat) (984077/1048576 : Rat) (17939/131072 : Rat) (46995/262144 : Rat),.S 1 (27/32 : Rat),.L (782239/1048576 : Rat) (1020105/1048576 : Rat) (149127/1048576 : Rat) (194941/1048576 : Rat),.L (814717/1048576 : Rat) (1053119/1048576 : Rat) (38841/262144 : Rat) (12583/65536 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P60
